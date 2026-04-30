"""EMLProofEnv — Gymnasium-compatible RL environment for EML proofs.

The agent picks one tactic per step from :data:`TACTIC_VOCABULARY`;
the env applies it to the current Lean source, calls the kernel
through :class:`petal.lean_worker.LeanWorker` (or an HTTP endpoint),
and returns the structured reward signal.

Termination: the proof is closed (sorry-free, no errors, no
unsolved goals) OR the step budget is exhausted.

Concurrency: one env per worker. Construct multiple env instances
with separate workers to parallelise training.
"""
from __future__ import annotations

import os
import random
from typing import Any, Optional, Sequence

import gymnasium as gym
import numpy as np
from gymnasium import spaces

from .observation import ObservationEncoder
from .rewards import RewardConfig, RewardSignal, compute_reward
from .tactics import TACTIC_VOCABULARY


__all__ = ["EMLProofEnv"]


_SCRATCH_PROBLEM_TEMPLATE = (
    "theorem _scratch_problem : True := by\n  sorry\n"
)


class EMLProofEnv(gym.Env):
    """Gymnasium environment for stepwise EML theorem proving.

    Two backends:

      * **Local worker** (default): pass a
        :class:`petal.lean_worker.LeanWorker` instance. Each step
        runs a real ``lake build`` against ``monogate-lean``.
      * **HTTP API**: pass ``api_url="https://api.monogate.dev"``
        and the env will POST to ``/api/lean/verify``. Slower but
        works without a local Lean install. (Dependencies kept
        soft — ``urllib`` only.)

    A "problem" is one of:

      * a PETAL ``theorem_id`` (env loads the canonical problem
        statement and starts from a ``sorry``-stub proof), or
      * a literal ``starter_source`` (free-form, when you want to
        train on goals that aren't in PETAL).
    """

    metadata = {"render_modes": ["human", "ansi"], "render_fps": 4}

    def __init__(
        self,
        *,
        theorem_id: Optional[str] = None,
        starter_source: Optional[str] = None,
        worker: Optional[Any] = None,
        api_url: Optional[str] = None,
        max_steps: int = 50,
        render_mode: Optional[str] = None,
        reward_config: Optional[RewardConfig] = None,
        petal_records: Optional[Sequence[dict]] = None,
        imports: Optional[Sequence[str]] = None,
        seed: Optional[int] = None,
    ) -> None:
        super().__init__()
        if theorem_id is None and starter_source is None:
            raise ValueError(
                "Provide either theorem_id (for a PETAL problem) or "
                "starter_source (free-form goal)."
            )
        if worker is None and api_url is None:
            raise ValueError(
                "Provide either worker (LeanWorker instance) or "
                "api_url (HTTP endpoint)."
            )

        self.theorem_id = theorem_id
        self.starter_source = starter_source
        self.worker = worker
        self.api_url = api_url.rstrip("/") if api_url else None
        self.max_steps = max_steps
        self.render_mode = render_mode
        self.reward_config = reward_config or RewardConfig()
        self.petal_records = list(petal_records) if petal_records else []
        self.imports = tuple(imports) if imports is not None else None

        self.encoder = ObservationEncoder()
        self.action_space = spaces.Discrete(len(TACTIC_VOCABULARY))
        self.observation_space = spaces.Box(
            low=-1.0,
            high=5.0,
            shape=(self.encoder.total_dim,),
            dtype=np.float32,
        )

        # Per-episode state.
        self._current_source: str = ""
        self._tactic_history: list[int] = []
        self._step_count: int = 0
        self._prev_goals: int = -1
        self._petal_record: Optional[dict] = None
        self._petal_dead_ends: list[str] = []
        self._rng = random.Random(seed)

    # ── Episode lifecycle ─────────────────────────────────────────

    def reset(
        self,
        *,
        seed: Optional[int] = None,
        options: Optional[dict] = None,
    ) -> tuple[np.ndarray, dict]:
        super().reset(seed=seed)
        if seed is not None:
            self._rng.seed(seed)

        self._current_source = self._initial_source()
        self._tactic_history = []
        self._step_count = 0
        self._prev_goals = -1
        self._petal_record = self._lookup_record()
        self._petal_dead_ends = self._extract_dead_ends(self._petal_record)

        info: dict[str, Any] = {
            "theorem_id": self.theorem_id,
            "petal_dead_ends": list(self._petal_dead_ends),
            "starter_source": self._current_source,
        }
        return self._observation(
            goal_text=self._current_source,
            goals_remaining=1,
            sorry_count=1,
            status="success",
        ), info

    def step(
        self,
        action: int,
    ) -> tuple[np.ndarray, float, bool, bool, dict]:
        if not self.action_space.contains(int(action)):
            raise ValueError(f"action {action} not in action_space")

        self._step_count += 1
        tactic = TACTIC_VOCABULARY[int(action)]
        self._tactic_history.append(int(action))

        new_source = self._apply_tactic(self._current_source, tactic)
        result = self._verify(new_source)

        signal = compute_reward(
            status=result["status"],
            sorry_count=result["sorry_count"],
            goals_remaining=result["goals_remaining"],
            prev_goals_remaining=self._prev_goals,
            is_one_node_win=False,  # Tool 4 / SuperBEST hookup is a follow-up.
            tactic=tactic,
            petal_dead_ends=self._petal_dead_ends,
            config=self.reward_config,
        )

        # Only commit the new source when the build was a success;
        # if the tactic produced an error, keep the previous source
        # so the agent can try a different approach next step.
        if result["status"] == "success":
            self._current_source = new_source
            self._prev_goals = result["goals_remaining"]

        proof_closed = (
            result["status"] == "success"
            and result["sorry_count"] == 0
            and result["goals_remaining"] == 0
        )
        terminated = bool(proof_closed)
        truncated = self._step_count >= self.max_steps and not terminated

        obs = self._observation(
            goal_text=self._current_source,
            goals_remaining=result["goals_remaining"],
            sorry_count=result["sorry_count"],
            status=result["status"],
        )
        info = {
            "tactic": tactic,
            "tactic_index": int(action),
            "result_status": result["status"],
            "goals_remaining": result["goals_remaining"],
            "sorry_count": result["sorry_count"],
            "errors": result.get("error_messages", []),
            "reward_signal": _signal_to_dict(signal),
            "proof_text": self._current_source,
            "step": self._step_count,
        }
        return obs, signal.total, terminated, truncated, info

    # ── Rendering ──────────────────────────────────────────────────

    def render(self) -> Optional[str]:
        text = (
            f"--- step {self._step_count} ---\n"
            f"history (last 6): {self._tactic_history[-6:]}\n"
            f"source:\n{self._current_source}"
        )
        if self.render_mode == "human":
            print(text)
            return None
        if self.render_mode == "ansi":
            return text
        return None

    def close(self) -> None:
        # No persistent resources beyond the worker (which the
        # caller owns); nothing to release here.
        pass

    # ── Internals ──────────────────────────────────────────────────

    def _initial_source(self) -> str:
        if self.starter_source is not None:
            return self.starter_source
        rec = self._lookup_record()
        if rec is None:
            return _SCRATCH_PROBLEM_TEMPLATE
        # Use the canonical statement with a sorry-stubbed proof so
        # the agent must close it themselves.
        statement = (rec.get("statement") or {}).get("lean4", "").strip()
        if not statement:
            return _SCRATCH_PROBLEM_TEMPLATE
        # Strip any inline `:= ...` proof if the lean4 field includes it.
        if ":=" in statement:
            statement = statement.split(":=", 1)[0].rstrip()
        return f"{statement} := by\n  sorry\n"

    def _lookup_record(self) -> Optional[dict]:
        if self.theorem_id is None:
            return None
        for rec in self.petal_records:
            if rec.get("theorem_id") == self.theorem_id:
                return rec
        return None

    @staticmethod
    def _extract_dead_ends(rec: Optional[dict]) -> list[str]:
        if rec is None:
            return []
        out: list[str] = []
        proof = rec.get("proof") or {}
        for step in proof.get("lean4_step_by_step") or []:
            for mistake in step.get("common_mistakes", []) or []:
                if not isinstance(mistake, str):
                    continue
                # Pull tactic-shaped tokens — the dead-end string
                # often mentions the tactic name in the prose.
                # Conservative: take tactic identifiers we recognise.
                from .tactics import COMMON_TACTICS
                for tac in COMMON_TACTICS:
                    if tac.lower() in mistake.lower():
                        out.append(tac)
        return list(dict.fromkeys(out))   # dedupe, preserve order

    # Tactics that, by their semantics, close the goal in one shot.
    # When the agent picks one of these, we replace the trailing
    # ``sorry`` directly instead of inserting before it.
    _CLOSING_TACTICS = frozenset({
        "rfl", "trivial", "decide", "ring", "norm_num", "linarith",
        "nlinarith", "omega", "assumption", "exact?", "apply?",
        "eml_auto",
    })

    def _is_closing_tactic(self, tactic: str) -> bool:
        head = tactic.strip().split(maxsplit=1)[0] if tactic.strip() else ""
        return head in self._CLOSING_TACTICS or tactic.startswith("exact ")

    def _apply_tactic(self, source: str, tactic: str) -> str:
        """Apply the tactic to the proof.

        Two placements:
          * **Closing tactic** → replace the trailing ``sorry`` with
            the tactic. The agent finishes the proof in one step.
          * **Progressing tactic** → insert the tactic before the
            trailing ``sorry``, keeping the placeholder so the
            agent can continue stepping.

        ``sorry``-free sources are returned unchanged.
        """
        if "sorry" not in source:
            return source
        idx = source.rfind("sorry")
        line_start = source.rfind("\n", 0, idx) + 1
        indent = source[line_start:idx]
        indent_str = indent if indent.strip() == "" else "  "

        prefix = source[:idx].rstrip()
        suffix = source[idx + len("sorry"):]

        if self._is_closing_tactic(tactic):
            return f"{prefix}\n{indent_str}{tactic}{suffix}"
        return f"{prefix}\n{indent_str}{tactic}\n{indent_str}sorry{suffix}"

    def _verify(self, source: str) -> dict:
        """Run the verification — local worker first, then HTTP."""
        if self.worker is not None:
            r = self.worker.verify(source, imports=self.imports)
            return {
                "status": r.status,
                "goals_remaining": r.goals_remaining,
                "sorry_count": r.sorry_count,
                "error_messages": list(r.error_messages),
                "goal_state": r.goal_state,
            }
        # HTTP path.
        return self._verify_http(source)

    def _verify_http(self, source: str) -> dict:
        import json as _json
        import urllib.request as _ur
        import urllib.error as _ue

        payload = {
            "lean_source": source,
            "imports": list(self.imports) if self.imports else None,
            "enrich": False,
        }
        url = f"{self.api_url}/api/lean/verify"
        body = _json.dumps(payload).encode("utf-8")
        req = _ur.Request(
            url,
            data=body,
            headers={"Content-Type": "application/json"},
            method="POST",
        )
        try:
            with _ur.urlopen(req, timeout=120) as resp:
                data = _json.loads(resp.read().decode("utf-8"))
        except (_ue.URLError, _ue.HTTPError, TimeoutError, OSError) as exc:
            return {
                "status": "unavailable",
                "goals_remaining": -1,
                "sorry_count": -1,
                "error_messages": [f"http: {exc!s}"],
                "goal_state": None,
            }
        return {
            "status": data.get("status", "error"),
            "goals_remaining": data.get("goals_remaining", -1),
            "sorry_count": data.get("sorry_count", -1),
            "error_messages": data.get("error_messages", []),
            "goal_state": data.get("goal_state"),
        }

    def _observation(
        self,
        *,
        goal_text: str,
        goals_remaining: int,
        sorry_count: int,
        status: str,
    ) -> np.ndarray:
        proof_lines = goal_text.count("\n")
        vec = self.encoder.encode(
            goal_text=goal_text,
            tactic_history=self._tactic_history[-self.encoder.history_dim:],
            vocab_size=len(TACTIC_VOCABULARY),
            goals_remaining=goals_remaining,
            sorry_count=sorry_count,
            proof_lines=proof_lines,
            status=status,
        )
        return np.asarray(vec, dtype=np.float32)


def _signal_to_dict(s: RewardSignal) -> dict[str, float]:
    return {
        "proof_complete": s.proof_complete,
        "superbest_bonus": s.superbest_bonus,
        "progress": s.progress,
        "valid_compile": s.valid_compile,
        "error": s.error,
        "dead_end": s.dead_end,
        "step": s.step,
        "total": s.total,
    }


# ── Gymnasium registration ────────────────────────────────────────────

# Only register once so re-imports are idempotent. Users who want
# the gym-style ``gym.make("EMLProof-v0")`` factory can supply
# their own kwargs (theorem_id + worker) via ``gym.make(...,
# theorem_id="depth_of_const", worker=lw)``.
_REGISTRY_ID = "EMLProof-v0"
try:
    if _REGISTRY_ID not in gym.envs.registry:  # type: ignore[operator]
        gym.register(
            id=_REGISTRY_ID,
            entry_point="petal.proof_gym.env:EMLProofEnv",
        )
except Exception:  # pragma: no cover - defensive
    pass
