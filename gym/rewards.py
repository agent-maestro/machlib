"""Reward shaping for the proof gym.

The reward signal is engineered to:

  * give a large terminal reward for closing a sorry cleanly,
  * reward intermediate goal-count reduction,
  * mildly discourage long proofs (step penalty),
  * heavily discourage repeating tactics PETAL has already
    documented as failing on this theorem.

The default weights come straight from the roadmap. Override via
:class:`RewardConfig`.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import Optional, Sequence


__all__ = [
    "RewardConfig",
    "RewardSignal",
    "compute_reward",
]


@dataclass(frozen=True)
class RewardConfig:
    """Knobs for reward shaping.

    The defaults match the roadmap spec:

      ``+100``  — proof complete (no sorry, build clean)
      ``+50``   — bonus for beating the SuperBEST node bound
      ``+10``   — goal count decreased on this step
      ``+1``    — compiled cleanly even with ``sorry`` remaining
      ``-1``    — error
      ``-5``    — repeated a known dead-end tactic from PETAL
      ``-0.1``  — step penalty
    """

    proof_complete_reward: float = 100.0
    superbest_bonus: float = 50.0
    progress_reward: float = 10.0
    valid_compile_reward: float = 1.0
    error_penalty: float = -1.0
    dead_end_penalty: float = -5.0
    step_penalty: float = -0.1


@dataclass(frozen=True)
class RewardSignal:
    """The decomposition of a single step's reward.

    Surfaces every component so a researcher can see why the
    agent got the reward it got. Sum of the floats equals the
    scalar reward returned by ``env.step``.
    """

    proof_complete: float = 0.0
    superbest_bonus: float = 0.0
    progress: float = 0.0
    valid_compile: float = 0.0
    error: float = 0.0
    dead_end: float = 0.0
    step: float = 0.0

    @property
    def total(self) -> float:
        return (
            self.proof_complete
            + self.superbest_bonus
            + self.progress
            + self.valid_compile
            + self.error
            + self.dead_end
            + self.step
        )


def compute_reward(
    *,
    status: str,
    sorry_count: int,
    goals_remaining: int,
    prev_goals_remaining: int,
    is_one_node_win: bool,
    tactic: str,
    petal_dead_ends: Sequence[str],
    config: Optional[RewardConfig] = None,
) -> RewardSignal:
    """Compute the reward decomposition for one step.

    Parameters
    ----------
    status:
        ``"success"`` / ``"error"`` / ``"timeout"`` / ``"unavailable"``
        — passed straight through from the worker.
    sorry_count:
        From the worker. ``0`` after a closed proof.
    goals_remaining:
        From the worker. ``0`` after a closed proof.
    prev_goals_remaining:
        Goal count BEFORE this step's tactic ran. ``-1`` on the
        very first step (no prior).
    is_one_node_win:
        ``True`` if the closed proof matches the SuperBEST node-
        count target — gives the bonus.
    tactic:
        The tactic the agent just played, as a string. Compared
        against ``petal_dead_ends`` for the dead-end penalty.
    petal_dead_ends:
        Tactics PETAL records have already documented as failing
        on this theorem.
    config:
        Override the default :class:`RewardConfig`.
    """
    cfg = config or RewardConfig()

    proof_complete = 0.0
    superbest_bonus = 0.0
    progress = 0.0
    valid_compile = 0.0
    error = 0.0
    dead_end = 0.0
    step = cfg.step_penalty

    proof_closed = (
        status == "success" and sorry_count == 0 and goals_remaining == 0
    )

    if proof_closed:
        proof_complete = cfg.proof_complete_reward
        if is_one_node_win:
            superbest_bonus = cfg.superbest_bonus

    elif status == "success":
        # Compiled clean but sorry remains: progress signal only.
        valid_compile = cfg.valid_compile_reward
        if (
            prev_goals_remaining > 0
            and goals_remaining >= 0
            and goals_remaining < prev_goals_remaining
        ):
            progress = cfg.progress_reward

    elif status == "error":
        error = cfg.error_penalty

    # Dead-end penalty is independent of status — the agent picked
    # a tactic that the corpus has already shown to fail here.
    if any(_match_tactic(tactic, dead) for dead in petal_dead_ends):
        dead_end = cfg.dead_end_penalty

    return RewardSignal(
        proof_complete=proof_complete,
        superbest_bonus=superbest_bonus,
        progress=progress,
        valid_compile=valid_compile,
        error=error,
        dead_end=dead_end,
        step=step,
    )


def _match_tactic(played: str, dead: str) -> bool:
    """Loose match: dead-end string appears as a token in the tactic.

    The PETAL records describe dead ends in prose ("ring fails
    here"), so we match by whole-word substring. Conservative —
    a dead end labelled ``"ring"`` only fires the penalty when the
    played tactic *contains* the word ``ring`` as a token.
    """
    if not played or not dead:
        return False
    played_l = played.lower()
    dead_l = dead.lower().strip()
    if not dead_l:
        return False
    # Whole-word check around the dead string.
    import re
    return bool(re.search(r"\b" + re.escape(dead_l) + r"\b", played_l))
