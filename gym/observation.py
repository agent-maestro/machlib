"""Observation encoding for the proof gym.

The roadmap suggests a 188-D float vector:

  ``[goal_embedding(128) + tactic_history(50) + metrics(10)]``

We don't have a real goal embedder yet (a future Phase 2.4 will
plug in a small transformer trained on the synthetic dataset from
Tool 3). For now the encoder produces a deterministic placeholder
based on string hashing — agents that train on this MUST be
re-trained when the embedding swap lands.

The tactic-history slot is a count vector over the recent N
tactics, the metrics slot reports goals_remaining / sorry_count /
proof_lines / status_one_hot.
"""
from __future__ import annotations

import hashlib
from dataclasses import dataclass
from typing import Optional, Sequence


__all__ = [
    "ObservationEncoder",
]


@dataclass
class ObservationEncoder:
    """Deterministic encoder from gym state to fixed-length float vector."""

    embed_dim: int = 128
    history_dim: int = 50
    metrics_dim: int = 10
    seed: int = 1

    @property
    def total_dim(self) -> int:
        return self.embed_dim + self.history_dim + self.metrics_dim

    def encode_goal(self, goal_text: Optional[str]) -> list[float]:
        """Hash-based 128-D embedding placeholder.

        Same input → same vector, different input → different
        vector. The values live in [-1, 1]. Stable across Python
        versions because we hash with sha256.
        """
        if not goal_text:
            return [0.0] * self.embed_dim
        digest = hashlib.sha256(goal_text.encode("utf-8")).digest()
        # Repeat the digest until we have enough bytes to fill the dim.
        needed = self.embed_dim
        bytestream = digest * ((needed // len(digest)) + 1)
        out: list[float] = []
        for i in range(needed):
            b = bytestream[i]
            # Map byte 0..255 → float in [-1, 1].
            out.append((b / 127.5) - 1.0)
        return out

    def encode_history(
        self,
        tactic_history: Sequence[int],
        vocab_size: int,
    ) -> list[float]:
        """One-hot-style count vector over the last `history_dim` actions.

        Each slot in the output corresponds to one action index in
        the vocabulary; the value is the number of times the agent
        played that action over the recent window. We bucket the
        first `history_dim` action indices; if the vocabulary is
        bigger than `history_dim` (it is — we have ~60 tactics),
        the last slot accumulates everything past `history_dim - 1`.
        """
        out = [0.0] * self.history_dim
        if vocab_size <= 0:
            return out
        for tac_idx in tactic_history:
            slot = min(tac_idx, self.history_dim - 1)
            if 0 <= slot < self.history_dim:
                out[slot] += 1.0
        # Normalise by the window length so the values are bounded.
        n = max(len(tactic_history), 1)
        return [v / n for v in out]

    def encode_metrics(
        self,
        *,
        goals_remaining: int,
        sorry_count: int,
        proof_lines: int,
        status: str,
    ) -> list[float]:
        """10-D scalar metric block.

        Layout (slot → meaning):
          0: goals_remaining (clipped to [-1, 5])
          1: sorry_count (clipped to [0, 5])
          2: proof_lines (clipped to [0, 50] / 50)
          3-6: status one-hot (success / error / timeout / unavailable)
          7: 1.0 if proof_complete else 0.0
          8: 1.0 if compiled_clean (status==success) else 0.0
          9: 1.0 reserved (always-on bias)
        """
        out = [0.0] * self.metrics_dim
        out[0] = float(max(-1, min(5, goals_remaining)))
        out[1] = float(max(0, min(5, sorry_count)))
        out[2] = float(max(0, min(50, proof_lines))) / 50.0

        status_idx = {
            "success": 3,
            "error": 4,
            "timeout": 5,
            "unavailable": 6,
        }.get(status, 4)
        out[status_idx] = 1.0

        proof_complete = (
            status == "success" and sorry_count == 0 and goals_remaining == 0
        )
        out[7] = 1.0 if proof_complete else 0.0
        out[8] = 1.0 if status == "success" else 0.0
        out[9] = 1.0
        return out

    def encode(
        self,
        *,
        goal_text: Optional[str],
        tactic_history: Sequence[int],
        vocab_size: int,
        goals_remaining: int,
        sorry_count: int,
        proof_lines: int,
        status: str,
    ) -> list[float]:
        """Compose the full 188-D observation vector."""
        return (
            self.encode_goal(goal_text)
            + self.encode_history(tactic_history, vocab_size)
            + self.encode_metrics(
                goals_remaining=goals_remaining,
                sorry_count=sorry_count,
                proof_lines=proof_lines,
                status=status,
            )
        )
