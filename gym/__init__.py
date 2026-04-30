"""petal.proof_gym — Tool 2 of the LLM-native EML tools roadmap.

A Gymnasium-style environment where:

  * **state**  = the current Lean source + tactic history + metrics
  * **action** = one tactic from the EML-aware vocabulary
  * **reward** = MSE-style signal for proof closure, weighted by
                 SuperBEST node-count savings, with PETAL dead-end
                 penalties for tactics the corpus has already
                 documented as failing on this theorem.

The env calls the live Lean kernel through either:
  - a local :class:`petal.lean_worker.LeanWorker` instance, or
  - the deployed ``/api/lean/verify`` HTTP endpoint.

Public API:

    from petal.proof_gym import EMLProofEnv, RewardConfig
    from petal.proof_gym import TACTIC_VOCABULARY
    env = EMLProofEnv(
        theorem_id="depth_of_const",
        worker=LeanWorker(lean_repo="/path/to/monogate-lean"),
    )
    obs, info = env.reset()
    obs, reward, terminated, truncated, info = env.step(action)

Hard dependency: Tool 1 (``petal.lean_worker``) must be importable.
Soft dependency: ``gymnasium`` — required only when actually
constructing :class:`EMLProofEnv`. The vocabulary, reward
computation, and observation encoding remain importable and
testable without it.
"""
from __future__ import annotations

from .tactics import TACTIC_VOCABULARY, EML_SPECIFIC_TACTICS
from .rewards import RewardConfig, RewardSignal, compute_reward
from .observation import ObservationEncoder

# Soft import for the Gymnasium-using class. Importing gymnasium
# pulls in numpy + a slow import chain, so we delay it. The wrapper
# below makes ``EMLProofEnv`` importable from this package only when
# the user actually has gymnasium installed; otherwise a clear
# ImportError fires at construction time.
try:
    from .env import EMLProofEnv
    _GYM_AVAILABLE = True
except ImportError:  # pragma: no cover
    _GYM_AVAILABLE = False

    class EMLProofEnv:  # type: ignore[no-redef]
        """Stub raised when ``gymnasium`` is missing."""

        def __init__(self, *_args, **_kwargs):
            raise ImportError(
                "EMLProofEnv requires gymnasium. "
                "Install with: pip install gymnasium"
            )


__all__ = [
    "EMLProofEnv",
    "RewardConfig",
    "RewardSignal",
    "TACTIC_VOCABULARY",
    "EML_SPECIFIC_TACTICS",
    "ObservationEncoder",
    "compute_reward",
]
