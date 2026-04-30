"""Tactic vocabulary for the proof gym.

The discrete action space is one tactic per index. Vocabulary mixes
common Lean tactics, compound combinations that close many EML
proofs, and a handful of EML-specific tactics from
``MonogateEML.Tactics`` (Tool 4).

The ordering is stable — RL checkpoints depend on action-index
identity, so DO NOT reorder this tuple. Add new tactics at the
end.
"""
from __future__ import annotations

# Standard Lean 4 / Mathlib tactics that close most goals.
COMMON_TACTICS: tuple[str, ...] = (
    "rfl",
    "trivial",
    "simp",
    "ring",
    "norm_num",
    "linarith",
    "nlinarith",
    "omega",
    "decide",
    "assumption",
    "exact?",
    "apply?",
    "constructor",
    "intro",
    "intros",
    "cases",
    "induction",
    "obtain",
    "rcases",
    "refine",
    "use",
    "ext",
    "funext",
    "by_contra",
    "contrapose",
    "exfalso",
    "left",
    "right",
    "push_neg",
    "norm_cast",
    "exact_mod_cast",
    "field_simp",
    "positivity",
)

# EML-specific simp-set / unfold combinations that recur in the
# monogate-lean library.
EML_SIMP_TACTICS: tuple[str, ...] = (
    "unfold eml",
    "unfold EMLTree.eval",
    "unfold EMLTree.depth",
    "simp [EMLTree.eval]",
    "simp [EMLTree.depth]",
    "simp [Real.log_one]",
    "simp [Real.exp_zero]",
    "simp only [eml, Real.log_one, sub_zero]",
    "simp [Real.exp_log, Real.log_exp]",
    "simp only [EMLTree.eval, EMLTree.depth, Complex.log_one, Complex.exp_zero, sub_zero]",
)

# Custom tactics from MonogateEML.Tactics (Tool 4 — shipped 2026-04-28).
EML_SPECIFIC_TACTICS: tuple[str, ...] = (
    "eml_auto",
    "eml_unfold",
    "eml_golf 1",
    "eml_golf 2",
    "eml_golf 3",
)

# Closure-witness shortcuts. These are the canonical lemma-applies
# that close IsEMLElementary goals.
EML_WITNESS_TACTICS: tuple[str, ...] = (
    "exact const_isEMLElementary _",
    "exact id_isEMLElementary",
    "exact exp_isEMLElementary",
    "exact exp_exp_isEMLElementary",
    "exact exp_const_isEMLElementary _",
    "apply IsEMLElementary.comp",
)

TACTIC_VOCABULARY: tuple[str, ...] = (
    COMMON_TACTICS
    + EML_SIMP_TACTICS
    + EML_SPECIFIC_TACTICS
    + EML_WITNESS_TACTICS
)


def tactic_index(tactic: str) -> int:
    """Lookup index in the vocabulary; ``-1`` if not present."""
    try:
        return TACTIC_VOCABULARY.index(tactic)
    except ValueError:
        return -1


def index_tactic(idx: int) -> str:
    """Return the tactic at ``idx`` in the vocabulary; raises on OOB."""
    return TACTIC_VOCABULARY[idx]
