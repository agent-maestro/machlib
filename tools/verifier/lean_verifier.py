"""Batch verification for generated variants.

Wraps :class:`petal.lean_worker.LeanWorker` with progress reporting,
optional timeout-per-candidate, and a "quick reject" sieve that
filters out variants whose statement contains tokens we know don't
exist (e.g. references to operators that aren't defined). Only the
candidates that survive the sieve actually invoke ``lake build``.

Cost expectations
=================

A single ``lake build`` of a fresh scratch module against a warm
Mathlib cache is in the 1–10 s range on a typical dev machine.
For a target of 3,000 verified variants, expect 1–3 hours of
wall-clock time. Run the verifier in a long-running process,
not from a notebook cell.
"""
from __future__ import annotations

import re
import time
from dataclasses import asdict, dataclass, field
from typing import Iterable, Optional, Sequence

from .generator import GeneratedVariant


__all__ = [
    "Verifier",
    "VerifiedVariant",
]


@dataclass(frozen=True)
class VerifiedVariant:
    """A candidate that survived ``lake build``."""

    theorem_id: str
    base_theorem_id: str
    strategy: str
    statement_lean4: str
    proof_lean4: str
    natural_language: str
    metadata: dict
    tactic_trace: tuple[str, ...]
    chain_order: int
    node_count: int
    cost_class: str
    build_time_seconds: float
    verified_at: str = ""

    def to_dict(self) -> dict:
        return asdict(self)


# ─── Quick-reject sieve ─────────────────────────────────────────────


# Tokens that, when present in a candidate's statement OR proof,
# guarantee a build failure — skip the lake call entirely. Add to
# this list as the generator gains new templates.
_BANNED_TOKENS = (
    ".eal", ".exl", ".edl", ".epl",   # placeholder constructors
                                       # not yet in monogate-lean
)


_TACTIC_RE = re.compile(
    r"\b("
    r"rfl|trivial|simp|ring|norm_num|linarith|nlinarith|omega|"
    r"decide|assumption|exact|apply|constructor|intro|intros|"
    r"cases|induction|obtain|rcases|refine|use|ext|funext|"
    r"by_contra|contrapose|exfalso|left|right|push_neg|"
    r"norm_cast|exact_mod_cast|field_simp|positivity|"
    r"eml_auto|eml_unfold|eml_golf|unfold|rw|show|have"
    r")\b"
)


def _quick_reject(v: GeneratedVariant) -> Optional[str]:
    """Return a reason string if we should skip lake; ``None`` to proceed."""
    text = v.statement_lean4 + "\n" + v.proof_lean4
    for tok in _BANNED_TOKENS:
        if tok in text:
            return f"banned token: {tok}"
    if not v.statement_lean4.strip():
        return "empty statement"
    return None


def _extract_tactics(proof: str) -> tuple[str, ...]:
    return tuple(_TACTIC_RE.findall(proof or ""))


# ─── Verifier ───────────────────────────────────────────────────────


class Verifier:
    """Run candidates through the LeanWorker and keep the green ones."""

    def __init__(
        self,
        worker,
        *,
        imports: Optional[Sequence[str]] = None,
        timeout_per_variant: float = 60.0,
        skip_quick_rejects: bool = True,
    ) -> None:
        self.worker = worker
        self.imports = tuple(imports) if imports is not None else None
        self.timeout = timeout_per_variant
        self.skip_quick_rejects = skip_quick_rejects

    def verify_one(
        self,
        v: GeneratedVariant,
    ) -> Optional[VerifiedVariant]:
        """Verify a single candidate. Returns ``None`` on rejection."""
        if self.skip_quick_rejects:
            reason = _quick_reject(v)
            if reason is not None:
                return None

        # Compose the source lake will see: statement + proof
        # appended together. The proof field already starts with
        # ``:= ...`` or ``by ...`` in the canonical PETAL format,
        # so we glue with a space.
        source = self._compose_source(v)
        t0 = time.time()
        result = self.worker.verify(
            source,
            imports=self.imports,
            timeout=self.timeout,
        )
        elapsed = time.time() - t0

        if result.status != "success" or result.sorry_count > 0:
            return None

        tactics = _extract_tactics(v.proof_lean4)

        # EML metrics (best-effort): the worker's eml_metrics dict
        # is empty in the MVP — populate ourselves from eml-cost
        # if it's installed.
        chain_order, node_count, cost_class = _profile(v.statement_lean4)

        from datetime import datetime, timezone
        return VerifiedVariant(
            theorem_id=v.theorem_id,
            base_theorem_id=v.base_theorem_id,
            strategy=v.strategy,
            statement_lean4=v.statement_lean4,
            proof_lean4=v.proof_lean4,
            natural_language=v.natural_language,
            metadata=dict(v.metadata),
            tactic_trace=tactics,
            chain_order=chain_order,
            node_count=node_count,
            cost_class=cost_class,
            build_time_seconds=round(elapsed, 3),
            verified_at=datetime.now(timezone.utc).isoformat(),
        )

    def verify_batch(
        self,
        variants: Iterable[GeneratedVariant],
        *,
        progress: bool = False,
    ) -> list[VerifiedVariant]:
        """Verify a batch of candidates. Returns only the verified."""
        survivors: list[VerifiedVariant] = []
        candidates = list(variants)
        n = len(candidates)
        for i, v in enumerate(candidates, start=1):
            verified = self.verify_one(v)
            if verified is not None:
                survivors.append(verified)
            if progress and (i % 25 == 0 or i == n):
                print(
                    f"  verified {len(survivors)} / processed {i} of {n} "
                    f"({100 * i / max(n, 1):.1f}%)"
                )
        return survivors

    # ── internals ────────────────────────────────────────────────

    def _compose_source(self, v: GeneratedVariant) -> str:
        """Glue statement + proof into a single Lean source block."""
        proof = v.proof_lean4.strip()
        # If the proof doesn't start with ``:=`` or ``by``, prepend
        # ``:= ``.
        if not proof:
            proof = "by sorry"
        if not proof.startswith(":=") and not proof.startswith("by"):
            proof = f":= {proof}"
        if proof.startswith("by"):
            proof = f":= {proof}"
        return f"{v.statement_lean4} {proof}\n"


# ─── Helpers ────────────────────────────────────────────────────────


def _profile(statement: str) -> tuple[int, int, str]:
    """Best-effort EML profile via eml-cost. Returns zeros on failure."""
    try:
        import sympy as sp  # noqa: F401  (eml-cost imports sympy)
        from eml_cost import analyze
        from eml_cost.profile import PfaffianProfile
    except ImportError:
        return (0, 0, "")
    # We don't try to parse Lean; the chain order of a Lean
    # statement is a property of the *expressions* it contains,
    # which are out of reach for our string-only generator.
    # Surface zeros as a deliberate "unknown" sentinel.
    _ = analyze, PfaffianProfile  # noqa: F841 — kept for future use
    return (0, 0, "")
