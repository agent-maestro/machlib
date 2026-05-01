"""Multi-proof BFS search — Phase B-001 of the v2.0 strength roadmap.

Given a theorem and a tactic vocabulary, breadth-first over tactic
sequences up to a depth bound, asking a verifier whether each
candidate closes the goal. Returns every proof found within the
budget, tagged with style classification and length-based
optimality flags.

Architecture::

    MultiProofSearch
       │  takes: tactic vocab, max_depth, max_proofs, timeout
       │
       │  uses:  Verifier (protocol)
       │           ↳ HeuristicVerifier — no Lean, pattern-based
       │           ↳ LeanKernelVerifier — real verification (Phase B-002)
       │
       └─ emits: list[ProofRecord]
                   ↳ tactic sequence
                   ↳ tactic count
                   ↳ style classification
                   ↳ is_optimal (shortest found)
                   ↳ discovered_by + discovery_date

The engine is verifier-agnostic, deterministic given a vocab + depth,
and (for the heuristic verifier) fully CPU-only with no external
dependencies. The roadmap's targeted yield is 3-5 proofs per
theorem; that's tunable via ``max_proofs``.
"""
from __future__ import annotations

import time
from collections import deque
from dataclasses import dataclass, field
from datetime import date
from typing import Iterable

from .tactics import TACTIC_VOCABULARY
from .verifiers import HeuristicVerifier, Verifier

# ─── style classifier ──────────────────────────────────────────────

_STYLE_PATTERNS = (
    # Specific patterns first — eml_specific should win over the broader
    # ``direct`` fallback when the proof is an EML witness apply, and
    # ``automation`` should win over ``direct`` for tactics like
    # ``trivial`` that technically also match ``exact`` shapes.
    ("eml_specific",   lambda seq: any(t.startswith(("eml_", "exact const_isEML", "exact id_isEML", "exact exp_", "apply IsEMLElementary")) for t in seq)),
    ("automation",     lambda seq: any(t in {"decide", "omega", "linarith", "nlinarith", "norm_num", "ring", "trivial"} for t in seq)),
    ("simplification", lambda seq: any(t.startswith("simp") or t == "field_simp" for t in seq)),
    ("rewriting",      lambda seq: any(t.startswith(("rw ", "unfold", "conv")) for t in seq)),
    ("contradiction",  lambda seq: any(t in {"by_contra", "push_neg", "exfalso", "contrapose"} for t in seq)),
    ("induction",      lambda seq: any(t.startswith(("induction", "cases", "rcases", "obtain")) for t in seq)),
    ("calculation",    lambda seq: any(t.startswith("calc") for t in seq)),
    # Catch-all for a single-tactic proof using rfl or a generic exact.
    ("direct",         lambda seq: seq == ["rfl"] or all(t.startswith("exact") for t in seq)),
)


def classify_style(tactic_sequence: list[str]) -> str:
    """Deterministic style label for a finished proof. First match wins.

    Falls back to ``"mixed"`` when no pattern matches — that's the
    interesting case for "alien-optimal" proof discovery: short
    sequences that don't fit any known shape.
    """
    for label, predicate in _STYLE_PATTERNS:
        if predicate(tactic_sequence):
            return label
    return "mixed"


# ─── result records ────────────────────────────────────────────────


@dataclass(frozen=True)
class ProofRecord:
    """One candidate proof discovered by the search.

    Maps cleanly into MachLib's ``proofs[]`` schema: the engine
    populates ``tactics``, ``tactic_count``, ``style``,
    ``discovered_by``, ``discovery_date`` directly.
    ``is_optimal`` is set by the engine after all results land
    (shortest = optimal among results from this run).
    """
    tactic_sequence: tuple[str, ...]
    style: str
    discovered_by: str
    discovery_date: str
    is_optimal: bool = False
    verification_time_seconds: float = 0.0

    @property
    def tactic_count(self) -> int:
        return len(self.tactic_sequence)

    def to_machlib_proof(self, proof_id: str, eml_node_cost: int = 0) -> dict:
        """Render to the ``proofs[]`` shape used by MachLib records."""
        return {
            "id": proof_id,
            "tactics": list(self.tactic_sequence),
            "tactic_count": self.tactic_count,
            "eml_node_cost": eml_node_cost,
            "style": self.style,
            "is_optimal": self.is_optimal,
            "discovered_by": self.discovered_by,
            "discovery_date": self.discovery_date,
        }


@dataclass
class SearchStats:
    """Per-run accounting — useful for tuning depth + timeout."""
    candidates_tried: int = 0
    candidates_verified: int = 0
    proofs_found: int = 0
    elapsed_seconds: float = 0.0
    hit_depth_limit: bool = False
    hit_timeout: bool = False
    hit_proof_limit: bool = False
    style_counts: dict[str, int] = field(default_factory=dict)


# ─── the engine ────────────────────────────────────────────────────


class MultiProofSearch:
    """BFS over tactic sequences. Verifier-agnostic.

    Default vocab is the 54-tactic gym vocabulary (``TACTIC_VOCABULARY``).
    Default verifier is ``HeuristicVerifier`` — pattern-based, no Lean.
    Plug in ``LeanKernelVerifier`` (or any ``Verifier``) to run on
    real theorems.

    Example::

        search = MultiProofSearch(max_depth=2, max_proofs=5)
        proofs = search.find_all_proofs(
            "theorem t : (1 : Nat) = 1 := by sorry"
        )
        for p in proofs:
            print(p.tactic_count, p.style, p.tactic_sequence)
    """

    def __init__(
        self,
        *,
        tactic_vocab: Iterable[str] | None = None,
        verifier: Verifier | None = None,
        max_depth: int = 4,
        max_proofs: int = 5,
        timeout_seconds: float = 60.0,
    ):
        self.tactic_vocab: tuple[str, ...] = tuple(
            tactic_vocab if tactic_vocab is not None else TACTIC_VOCABULARY
        )
        self.verifier: Verifier = verifier or HeuristicVerifier()
        self.max_depth = max_depth
        self.max_proofs = max_proofs
        self.timeout_seconds = timeout_seconds

    def find_all_proofs(
        self,
        theorem_statement: str,
    ) -> tuple[list[ProofRecord], SearchStats]:
        """BFS until we hit ``max_proofs`` / ``max_depth`` / ``timeout_seconds``.

        Returns proofs in discovery order (shortest first by BFS
        property). The first proof is therefore always the shortest
        the engine can find within budget, and gets ``is_optimal=True``.
        """
        stats = SearchStats()
        started = time.perf_counter()
        deadline = started + self.timeout_seconds

        # BFS frontier: each item is a tactic sequence (tuple).
        # Empty sequence is the entry point — an unproven goal.
        frontier: deque[tuple[str, ...]] = deque([()])
        proofs: list[ProofRecord] = []

        while frontier:
            now = time.perf_counter()
            if now >= deadline:
                stats.hit_timeout = True
                break
            if len(proofs) >= self.max_proofs:
                stats.hit_proof_limit = True
                break

            current = frontier.popleft()

            if current:
                # Verify before extending — we want the shortest proofs first.
                stats.candidates_tried += 1
                v_start = time.perf_counter()
                ok = self.verifier.verify(
                    theorem_statement,
                    list(current),
                    timeout_seconds=max(0.1, deadline - now),
                )
                v_elapsed = time.perf_counter() - v_start
                stats.candidates_verified += 1

                if ok:
                    style = classify_style(list(current))
                    proofs.append(ProofRecord(
                        tactic_sequence=current,
                        style=style,
                        discovered_by=f"bfs_v1+{self.verifier.name}",
                        discovery_date=date.today().isoformat(),
                        verification_time_seconds=round(v_elapsed, 4),
                    ))
                    stats.style_counts[style] = stats.style_counts.get(style, 0) + 1
                    # Don't extend a closed proof.
                    continue

            # Extend the frontier with each tactic appended, up to depth.
            if len(current) >= self.max_depth:
                stats.hit_depth_limit = True
                continue
            for tactic in self.tactic_vocab:
                frontier.append(current + (tactic,))

        stats.elapsed_seconds = round(time.perf_counter() - started, 4)
        stats.proofs_found = len(proofs)

        # Mark the shortest as optimal. BFS gives shortest-first by
        # depth, so it's whichever has the smallest ``tactic_count``.
        if proofs:
            shortest = min(p.tactic_count for p in proofs)
            proofs = [
                ProofRecord(
                    tactic_sequence=p.tactic_sequence,
                    style=p.style,
                    discovered_by=p.discovered_by,
                    discovery_date=p.discovery_date,
                    is_optimal=(p.tactic_count == shortest),
                    verification_time_seconds=p.verification_time_seconds,
                )
                for p in proofs
            ]

        return proofs, stats
