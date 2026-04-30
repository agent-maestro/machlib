"""Five-strategy template generator for synthetic EML theorem variants.

Each strategy takes a base PETAL record and emits a list of
:class:`GeneratedVariant` objects. The variants are *candidates* —
they have not been verified by the kernel. Pass them through
:class:`petal.synthetic.Verifier` to filter to the ones that
actually compile.

Strategies
==========

  1. **constant_swap** — replace literal numerals (``1``, ``2``,
     ``Real.pi``) in the statement with a fresh universe-quantified
     variable. Often produces a strictly more general theorem.

  2. **domain_change** — swap one type for another at the level of
     statement variables (e.g. ``ℝ`` → ``ℂ``). The proof is
     copied verbatim and may or may not survive — verifier decides.

  3. **operator_swap** — replace the EML operator ``ceml`` with
     one of its 16 sister operators in the SuperBEST family.
     Many of these will fail; the small number that don't are
     the structural neighbours we want to learn about.

  4. **composition_depth** — wrap a depth-1 expression in another
     ``ceml(_, const 1)`` layer. Trivially produces a higher-depth
     analogue of the same theorem when the property is preserved
     under composition.

  5. **negation** — emit ``¬ (statement)`` as a candidate. Most
     will fail (the statement was true). The ones that pass are
     the falsifiable variants — useful negative examples.
"""
from __future__ import annotations

import re
from dataclasses import dataclass, field
from typing import Iterable, Optional


__all__ = [
    "EMLTheoremGenerator",
    "GeneratedVariant",
    "VARIATION_TYPES",
]


VARIATION_TYPES = (
    "constant_swap",
    "domain_change",
    "operator_swap",
    "composition_depth",
    "negation",
)


# Tunable per-strategy variant counts — keep these conservative;
# the cost is paid by Lake which has to type-check each candidate.
DEFAULT_VARIANTS_PER_STRATEGY: dict[str, int] = {
    "constant_swap": 5,
    "domain_change": 2,
    "operator_swap": 3,
    "composition_depth": 3,
    "negation": 2,
}


# Sister operators in the SuperBEST family (Tool 4 / paper).
SISTER_OPERATORS = (
    "eml",   # exp(x) - log(y)            — the canonical
    "eal",   # exp(x) + log(y)
    "exl",   # exp(x) * log(y)
    "edl",   # exp(x) / log(y)
    "epl",   # exp(x) ^ log(y)
)


@dataclass(frozen=True)
class GeneratedVariant:
    """One un-verified candidate variant of a base theorem.

    Carrying both the base theorem id and the strategy that
    produced it lets the verifier blame the right template when a
    candidate fails.
    """

    theorem_id: str          # synthetic id: ``<base>_<strategy>_<i>``
    base_theorem_id: str     # the PETAL record this came from
    strategy: str            # one of VARIATION_TYPES
    statement_lean4: str     # full statement (no proof)
    proof_lean4: str         # the proof body to try
    natural_language: str    # human-readable description
    metadata: dict = field(default_factory=dict)

    def to_dict(self) -> dict:
        return {
            "theorem_id": self.theorem_id,
            "base_theorem_id": self.base_theorem_id,
            "strategy": self.strategy,
            "statement_lean4": self.statement_lean4,
            "proof_lean4": self.proof_lean4,
            "natural_language": self.natural_language,
            "metadata": dict(self.metadata),
        }


# ─── Generator ──────────────────────────────────────────────────────


class EMLTheoremGenerator:
    """Template-based variant generator.

    Construct with the PETAL records, call :meth:`generate_all`
    to get every candidate variant the strategies produce. Pass
    the result to :class:`Verifier` to filter to verified-only.
    """

    def __init__(
        self,
        records: Iterable[dict],
        *,
        variants_per_strategy: Optional[dict[str, int]] = None,
        seed: int = 1,
    ) -> None:
        self.records = list(records)
        self.variants_per_strategy = (
            variants_per_strategy or DEFAULT_VARIANTS_PER_STRATEGY
        )
        self.seed = seed

    # ── public surface ───────────────────────────────────────────

    def generate_all(self) -> list[GeneratedVariant]:
        out: list[GeneratedVariant] = []
        for rec in self.records:
            out.extend(self.generate_for_record(rec))
        return out

    def generate_for_record(self, rec: dict) -> list[GeneratedVariant]:
        out: list[GeneratedVariant] = []
        for strategy in VARIATION_TYPES:
            count = self.variants_per_strategy.get(strategy, 0)
            for i in range(count):
                v = self._make_variant(rec, strategy, i)
                if v is not None:
                    out.append(v)
        return out

    # ── per-strategy ─────────────────────────────────────────────

    def _make_variant(
        self,
        rec: dict,
        strategy: str,
        i: int,
    ) -> Optional[GeneratedVariant]:
        if strategy == "constant_swap":
            return self._constant_swap(rec, i)
        if strategy == "domain_change":
            return self._domain_change(rec, i)
        if strategy == "operator_swap":
            return self._operator_swap(rec, i)
        if strategy == "composition_depth":
            return self._composition_depth(rec, i)
        if strategy == "negation":
            return self._negation(rec, i)
        return None

    # ── strategy implementations ─────────────────────────────────

    def _base(self, rec: dict) -> Optional[tuple[str, str, str]]:
        statement = (rec.get("statement") or {}).get("lean4", "").strip()
        proof = (rec.get("proof") or {}).get("lean4_full", "").strip()
        if not statement:
            return None
        nat = (rec.get("statement") or {}).get("natural_language", "")
        # Strip any `:=` body if it's in the statement field.
        if ":=" in statement:
            statement = statement.split(":=", 1)[0].rstrip()
        return statement, proof, nat

    def _id(self, base: str, strategy: str, i: int) -> str:
        return f"{base}_{strategy}_{i}"

    # constant_swap ............................................

    _LITERAL_RE = re.compile(r"\b(\d+)\b")

    def _constant_swap(
        self,
        rec: dict,
        i: int,
    ) -> Optional[GeneratedVariant]:
        base = self._base(rec)
        if base is None:
            return None
        statement, proof, nat = base
        # Only swap literal integers in the statement, not the proof.
        literals = self._LITERAL_RE.findall(statement)
        if not literals:
            return None
        # Pick the i-th literal to swap (cycle if i exceeds count).
        target = literals[i % len(literals)]
        new_var = f"k{i}"
        # Replace ONE occurrence of the literal with the variable
        # name; introduce a `(k_i : ℕ)` quantifier at the front.
        # Naive: no syntactic awareness. Verifier filters out the
        # mangled ones.
        new_statement = statement.replace(target, new_var, 1)
        new_statement = self._inject_param(
            new_statement, f"({new_var} : ℕ)"
        )
        return GeneratedVariant(
            theorem_id=self._id(rec.get("theorem_id", "x"), "constant_swap", i),
            base_theorem_id=rec.get("theorem_id", ""),
            strategy="constant_swap",
            statement_lean4=new_statement,
            proof_lean4=proof,
            natural_language=f"{nat} (with constant {target} promoted to a parameter {new_var})".strip(),
            metadata={"swapped_literal": target, "fresh_var": new_var},
        )

    # domain_change ............................................

    _DOMAIN_PAIRS = (
        ("ℝ", "ℂ"),
        ("Real", "Complex"),
        ("ℕ", "ℤ"),
    )

    def _domain_change(
        self,
        rec: dict,
        i: int,
    ) -> Optional[GeneratedVariant]:
        base = self._base(rec)
        if base is None:
            return None
        statement, proof, nat = base
        old, new = self._DOMAIN_PAIRS[i % len(self._DOMAIN_PAIRS)]
        if old not in statement:
            return None
        new_statement = statement.replace(old, new)
        new_proof = proof.replace(old, new)
        return GeneratedVariant(
            theorem_id=self._id(rec.get("theorem_id", "x"), "domain_change", i),
            base_theorem_id=rec.get("theorem_id", ""),
            strategy="domain_change",
            statement_lean4=new_statement,
            proof_lean4=new_proof,
            natural_language=f"{nat} (over {new} instead of {old})".strip(),
            metadata={"from_domain": old, "to_domain": new},
        )

    # operator_swap ............................................

    def _operator_swap(
        self,
        rec: dict,
        i: int,
    ) -> Optional[GeneratedVariant]:
        base = self._base(rec)
        if base is None:
            return None
        statement, proof, nat = base
        if "ceml" not in statement and "eml" not in statement:
            return None
        new_op = SISTER_OPERATORS[(i + 1) % len(SISTER_OPERATORS)]
        # Replace .ceml with the alternate constructor (won't exist
        # for the sisters yet — verifier will fail; that's the point).
        new_statement = statement.replace(".ceml", f".{new_op}")
        new_proof = proof.replace(".ceml", f".{new_op}")
        return GeneratedVariant(
            theorem_id=self._id(rec.get("theorem_id", "x"), "operator_swap", i),
            base_theorem_id=rec.get("theorem_id", ""),
            strategy="operator_swap",
            statement_lean4=new_statement,
            proof_lean4=new_proof,
            natural_language=f"{nat} (with ceml replaced by {new_op})".strip(),
            metadata={"swapped_to": new_op},
        )

    # composition_depth ........................................

    def _composition_depth(
        self,
        rec: dict,
        i: int,
    ) -> Optional[GeneratedVariant]:
        base = self._base(rec)
        if base is None:
            return None
        statement, proof, nat = base
        # We add `i + 1` extra layers of ceml-with-const-1 wrapping
        # around the variable. Conservative: only meaningful for
        # statements that mention ``EMLTree.var`` or ``expTree``.
        if "expTree" not in statement and "EMLTree.var" not in statement:
            return None
        wrap = "(.ceml " * (i + 1)
        close = " (.const 1))" * (i + 1)
        new_statement = statement.replace(
            "EMLTree.var", f"{wrap}EMLTree.var{close}"
        )
        return GeneratedVariant(
            theorem_id=self._id(
                rec.get("theorem_id", "x"), "composition_depth", i
            ),
            base_theorem_id=rec.get("theorem_id", ""),
            strategy="composition_depth",
            statement_lean4=new_statement,
            proof_lean4=proof,
            natural_language=(
                f"{nat} (with {i + 1} extra ceml(_, const 1) compositions)"
            ).strip(),
            metadata={"extra_layers": i + 1},
        )

    # negation .................................................

    def _negation(
        self,
        rec: dict,
        i: int,
    ) -> Optional[GeneratedVariant]:
        base = self._base(rec)
        if base is None:
            return None
        statement, proof, nat = base
        # Wrap the body of the statement in ``¬ (...)``. Crude:
        # find the colon that separates the binders from the body.
        colon = self._top_level_colon(statement)
        if colon < 0:
            return None
        binders = statement[:colon]
        body = statement[colon + 1:].lstrip()
        new_body = f"¬ ({body})"
        new_statement = f"{binders}: {new_body}"
        # No reasonable proof to attach; the verifier will reject
        # when the original was true. Use ``by sorry`` as a
        # placeholder so the verifier sees a valid skeleton.
        return GeneratedVariant(
            theorem_id=self._id(rec.get("theorem_id", "x"), "negation", i),
            base_theorem_id=rec.get("theorem_id", ""),
            strategy="negation",
            statement_lean4=new_statement,
            proof_lean4="by sorry",
            natural_language=f"NEGATION of: {nat}".strip(),
            metadata={"polarity": "negation"},
        )

    # ── helpers ──────────────────────────────────────────────────

    @staticmethod
    def _inject_param(statement: str, param_decl: str) -> str:
        """Insert a parameter declaration after `theorem NAME `.

        ``theorem foo : P`` → ``theorem foo (k : ℕ) : P``.
        Conservative: only when we can find a ``theorem|lemma`` head.
        """
        m = re.match(
            r"^(\s*)(theorem|lemma|def)\s+(\S+)\s+", statement
        )
        if not m:
            return statement
        idx = m.end()
        return statement[:idx] + f"{param_decl} " + statement[idx:]

    @staticmethod
    def _top_level_colon(statement: str) -> int:
        """Find the colon that separates binders from body.

        Skips colons inside parens / brackets / braces.
        """
        depth = 0
        for i, ch in enumerate(statement):
            if ch in "([{":
                depth += 1
            elif ch in ")]}":
                depth -= 1
            elif ch == ":" and depth == 0:
                # Avoid the second colon in `:=`.
                if i + 1 < len(statement) and statement[i + 1] == "=":
                    continue
                return i
        return -1
