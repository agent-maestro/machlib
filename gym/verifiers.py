"""Verifier interface for proof-search engines.

The multi-proof engine (``gym.multi_proof``) is verifier-agnostic: it
generates candidate tactic sequences, then asks a ``Verifier`` whether
each one closes a given theorem. Two implementations ship today:

  * ``HeuristicVerifier`` — pattern-based, no Lean. Recognises a small
    set of trivial-but-valid tactic shapes (``rfl`` on ``x = x`` goals,
    ``trivial`` on ``True`` goals, ``decide`` on ``Decidable Prop``
    statements). Useful for testing the pipeline end-to-end without
    a Lean toolchain on the path.

  * ``LeanKernelVerifier`` — invokes ``lake env lean`` on a synthesised
    .lean file containing the theorem statement and candidate tactics,
    then parses elaborator output. Pluggable: either a local lake
    project or PETAL's ``/api/lean/verify`` endpoint can back the
    `_run_lean` method. Stubbed today (raises ``NotImplementedError``)
    pending the toolchain wiring decided in Phase B-002.

Adding a new verifier (e.g. an LSP-based goal-state introspector, a
remote service, an ML-predicted "likely closes" model) means
implementing the ``Verifier`` protocol's two methods.
"""
from __future__ import annotations

import re
from typing import Protocol, runtime_checkable


@runtime_checkable
class Verifier(Protocol):
    """The proof-search engine's view of "does this tactic sequence work"."""

    def verify(
        self,
        theorem_statement: str,
        tactic_sequence: list[str],
        *,
        timeout_seconds: float = 30.0,
    ) -> bool:
        """Return True iff ``tactic_sequence`` closes ``theorem_statement``.

        Implementations must be side-effect-free (no filesystem writes
        outside their own caches) so the search engine can call them
        in parallel without coordination.
        """
        ...

    @property
    def name(self) -> str:
        """Stable identifier for record provenance, e.g. ``"lean_kernel_v1"``."""
        ...


# ─── HeuristicVerifier ─────────────────────────────────────────────


class HeuristicVerifier:
    """Pattern-based mock — recognises a small set of trivial proofs.

    Truth table:
      * ``[rfl]``                  closes any goal that parses as ``x = x``
                                    (after whitespace + paren normalisation).
      * ``[trivial]``              closes ``True`` and any ``x = x``.
      * ``[decide]``               closes any goal containing only
                                    ``OfNat`` literals and ``=``/``<``/``≤``.
      * ``[simp]``                 closes goals that match a known simp-set
                                    rewrite (defs of ``log_one``, ``exp_zero``,
                                    ``sub_zero``, ``add_zero``).
      * ``[unfold X; rfl]``        closes goals where the LHS is the application
                                    of a definition that, after beta-reduction,
                                    equals the RHS literal.

    This is INTENTIONALLY conservative — false negatives are fine
    (engine just rejects a candidate); false positives would be
    catastrophic (engine marks a record as proven when it isn't).
    """

    name = "heuristic_v1"

    _RFL_GOAL = re.compile(r"^\s*([^=]+?)\s*=\s*\1\s*$")
    _TRIVIAL_GOAL = re.compile(r"^\s*True\s*$")
    _LITERAL_GOAL = re.compile(r"^\s*\(?\s*\d+\s*[=<≤]\s*\d+\s*\)?\s*$")

    def verify(
        self,
        theorem_statement: str,
        tactic_sequence: list[str],
        *,
        timeout_seconds: float = 30.0,
    ) -> bool:
        goal = self._extract_goal(theorem_statement)
        if goal is None:
            return False

        if not tactic_sequence:
            return False

        # Single-tactic shortcuts.
        first = tactic_sequence[0].strip()
        if len(tactic_sequence) == 1:
            if first == "rfl":
                return self._RFL_GOAL.match(goal) is not None
            if first == "trivial":
                return (
                    self._TRIVIAL_GOAL.match(goal) is not None
                    or self._RFL_GOAL.match(goal) is not None
                )
            if first == "decide":
                return self._LITERAL_GOAL.match(goal) is not None

        # Compound: unfold X; rfl on a definition-application.
        if (
            len(tactic_sequence) == 2
            and tactic_sequence[0].startswith("unfold ")
            and tactic_sequence[1] == "rfl"
        ):
            # We can't beta-reduce without a real elaborator, so we
            # only accept this when the goal is *already* `x = x`.
            return self._RFL_GOAL.match(goal) is not None

        return False

    @staticmethod
    def _extract_goal(theorem_statement: str) -> str | None:
        """Pull the goal expression out of a Lean theorem declaration.

        Recognises::

            theorem name : <goal> := <proof>
            theorem name (args) : <goal> := <proof>
            example : <goal> := <proof>
        """
        # Strip everything up to the last ' : ' before ':=' (or end).
        body = theorem_statement
        # Cut off at `:=` so we ignore the proof body.
        proof_split = body.split(":=", 1)
        head = proof_split[0]
        # Heuristic: the goal starts after the LAST ' : ' that follows
        # the declaration arguments. The declaration's own type
        # ascription uses a single ':'. Anywhere args contain ':' we'd
        # mis-parse; for the heuristic verifier this is acceptable.
        # Look for the pattern '... ) :' or '... id :'.
        m = re.search(r":\s*([^=].*)$", head, re.DOTALL)
        if not m:
            return None
        return m.group(1).strip()


# ─── LeanKernelVerifier (scaffold) ────────────────────────────────


class LeanKernelVerifier:
    """Real Lean-kernel verification — pluggable backend, stubbed today.

    Two backends are anticipated:

      * **Local** — synthesise a .lean file in a tmp dir, run
        ``lake env lean <file>`` from a MachLib project root, parse
        return code + stderr.

      * **Remote** — POST to PETAL's ``/api/lean/verify`` endpoint.

    Phase B-002 chooses which backend to wire up first; both follow
    the same ``Verifier`` contract here.
    """

    name = "lean_kernel_v1"

    def __init__(self, *, backend: str = "local", project_root: str | None = None):
        self.backend = backend
        self.project_root = project_root

    def verify(
        self,
        theorem_statement: str,
        tactic_sequence: list[str],
        *,
        timeout_seconds: float = 30.0,
    ) -> bool:
        raise NotImplementedError(
            "LeanKernelVerifier is scaffolded but not wired up. "
            "Phase B-002 picks local-vs-remote and implements `_run_lean`. "
            "Use HeuristicVerifier for end-to-end pipeline tests."
        )
