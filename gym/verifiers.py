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
    """Real Lean-kernel verification via local lake build.

    Wired up in C-239 (2026-05-03). Backend = local; delegates to
    the vendored ``gym._lean_worker.LeanWorker``, which:

      1. writes a unique scratch .lean inside the MachLib lake project
         (``foundations/MachLib/_SweepScratch_<n>.lean``),
      2. runs ``lake build MachLib._SweepScratch_<n>`` (cache-friendly —
         core MachLib oleans are reused),
      3. parses elaborator output via ``parse_lake_output``,
      4. cleans up the scratch file in ``finally``.

    Verifier protocol contract: ``verify(theorem_statement, tactic_sequence)``
    returns True iff substituting the tactic sequence for the unique
    target sorry sentinel results in a clean ``lake build`` AND the
    sorry count of the synthesised source equals
    ``count(theorem_statement) - 1`` (i.e. exactly one sorry — the
    target — was discharged, no new ones introduced, sibling sorries
    in the same file are tolerated).

    The driver MUST mark the target sorry with the
    :attr:`TARGET_SORRY_MARKER` sentinel before calling ``verify``.
    The synthesiser then string-replaces only that marker, so multi-
    theorem Discovered/ files can be verified per-theorem.

    Remote backend is not implemented in C-239.
    """

    name = "lean_kernel_v1"

    #: Sentinel string the driver inserts at the target sorry's
    #: position. The verifier substitutes the joined tactic sequence
    #: in place of this exact substring. Includes a Lean block
    #: comment so it remains a syntactically valid sorry while
    #: serving as a unique replacement marker.
    TARGET_SORRY_MARKER = "sorry /-TARGET-/"

    def __init__(
        self,
        *,
        backend: str = "local",
        project_root: str | None = None,
        default_timeout: float = 30.0,
    ) -> None:
        if backend != "local":
            raise NotImplementedError(
                f"backend={backend!r} not implemented; "
                "only 'local' is wired up in C-239."
            )
        self.backend = backend
        self.project_root = project_root
        self.default_timeout = default_timeout

        # Lazy import keeps test collection working when the lake
        # toolchain isn't on PATH. Construction proceeds; the
        # NotAvailable check fires only on the first verify() call.
        from pathlib import Path as _Path
        from ._lean_worker import LeanWorker

        if project_root is None:
            # Default: this file lives at machlib/gym/verifiers.py;
            # foundations/ is two parents up + "foundations".
            here = _Path(__file__).resolve()
            default_root = here.parent.parent / "foundations"
            root = default_root
        else:
            root = _Path(project_root)

        # Scratch basename includes the process PID so concurrent
        # worker processes don't collide on the same scratch file
        # path (the vendored ``_scratch_counter`` is per-process,
        # so without a PID suffix, worker A and worker B both
        # write ``_SweepScratch_1.lean`` and clobber each other).
        # C-239 parallelism fix.
        import os as _os
        self._worker = LeanWorker(
            lean_repo=root,
            scratch_namespace="MachLib",
            scratch_basename=f"_SweepScratch_p{_os.getpid()}",
            # Target source already imports MachLib.{Basic,EML,Trig,Forge}.
            # Pass empty default_imports so we don't double-import.
            default_imports=(),
            default_timeout=default_timeout,
        )

    def verify(
        self,
        theorem_statement: str,
        tactic_sequence: list[str],
        *,
        timeout_seconds: float = 30.0,
    ) -> bool:
        # Pre-flight: the driver MUST mark the target sorry with the
        # sentinel. If the marker isn't present, fail closed — a
        # successful build wouldn't tell us whether the candidate
        # closed THIS theorem or some other coincidentally-resolved
        # one.
        if self.TARGET_SORRY_MARKER not in theorem_statement:
            return False

        # Synthesise: replace ONLY the sentinel (occurrence 1) with
        # the tactic sequence joined by newlines, indented to match
        # the existing `unfold X` line in the Discovered/ shape
        # (2-space indentation under `:= by`).
        replacement = "\n  ".join(tactic_sequence) if tactic_sequence else ""
        synthesised = theorem_statement.replace(
            self.TARGET_SORRY_MARKER,
            replacement,
            1,
        )

        # Defensive: if the synthesised source still contains the
        # marker (multiple sentinels would mean a driver bug), reject.
        if self.TARGET_SORRY_MARKER in synthesised:
            return False

        # Compute expected post-substitution sorry count. The
        # vendored worker counts sorries via `\bsorry\b`, which
        # matches both the target marker (``sorry /-TARGET-/``) and
        # ordinary sibling sorries (``sorry  -- TODO: ...``). After
        # substitution, the count must drop by exactly one.
        from ._lean_worker import _count_sorries  # internal helper
        n_before = _count_sorries(theorem_statement)
        n_expected = n_before - 1

        # Run lake build on the synthesised source.
        result = self._worker.verify(synthesised, timeout=timeout_seconds)

        if result.status != "success":
            return False
        if result.sorry_count != n_expected:
            return False
        return True
