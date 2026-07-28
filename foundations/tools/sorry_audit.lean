/-
  sorry_audit.lean — regression gate: NO hidden `sorryAx` in MachLib.

  Walks every MachLib theorem/def and flags any that (transitively) depend on `sorryAx` —
  catching exactly the case where a tactic (e.g. the all-`try` `mach_ring`) silently swallows an
  unclosable goal into a `sorry` that compiles green. The three documented, intentional exceptions
  (a RED/GREEN teaching pair + the explicitly-disclaimed High-Dimensional draft queue) are
  allowlisted; ANY other `sorryAx` is a regression and fails the build (non-zero exit).

  Run:  cd foundations && lake env lean tools/sorry_audit.lean
  Exit: 0 on PASS, 1 on FAIL (verified 2026-07-28 in both directions).

  SCOPE LIMIT, found 2026-07-28 by a canary that DID NOT fire. The walk filters on
  `(`MachLib).isPrefixOf n`, so it sees declarations under `MachLib.*` and NOTHING ELSE. An
  injected `theorem audit_canary_regression : True := by sorry` appended AFTER `end MachLib` in
  ForgeTest.lean was invisible to this gate; moved INSIDE the namespace it fires immediately and
  names the offender. The gate is sound for its stated scope and blind outside it -- which matters
  because appending to the end of a file is exactly how a declaration ends up at root by accident.
  If a top-level namespace other than `MachLib` is ever added, this filter must widen with it.
-/
import MachLib
open Lean

/-- Intentional, documented sorry-bearing declarations. Anything else is a regression. -/
def allowedSorry : List Name := [
  -- ForgeTest.lean: RED skeleton paired with the GREEN `halve_in_unit` right below it
  `MachLib.Real.halve_in_unit_sorry,
  -- HighDimensional.lean module disclaimer: "intentionally carry `sorry`; formalization targets,
  -- not completed proof claims." Not in the public front door (what_is_proven.md); orphan.
  --
  -- 2026-07-28: `high_dim_ball_cube_ratio_tends_zero` was REMOVED FROM THIS LIST because it is now
  -- PROVEN (BallCubeRatio.lean). Pruning matters: an allowlist entry for a clean declaration is a
  -- silent licence for it to regress -- the gate would accept the sorry coming back. The allowlist
  -- must track what is actually broken, not what was ever broken.
  --
  -- The one that remains is NOT closable as stated: `ReplayPacket`, `ValidGuards` and
  -- `DomainPreserved` are all opaque placeholders with zero content, so `ValidGuards p ->
  -- DomainPreserved p` is an implication between two uninterpreted predicates. Closing it means
  -- SPECIFYING the IR's guard semantics -- a different project, and arguably one that belongs in
  -- Forge rather than machlib. Adding a "foothold axiom" to discharge it (the idiom the rest of
  -- that file uses) would be strictly WORSE than the sorry: it moves a visible gap into the
  -- invisible axiom ledger.
  `MachLib.HighDimensional.guarded_lowering_preserves_domain_annotations ]

run_cmd do
  let env ← getEnv
  let mut allSorry : Array Name := #[]
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`MachLib).isPrefixOf n then
      match ci with
      | .thmInfo _ | .defnInfo _ =>
        let (_, s) := ((CollectAxioms.collect n).run env).run {}
        if s.axioms.contains ``sorryAx then
          allSorry := allSorry.push n
          unless allowedSorry.contains n do bad := bad.push n
      | _ => pure ()
  if bad.isEmpty then
    logInfo m!"SORRY-AUDIT PASS — {allSorry.size} sorryAx decls, all allowlisted ({allowedSorry.length} entries) (documented drafts/tests); no hidden sorries across MachLib."
  else
    throwError m!"SORRY-AUDIT FAIL — {bad.size} NON-allowlisted sorryAx decl(s): {bad.toList}"
