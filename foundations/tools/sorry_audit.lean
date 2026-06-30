/-
  sorry_audit.lean — regression gate: NO hidden `sorryAx` in MachLib.

  Walks every MachLib theorem/def and flags any that (transitively) depend on `sorryAx` —
  catching exactly the case where a tactic (e.g. the all-`try` `mach_ring`) silently swallows an
  unclosable goal into a `sorry` that compiles green. The three documented, intentional exceptions
  (a RED/GREEN teaching pair + the explicitly-disclaimed High-Dimensional draft queue) are
  allowlisted; ANY other `sorryAx` is a regression and fails the build (non-zero exit).

  Run:  cd foundations && lake env lean tools/sorry_audit.lean
-/
import MachLib
open Lean

/-- Intentional, documented sorry-bearing declarations. Anything else is a regression. -/
def allowedSorry : List Name := [
  -- ForgeTest.lean: RED skeleton paired with the GREEN `halve_in_unit` right below it
  `MachLib.Real.halve_in_unit_sorry,
  -- HighDimensional.lean module disclaimer: "intentionally carry `sorry`; formalization targets,
  -- not completed proof claims." Not in the public front door (what_is_proven.md); orphan (nothing
  -- depends on them).
  `MachLib.HighDimensional.high_dim_ball_cube_ratio_tends_zero,
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
    logInfo m!"SORRY-AUDIT PASS — {allSorry.size} sorryAx decls, all {allowedSorry.length} allowlisted (documented drafts/tests); no hidden sorries across MachLib."
  else
    throwError m!"SORRY-AUDIT FAIL — {bad.size} NON-allowlisted sorryAx decl(s): {bad.toList}"
