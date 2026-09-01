/-
  sorry_audit.lean — regression gate: NO hidden `sorryAx` in MachLib.

  Walks every MachLib theorem/def and flags any that (transitively) depend on `sorryAx` —
  catching exactly the case where a tactic (e.g. the all-`try` `mach_ring`) silently swallows an
  unclosable goal into a `sorry` that compiles green. The one documented, intentional exception
  (a RED/GREEN teaching pair in ForgeTest.lean) is allowlisted; ANY other `sorryAx` is a regression
  and fails the build (non-zero exit).

  BOTH DIRECTIONS, added 2026-07-29. The allowlist must correspond EXACTLY to what actually carries
  `sorryAx` — an entry for a declaration that is now clean is a standing licence for the sorry to
  come back unnoticed, and it rots in the direction that feels safe (someone closed a proof; nobody
  went back to prune). So a stale entry now FAILS the gate and says which remedy applies (present +
  proven -> prune; absent -> deleted or renamed).

  FIRING SPECIMEN, historical rather than synthetic: on the run that introduced the check the gate
  went RED immediately on `guarded_lowering_preserves_domain_annotations`, allowlisted as "NOT
  closable as stated" and then closed anyway with footprint `[propext]`. The licence had outlived
  the sorry. Pruned; gate returns 0.

  Run:  cd foundations && lake env lean tools/sorry_audit.lean
  Exit: 0 on PASS, 1 on FAIL (verified 2026-07-28 in both directions; the rot direction verified
        2026-07-29, RED on the real stale entry then GREEN after pruning).

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
  --
  -- DISCHARGE CONDITION (added 2026-08-31, asked for by an outside reader who read "1 allowlisted"
  -- as a proof debt one step from becoming two). It is not a debt and it must NOT be discharged by
  -- proving it. This entry is the gate's FIRING SPECIMEN: the known-bad input whose passage would
  -- mean the gate had stopped working. It retires only when the teaching pair is deleted, or when a
  -- different firing specimen replaces it -- and removing it without a replacement REDUCES safety,
  -- because a gate with no specimen is unvalidated (see `feedback_gate_specimen_discipline`).
  -- The second entry this reader feared cannot arrive silently: allowlist ROT fails the gate in
  -- both directions, so a licence cannot outlive its sorry, and adding one requires editing this
  -- file.
  `MachLib.Real.halve_in_unit_sorry
  -- HighDimensional.lean module disclaimer: "intentionally carry `sorry`; formalization targets,
  -- not completed proof claims." Not in the public front door (what_is_proven.md); orphan.
  --
  -- 2026-07-28: `high_dim_ball_cube_ratio_tends_zero` was REMOVED FROM THIS LIST because it is now
  -- PROVEN (BallCubeRatio.lean). Pruning matters: an allowlist entry for a clean declaration is a
  -- silent licence for it to regress -- the gate would accept the sorry coming back. The allowlist
  -- must track what is actually broken, not what was ever broken.
  --
  -- 2026-07-29: `MachLib.HighDimensional.guarded_lowering_preserves_domain_annotations` REMOVED for
  -- the same reason, and it is worth recording that the paragraph above did not prevent it. It was
  -- allowlisted as "NOT closable as stated" -- and then closed anyway, by
  -- `GuardedLowering.guarded_lowering_preserves_domain`, footprint `[propext]`, no foothold axiom.
  -- Nobody pruned the entry, so the licence outlived the sorry by an unknown number of commits.
  -- Found by the pre-migration baseline capture, from a count disagreement: the gate said 1 sorryAx
  -- decl while the allowlist said 2 entries and `AUDIT_SORRY.md` prose said 2 carried it. Hence the
  -- ROT CHECK below -- a comment asking for pruning is not a mechanism, and this list is now
  -- required to correspond EXACTLY.
  ]

run_cmd do
  let env ← getEnv
  let mut allSorry : Array Name := #[]
  let mut bad : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if (`MachLib).isPrefixOf n then
      match ci with
      | .thmInfo _ | .defnInfo _ =>
        -- v4.32.2 made `CollectAxioms.collect` private, so this reached into an implementation
        -- detail until upstream closed it. `Lean.collectAxioms` is the public interface and always
        -- was; switching to it is the repair AND removes the reason this can break again.
        -- INSTRUMENT breakage, not a subject regression: the library built clean with its one
        -- allowlisted `sorry` while this gate could not compile.
        let axs ← Lean.collectAxioms n
        if axs.contains ``sorryAx then
          allSorry := allSorry.push n
          unless allowedSorry.contains n do bad := bad.push n
      | _ => pure ()
  -- BOTH DIRECTIONS, added 2026-07-29. The allowlist is a correspondence claim ("these decls carry
  -- sorry, on purpose"), so it rots the same way every other correspondence in this repo rots -- and
  -- it rots in the direction that FEELS SAFE: an entry for a declaration that is now clean is a
  -- standing licence for the sorry to come back unnoticed. The file's own comment said exactly this
  -- one entry earlier and it happened anyway, which is why it is now the GATE's job and not a note.
  let stale := allowedSorry.filter (fun n => !allSorry.contains n)
  if bad.isEmpty && stale.isEmpty then
    logInfo m!"SORRY-AUDIT PASS — {allSorry.size} sorryAx decls, allowlist {allowedSorry.length} entries, EXACT correspondence (documented drafts/tests); no hidden sorries across MachLib."
  else if !bad.isEmpty then
    throwError m!"SORRY-AUDIT FAIL — {bad.size} NON-allowlisted sorryAx decl(s): {bad.toList}"
  else
    throwError m!"SORRY-AUDIT FAIL — ALLOWLIST ROT: {stale.length} entr{if stale.length == 1 then "y" else "ies"} no longer carr{if stale.length == 1 then "ies" else "y"} sorryAx: {stale.map fun n => if (env.find? n).isSome then s!"{n} [present, now PROVEN -- prune it]" else s!"{n} [ABSENT from the environment -- deleted or renamed]"}. An allowlist entry for a clean declaration licenses the sorry to return silently. Prune it."
