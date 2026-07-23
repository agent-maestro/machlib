import MachLib.EMLCertcomGrounded

/-!
# The compositional Certcom handshake: arbitrary `var`+`eml` trees, one reusable lemma

`EMLCertcomGrounded.lean` grounded exactly ONE tree, `EMLTree.eml EMLTree.var EMLTree.var`, by hand.
This file generalizes that construction to ANY `EMLTree` built from `var`/`eml` alone (arbitrary depth,
arbitrary shape) — the "Groundable" pipeline: one recursive translation, one recursive validity
predicate, one recursive error-bound function, and one theorem proved by structural induction that
every such tree inherits automatically. Adding a supported constructor to this fragment would need
exactly one new case in each of the four definitions below, not a bespoke per-tree proof.

**Scope: `var`+`eml` only, no `const`.** `EMLTree.const : Real → EMLTree` takes a `MachLib.Real`;
translating it needs `floatOfR`, and — unlike a bare `.var` read — every `const` LEAF then carries its
own quantization error (`real_round_bounds`), which must itself propagate through however many
`exp`/`log` layers sit above it, compounding with each level's own Lipschitz amplification. That is
real, additional complexity (not present in the single-tree case, where the ONE variable read carries
zero error) and is deliberately left for a follow-up, exactly as `EMLCertcomBridge.lean` deliberately
scoped past `const` for the same reason at depth 1. Every tree built purely from `var`/`eml` — which is
already an unbounded, arbitrary-shape family — is fully covered here.
-/

namespace Certcom

open MachLib MachLib.Real

/-- Real semantics for Option D's `EMLTree`, read through Certcom's own `Trans1`: `.exp ↦ exp`,
`.ln ↦ log` (the only two primitives a `var`+`eml` translation ever produces). -/
noncomputable def realOfEML : Trans1 → MachLib.Real → MachLib.Real
  | .exp => exp | .ln => log | _ => id

/-- Certcom's compiled form of a `var`+`eml` `EMLTree`, decomposed exactly like `emlVarVar`
(`EMLCertcomBridge.lean`), recursively: `eml t1 t2 ↦ exp(⟦t1⟧) − log(⟦t2⟧)`. The `const` case is
unreachable for any tree satisfying `EMLTreeVarValid` below (see the module docstring); given here
only so the function is total. -/
def toCertcomEML : EMLTree → EML
  | .const _ => .lit 0.0
  | .var => .var "x"
  | .eml t1 t2 => .bin .sub (.tr1 .exp (toCertcomEML t1)) (.tr1 .ln (toCertcomEML t2))

/-- **The explicit, recursively-computed forward-error bound** — the "one reusable primitive-
grounding lemma" applied at every `eml` node. `t1`'s bound `E1` gives a magnitude envelope
`[xe1 − E1, xe1 + E1]` for `exp`'s Lipschitz domain (`hi1 := xe1 + E1`, matching `real_exp_rounds`'
own shape); `t2`'s bound `E2` gives `[xe2 − E2, xe2 + E2]` for `log`'s (needing the positivity margin
`EMLTreeVarValid` requires). The formula is `absenc_lip_local` (Lipschitz-amplify + primitive round)
composed twice, then `absenc_sub`'s cross term — the same shape `EMLCertcomGrounded.lean`'s
`eml_var_var_pipeline_uniform_grounded` derives by hand for the ONE fixed tree `eml var var`, here
produced automatically for any tree. -/
noncomputable def emlTreeErrorBound : EMLTree → Real → Real
  | .const _, _ => 0
  | .var, _ => 0
  | .eml t1 t2, x =>
      let E1 := emlTreeErrorBound t1 x
      let E2 := emlTreeErrorBound t2 x
      let hi1 := t1.eval x + E1
      let lo2 := t2.eval x - E2
      let hi2 := t2.eval x + E2
      let Ex := u * exp hi1 + exp hi1 * E1
      let Ey := u * (abs (log lo2) + abs (log hi2)) + (1 / lo2) * E2
      u * ((exp hi1 + Ex) + ((abs (log lo2) + abs (log hi2)) + Ey)) + (Ex + Ey)

/-- **Pointwise validity for `var`+`eml` trees**: at every `eml` node, the log argument's own error
envelope must stay strictly inside the positive reals — `emlTreeErrorBound t2 x < t2.eval x` — the
pointwise analogue of `EMLPfaffianValidOn`'s interval-wide positivity condition, sharpened to also
cover the compiled artifact's own rounding slop, not just the exact value's sign. -/
inductive EMLTreeVarValid (x : Real) : EMLTree → Prop
  | var : EMLTreeVarValid x .var
  | eml (t1 t2 : EMLTree) (hmargin : emlTreeErrorBound t2 x < t2.eval x) :
      EMLTreeVarValid x t1 → EMLTreeVarValid x t2 → EMLTreeVarValid x (.eml t1 t2)

/-- `emlTreeErrorBound` is non-negative, GIVEN validity (the `1/lo2` term needs `lo2 > 0`, which only
holds under `EMLTreeVarValid`'s positivity margin — not an unconditional fact about the raw formula).
Proved by induction on the validity derivation itself, not on `EMLTree` directly, so `hmargin`/the IH
are available exactly where the `.eml` case's division needs them. -/
theorem emlTreeErrorBound_nonneg {x : Real} : ∀ {t : EMLTree}, EMLTreeVarValid x t →
    0 ≤ emlTreeErrorBound t x := by
  intro t hv
  induction hv with
  | var => exact le_refl 0
  | eml t1 t2 hmargin _ _ ih1 ih2 =>
      have hE1 : (0:Real) ≤ emlTreeErrorBound t1 x := ih1
      have hE2 : (0:Real) ≤ emlTreeErrorBound t2 x := ih2
      have hlo2pos : (0:Real) < t2.eval x - emlTreeErrorBound t2 x := sub_pos_of_lt hmargin
      have hEx : (0:Real) ≤ u * exp (t1.eval x + emlTreeErrorBound t1 x)
            + exp (t1.eval x + emlTreeErrorBound t1 x) * emlTreeErrorBound t1 x :=
        add_nonneg (mul_nonneg u_nonneg (le_of_lt (exp_pos _)))
          (mul_nonneg (le_of_lt (exp_pos _)) hE1)
      have hEy : (0:Real) ≤ u * (abs (log (t2.eval x - emlTreeErrorBound t2 x))
              + abs (log (t2.eval x + emlTreeErrorBound t2 x)))
            + (1 / (t2.eval x - emlTreeErrorBound t2 x)) * emlTreeErrorBound t2 x :=
        add_nonneg (mul_nonneg u_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)))
          (mul_nonneg (le_of_lt (one_div_pos_of_pos hlo2pos)) hE2)
      show (0:Real) ≤ u * ((exp (t1.eval x + emlTreeErrorBound t1 x)
              + (u * exp (t1.eval x + emlTreeErrorBound t1 x)
                + exp (t1.eval x + emlTreeErrorBound t1 x) * emlTreeErrorBound t1 x))
            + ((abs (log (t2.eval x - emlTreeErrorBound t2 x))
                + abs (log (t2.eval x + emlTreeErrorBound t2 x)))
              + (u * (abs (log (t2.eval x - emlTreeErrorBound t2 x))
                  + abs (log (t2.eval x + emlTreeErrorBound t2 x)))
                + (1 / (t2.eval x - emlTreeErrorBound t2 x)) * emlTreeErrorBound t2 x)))
          + ((u * exp (t1.eval x + emlTreeErrorBound t1 x)
                + exp (t1.eval x + emlTreeErrorBound t1 x) * emlTreeErrorBound t1 x)
            + (u * (abs (log (t2.eval x - emlTreeErrorBound t2 x))
                  + abs (log (t2.eval x + emlTreeErrorBound t2 x)))
              + (1 / (t2.eval x - emlTreeErrorBound t2 x)) * emlTreeErrorBound t2 x))
      exact add_nonneg
        (mul_nonneg u_nonneg
          (add_nonneg (add_nonneg (le_of_lt (exp_pos _)) hEx)
            (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hEy)))
        (add_nonneg hEx hEy)

/-- **The compositional Certcom handshake.** For ANY `var`+`eml` `EMLTree` `t`, valid at the point
`x := realToR (env "x").toF` (`EMLTreeVarValid`): `toCertcomEML t` is in Certcom's own certified
nested-local fold fragment (`IsFoldLocal`), its exact real semantics agree with `t.eval x` EXACTLY
(zero approximation — no constants, no rounding enters the exact-real layer for a `var`+`eml` tree),
and its COMPILED evaluation is within the explicit, recursively-computed `emlTreeErrorBound t x` of
`t.eval x`. One induction on `EMLTreeVarValid`, reusing `absenc_lip_local`/`absenc_sub` directly at
the `eml` case (not routed through `pipeline_nested_local`'s own existential, so the bound comes out
in `emlTreeErrorBound`'s EXACT closed form, not merely "some" bound) — building `IsFoldLocal` too,
alongside, as a reusable witness for anyone who also wants the emitted-C connection via
`pipeline_nested_local`/`emitC_correct`. -/
theorem eml_tree_var_grounded (env : Env) : ∀ (t : EMLTree),
    EMLTreeVarValid (realToR (env "x").toF) t →
      IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env (toCertcomEML t) ∧
      exactRn realToR realOfEML env (toCertcomEML t) = t.eval (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t)).toF
          - t.eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound t (realToR (env "x").toF) := by
  intro t hv
  induction hv with
  | var =>
      refine ⟨IsFoldLocal.var "x", rfl, ?_⟩
      show abs (realToR (env "x").toF - realToR (env "x").toF) ≤ 0
      rw [sub_self]; exact le_of_eq abs_zero
  | eml t1 t2 hmargin hv1 hv2 ih1 ih2 =>
      obtain ⟨hfold1, hexact1, herr1⟩ := ih1
      obtain ⟨hfold2, hexact2, herr2⟩ := ih2
      have hE1nn : (0:Real) ≤ emlTreeErrorBound t1 (realToR (env "x").toF) :=
        emlTreeErrorBound_nonneg hv1
      have hE2nn : (0:Real) ≤ emlTreeErrorBound t2 (realToR (env "x").toF) :=
        emlTreeErrorBound_nonneg hv2
      have hlo2pos : (0:Real) < t2.eval (realToR (env "x").toF)
          - emlTreeErrorBound t2 (realToR (env "x").toF) := sub_pos_of_lt hmargin
      -- bounds on t1's computed value, from herr1 (abs form → two-sided)
      have h1lo : t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF)
          ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF := by
        have h1 : -(emlTreeErrorBound t1 (realToR (env "x").toF))
            ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF
              - t1.eval (realToR (env "x").toF) := (abs_le_iff.mp herr1).1
        have e4 : t1.eval (realToR (env "x").toF)
            + (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF
              - t1.eval (realToR (env "x").toF))
            = realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF := by
          mach_ring
        have e3 : t1.eval (realToR (env "x").toF) + -(emlTreeErrorBound t1 (realToR (env "x").toF))
            = t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF) := by
          mach_ring
        have h2' := add_le_add_left h1 (t1.eval (realToR (env "x").toF))
        rw [e3, e4] at h2'; exact h2'
      have h1hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF
          ≤ t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF) := by
        have h1 : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF
              - t1.eval (realToR (env "x").toF) ≤ emlTreeErrorBound t1 (realToR (env "x").toF) :=
          (abs_le_iff.mp herr1).2
        have e4 : t1.eval (realToR (env "x").toF)
            + (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF
              - t1.eval (realToR (env "x").toF))
            = realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF := by
          mach_ring
        have h2' := add_le_add_left h1 (t1.eval (realToR (env "x").toF))
        rw [e4] at h2'; exact h2'
      -- bounds on t2's computed value, same pattern
      have h2lo : t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
          ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF := by
        have h1 : -(emlTreeErrorBound t2 (realToR (env "x").toF))
            ≤ realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF
              - t2.eval (realToR (env "x").toF) := (abs_le_iff.mp herr2).1
        have e4 : t2.eval (realToR (env "x").toF)
            + (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF
              - t2.eval (realToR (env "x").toF))
            = realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF := by
          mach_ring
        have e3 : t2.eval (realToR (env "x").toF) + -(emlTreeErrorBound t2 (realToR (env "x").toF))
            = t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF) := by
          mach_ring
        have h2' := add_le_add_left h1 (t2.eval (realToR (env "x").toF))
        rw [e3, e4] at h2'; exact h2'
      have h2hi : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF
          ≤ t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF) := by
        have h1 : realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF
              - t2.eval (realToR (env "x").toF) ≤ emlTreeErrorBound t2 (realToR (env "x").toF) :=
          (abs_le_iff.mp herr2).2
        have e4 : t2.eval (realToR (env "x").toF)
            + (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF
              - t2.eval (realToR (env "x").toF))
            = realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF := by
          mach_ring
        have h2' := add_le_add_left h1 (t2.eval (realToR (env "x").toF))
        rw [e4] at h2'; exact h2'
      -- exact-value bounds (equalities, widened via the nonneg error)
      have h1xe_lo : t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF)
          ≤ exactRn realToR realOfEML env (toCertcomEML t1) := by
        rw [hexact1]
        have e : t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF)
              ≤ t1.eval (realToR (env "x").toF) - 0 :=
          sub_le_sub_left hE1nn (t1.eval (realToR (env "x").toF))
        have e2 : t1.eval (realToR (env "x").toF) - 0 = t1.eval (realToR (env "x").toF) := by
          mach_ring
        rw [e2] at e; exact e
      have h1xe_hi : exactRn realToR realOfEML env (toCertcomEML t1)
          ≤ t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF) := by
        rw [hexact1]
        have e2 : t1.eval (realToR (env "x").toF) + 0 = t1.eval (realToR (env "x").toF) := by
          mach_ring
        have e : t1.eval (realToR (env "x").toF) + 0
              ≤ t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF) :=
          add_le_add_left hE1nn _
        rw [e2] at e; exact e
      have h2xe_lo : t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
          ≤ exactRn realToR realOfEML env (toCertcomEML t2) := by
        rw [hexact2]
        have e : t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
              ≤ t2.eval (realToR (env "x").toF) - 0 :=
          sub_le_sub_left hE2nn (t2.eval (realToR (env "x").toF))
        have e2 : t2.eval (realToR (env "x").toF) - 0 = t2.eval (realToR (env "x").toF) := by
          mach_ring
        rw [e2] at e; exact e
      have h2xe_hi : exactRn realToR realOfEML env (toCertcomEML t2)
          ≤ t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF) := by
        rw [hexact2]
        have e2 : t2.eval (realToR (env "x").toF) + 0 = t2.eval (realToR (env "x").toF) := by
          mach_ring
        have e : t2.eval (realToR (env "x").toF) + 0
              ≤ t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF) :=
          add_le_add_left hE2nn _
        rw [e2] at e; exact e
      -- direct (non-exactRn) bounds on t1.eval x / t2.eval x themselves, for absenc_lip_local
      have h1eval_lo : t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF)
          ≤ t1.eval (realToR (env "x").toF) := by
        have e : t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF)
              ≤ t1.eval (realToR (env "x").toF) - 0 :=
          sub_le_sub_left hE1nn (t1.eval (realToR (env "x").toF))
        have e2 : t1.eval (realToR (env "x").toF) - 0 = t1.eval (realToR (env "x").toF) := by
          mach_ring
        rw [e2] at e; exact e
      have h1eval_hi : t1.eval (realToR (env "x").toF)
          ≤ t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF) := by
        have e2 : t1.eval (realToR (env "x").toF) + 0 = t1.eval (realToR (env "x").toF) := by
          mach_ring
        have e : t1.eval (realToR (env "x").toF) + 0
              ≤ t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF) :=
          add_le_add_left hE1nn _
        rw [e2] at e; exact e
      have h2eval_lo : t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
          ≤ t2.eval (realToR (env "x").toF) := by
        have e : t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
              ≤ t2.eval (realToR (env "x").toF) - 0 :=
          sub_le_sub_left hE2nn (t2.eval (realToR (env "x").toF))
        have e2 : t2.eval (realToR (env "x").toF) - 0 = t2.eval (realToR (env "x").toF) := by
          mach_ring
        rw [e2] at e; exact e
      have h2eval_hi : t2.eval (realToR (env "x").toF)
          ≤ t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF) := by
        have e2 : t2.eval (realToR (env "x").toF) + 0 = t2.eval (realToR (env "x").toF) := by
          mach_ring
        have e : t2.eval (realToR (env "x").toF) + 0
              ≤ t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF) :=
          add_le_add_left hE2nn _
        rw [e2] at e; exact e
      -- the exp node
      have hfoldexp : IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
          (.tr1 .exp (toCertcomEML t1)) :=
        IsFoldLocal.tr1 .exp (toCertcomEML t1)
          (exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF)))
          (t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF))
          (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
          (u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF)))
          (le_of_lt (exp_pos _)) (exp_lip_local _ _)
          h1lo h1hi h1xe_lo h1xe_hi (real_exp_rounds _ _ h1hi) hfold1
      have hEexp : AbsEnc
          (u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
            + exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
              * emlTreeErrorBound t1 (realToR (env "x").toF))
          (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (.tr1 .exp (toCertcomEML t1))).toF)
          (exp (t1.eval (realToR (env "x").toF))) := by
        show AbsEnc _ (realToR (stdI1 leanPrims .exp
            (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t1)).toF)) _
        exact absenc_lip_local (le_of_lt (exp_pos _)) (exp_lip_local _ _)
          herr1 h1lo h1hi h1eval_lo h1eval_hi (real_exp_rounds _ _ h1hi)
      -- the ln node
      have hfoldlog : IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
          (.tr1 .ln (toCertcomEML t2)) :=
        IsFoldLocal.tr1 .ln (toCertcomEML t2)
          (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
          (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF))
          (t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF))
          (u * (abs (log (t2.eval (realToR (env "x").toF)
                - emlTreeErrorBound t2 (realToR (env "x").toF)))
              + abs (log (t2.eval (realToR (env "x").toF)
                + emlTreeErrorBound t2 (realToR (env "x").toF)))))
          (le_of_lt (one_div_pos_of_pos hlo2pos)) (log_lip_local _ _ hlo2pos)
          h2lo h2hi h2xe_lo h2xe_hi (real_log_rounds _ _ _ hlo2pos h2lo h2hi) hfold2
      have hEln : AbsEnc
          (u * (abs (log (t2.eval (realToR (env "x").toF)
                - emlTreeErrorBound t2 (realToR (env "x").toF)))
              + abs (log (t2.eval (realToR (env "x").toF)
                + emlTreeErrorBound t2 (realToR (env "x").toF))))
            + (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
              * emlTreeErrorBound t2 (realToR (env "x").toF))
          (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (.tr1 .ln (toCertcomEML t2))).toF)
          (log (t2.eval (realToR (env "x").toF))) := by
        show AbsEnc _ (realToR (stdI1 leanPrims .ln
            (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t2)).toF)) _
        exact absenc_lip_local (le_of_lt (one_div_pos_of_pos hlo2pos)) (log_lip_local _ _ hlo2pos)
          herr2 h2lo h2hi h2eval_lo h2eval_hi (real_log_rounds _ _ _ hlo2pos h2lo h2hi)
      -- combine
      have hfoldsub : IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
          (.bin .sub (.tr1 .exp (toCertcomEML t1)) (.tr1 .ln (toCertcomEML t2))) :=
        IsFoldLocal.sub _ _ hfoldexp hfoldlog
      have hsub : RoundsW u
          (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (.bin .sub (.tr1 .exp (toCertcomEML t1)) (.tr1 .ln (toCertcomEML t2)))).toF)
          (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
              (.tr1 .exp (toCertcomEML t1))).toF
            - realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
              (.tr1 .ln (toCertcomEML t2))).toF) := by
        show RoundsW u
            (realToR ((evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
                  (.tr1 .exp (toCertcomEML t1))).toF
                - (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
                  (.tr1 .ln (toCertcomEML t2))).toF))
            (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
                (.tr1 .exp (toCertcomEML t1))).toF
              - realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
                (.tr1 .ln (toCertcomEML t2))).toF)
        exact real_fpbridge.sub _ _
      have hcombined := absenc_sub hEexp hEln hsub
      -- loosen: exp(t1.eval x) → exp hi1, abs(log(t2.eval x)) → abs(log lo2)+abs(log hi2)
      have hexpabs : abs (exp (t1.eval (realToR (env "x").toF))) = exp (t1.eval (realToR (env "x").toF)) :=
        abs_of_nonneg (le_of_lt (exp_pos _))
      have hexple : exp (t1.eval (realToR (env "x").toF))
          ≤ exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF)) :=
        exp_monotone h1eval_hi
      have hneg_abs_le : ∀ y : Real, -(abs y) ≤ y := by
        intro y
        have h1 : -y ≤ abs (-y) := le_abs_self (-y)
        rw [abs_neg] at h1
        have h2 := neg_le_neg h1
        have e : -(-y) = y := by mach_ring
        rw [e] at h2
        exact h2
      have ht2pos : (0:Real) < t2.eval (realToR (env "x").toF) := by
        have e : t2.eval (realToR (env "x").toF)
            = t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
              + emlTreeErrorBound t2 (realToR (env "x").toF) := by mach_ring
        rw [e]; exact lt_of_lt_of_le hlo2pos (le_add_of_nonneg_right hE2nn)
      have hlogabsle : abs (log (t2.eval (realToR (env "x").toF)))
          ≤ abs (log (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
            + abs (log (t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF))) := by
        apply abs_le_iff.mpr
        refine ⟨?_, ?_⟩
        · have h1 : log (t2.eval (realToR (env "x").toF)
                - emlTreeErrorBound t2 (realToR (env "x").toF)) ≤ log (t2.eval (realToR (env "x").toF)) :=
            log_le_log hlo2pos h2eval_lo
          have h2 := hneg_abs_le (log (t2.eval (realToR (env "x").toF)
              - emlTreeErrorBound t2 (realToR (env "x").toF)))
          have h3 := abs_nonneg (log (t2.eval (realToR (env "x").toF)
              + emlTreeErrorBound t2 (realToR (env "x").toF)))
          have h4 : -(abs (log (t2.eval (realToR (env "x").toF)
                  - emlTreeErrorBound t2 (realToR (env "x").toF)))
                + abs (log (t2.eval (realToR (env "x").toF)
                  + emlTreeErrorBound t2 (realToR (env "x").toF))))
              ≤ log (t2.eval (realToR (env "x").toF)
                - emlTreeErrorBound t2 (realToR (env "x").toF)) := by
            have e : -(abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  + abs (log (t2.eval (realToR (env "x").toF)
                    + emlTreeErrorBound t2 (realToR (env "x").toF))))
                ≤ -(abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))) := by
              have e2 : -(abs (log (t2.eval (realToR (env "x").toF)
                      - emlTreeErrorBound t2 (realToR (env "x").toF)))
                    + abs (log (t2.eval (realToR (env "x").toF)
                      + emlTreeErrorBound t2 (realToR (env "x").toF))))
                  = -(abs (log (t2.eval (realToR (env "x").toF)
                      - emlTreeErrorBound t2 (realToR (env "x").toF))))
                    - abs (log (t2.eval (realToR (env "x").toF)
                      + emlTreeErrorBound t2 (realToR (env "x").toF))) := by mach_ring
              rw [e2]; exact sub_le_self h3
            exact le_trans e h2
          exact le_trans h4 h1
        · have h1 : log (t2.eval (realToR (env "x").toF))
              ≤ log (t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF)) :=
            log_le_log ht2pos h2eval_hi
          have h2 := le_abs_self (log (t2.eval (realToR (env "x").toF)
              + emlTreeErrorBound t2 (realToR (env "x").toF)))
          have h3 := abs_nonneg (log (t2.eval (realToR (env "x").toF)
              - emlTreeErrorBound t2 (realToR (env "x").toF)))
          have h4 : abs (log (t2.eval (realToR (env "x").toF)
                + emlTreeErrorBound t2 (realToR (env "x").toF)))
              ≤ abs (log (t2.eval (realToR (env "x").toF)
                  - emlTreeErrorBound t2 (realToR (env "x").toF)))
                + abs (log (t2.eval (realToR (env "x").toF)
                  + emlTreeErrorBound t2 (realToR (env "x").toF))) :=
            le_add_of_nonneg_left h3
          exact le_trans h1 (le_trans h2 h4)
      have hloosen : u * ((abs (exp (t1.eval (realToR (env "x").toF)))
              + (u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                + exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                  * emlTreeErrorBound t1 (realToR (env "x").toF)))
            + (abs (log (t2.eval (realToR (env "x").toF)))
              + (u * (abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  + abs (log (t2.eval (realToR (env "x").toF)
                    + emlTreeErrorBound t2 (realToR (env "x").toF))))
                + (1 / (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  * emlTreeErrorBound t2 (realToR (env "x").toF))))
          + ((u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                + exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                  * emlTreeErrorBound t1 (realToR (env "x").toF))
            + (u * (abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  + abs (log (t2.eval (realToR (env "x").toF)
                    + emlTreeErrorBound t2 (realToR (env "x").toF))))
              + (1 / (t2.eval (realToR (env "x").toF)
                  - emlTreeErrorBound t2 (realToR (env "x").toF)))
                * emlTreeErrorBound t2 (realToR (env "x").toF)))
        ≤ emlTreeErrorBound (t1.eml t2) (realToR (env "x").toF) := by
        show _ ≤ u * ((exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
              + (u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                + exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                  * emlTreeErrorBound t1 (realToR (env "x").toF)))
            + ((abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  + abs (log (t2.eval (realToR (env "x").toF)
                    + emlTreeErrorBound t2 (realToR (env "x").toF))))
              + (u * (abs (log (t2.eval (realToR (env "x").toF)
                      - emlTreeErrorBound t2 (realToR (env "x").toF)))
                    + abs (log (t2.eval (realToR (env "x").toF)
                      + emlTreeErrorBound t2 (realToR (env "x").toF))))
                + (1 / (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  * emlTreeErrorBound t2 (realToR (env "x").toF))))
          + ((u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                + exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                  * emlTreeErrorBound t1 (realToR (env "x").toF))
            + (u * (abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  + abs (log (t2.eval (realToR (env "x").toF)
                    + emlTreeErrorBound t2 (realToR (env "x").toF))))
              + (1 / (t2.eval (realToR (env "x").toF)
                  - emlTreeErrorBound t2 (realToR (env "x").toF)))
                * emlTreeErrorBound t2 (realToR (env "x").toF)))
        rw [hexpabs]
        exact add_le_add
          (mul_le_mul_of_nonneg_left
            (add_le_add (add_le_add hexple (le_refl _)) (add_le_add hlogabsle (le_refl _)))
            u_nonneg)
          (le_refl _)
      refine ⟨hfoldsub, ?_, le_trans hcombined hloosen⟩
      rw [show toCertcomEML (t1.eml t2)
            = .bin .sub (.tr1 .exp (toCertcomEML t1)) (.tr1 .ln (toCertcomEML t2)) from rfl]
      show exactRn realToR realOfEML env (.tr1 .exp (toCertcomEML t1))
          - exactRn realToR realOfEML env (.tr1 .ln (toCertcomEML t2))
        = exp (t1.eval (realToR (env "x").toF)) - log (t2.eval (realToR (env "x").toF))
      show realOfEML .exp (exactRn realToR realOfEML env (toCertcomEML t1))
          - realOfEML .ln (exactRn realToR realOfEML env (toCertcomEML t2))
        = exp (t1.eval (realToR (env "x").toF)) - log (t2.eval (realToR (env "x").toF))
      rw [hexact1, hexact2]
      rfl

/-- **Non-vacuity: genuine depth-2 nesting, not just the one hand-built tree.**
`eml (eml var var) var` — `exp(exp x − log x) − log x` — is a tree
`EMLCertcomGrounded.lean`'s hand-built `eml_var_var_pipeline_uniform_grounded` was never built for
(that file covers ONLY `eml var var`, depth 1). `eml_tree_var_grounded` applies to it directly, no
new proof: this is the "one reusable primitive-grounding lemma, arbitrary trees inherit
automatically" property stated as a working instance, not just a claim. `hv` (validity at depth 2) is
taken as a hypothesis here — same status as every domain/range hypothesis elsewhere in this
codebase (`pid_log_cosh_grounded`'s `hlo`, `EMLPfaffianValidOn`, …); discharging it CONCRETELY would
need a numeric value for `u`, which this codebase deliberately never fixes (every `real_X_rounds`
bound stays symbolic in `u`, not instantiated). -/
theorem eml_tree_var_grounded_depth2_instance (env : Env)
    (hv : EMLTreeVarValid (realToR (env "x").toF)
      (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)) :
    IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
        (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)) ∧
      exactRn realToR realOfEML env
          (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var))
        = (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var).eval
          (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var))).toF
          - (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var).eval
            (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)
          (realToR (env "x").toF) :=
  eml_tree_var_grounded env _ hv

end Certcom
