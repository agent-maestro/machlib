import MachLib.EMLCertcomGrounded

/-!
# The compositional Certcom handshake: any `EMLTree`, one reusable lemma

`EMLCertcomGrounded.lean` grounded exactly ONE tree, `EMLTree.eml EMLTree.var EMLTree.var`, by hand.
This file generalizes that construction to ANY `EMLTree` — `const`, `var`, and `eml`, arbitrary depth,
arbitrary shape — the "Groundable" pipeline: one recursive translation, one recursive validity
predicate, one recursive error-bound function, and one theorem proved by structural induction that
every such tree inherits automatically.

**`const` closes the last gap this file's own earlier version deferred.** `EMLTree.const c` translates
via `floatOfR c` (the disclosed Real→Float quantization axiom, `EMLCertcomGrounded.lean`), and —
unlike a bare `.var` read, which carries zero error — every `const` LEAF now carries its own
quantization error (`real_round_bounds`). The key structural fact that makes this tractable: the SAME
`emlTreeErrorBound` recursion built for `var`+`eml` trees already upper-bounds BOTH the compiled-vs-
exact error AND the exact-vs-true error (it's built from Lipschitz composition plus extra non-negative
rounding terms on top), so no SECOND recursive function is needed — only the theorem's own conjunct
shape changes: `exactRn t = t.eval x` (an exact equality, true only when no constant ever entered the
recursion) becomes `abs (exactRn t − t.eval x) ≤ emlTreeErrorBound t x` (an inequality, using the same
bound function), and the `.const` leaf becomes a genuine new base case rather than an unreachable one.
-/

namespace Certcom

open MachLib MachLib.Real

/-- Real semantics for Option D's `EMLTree`, read through Certcom's own `Trans1`: `.exp ↦ exp`,
`.ln ↦ log` (the only two primitives an `EMLTree` translation ever produces). -/
noncomputable def realOfEML : Trans1 → MachLib.Real → MachLib.Real
  | .exp => exp | .ln => log | _ => id

/-- Certcom's compiled form of an `EMLTree`, decomposed exactly like `emlVarVar`
(`EMLCertcomBridge.lean`), recursively: `eml t1 t2 ↦ exp(⟦t1⟧) − log(⟦t2⟧)`, `const c ↦ .lit (floatOfR
c)` (the disclosed quantization), `var ↦ .var "x"`. -/
noncomputable def toCertcomEML : EMLTree → EML
  | .const c => .lit (floatOfR c)
  | .var => .var "x"
  | .eml t1 t2 => .bin .sub (.tr1 .exp (toCertcomEML t1)) (.tr1 .ln (toCertcomEML t2))

/-- **The explicit, recursively-computed forward-error bound** — the "one reusable primitive-
grounding lemma" applied at every node. At a `const c` leaf: `real_round_bounds`'s own quantization
bound, `u · abs c` (tight — `M := abs c`). At `var`: zero (no rounding at a bare read). At `eml t1 t2`:
`t1`'s bound `E1` gives a magnitude envelope `[xe1 − E1, xe1 + E1]` for `exp`'s Lipschitz domain
(`hi1 := xe1 + E1`, matching `real_exp_rounds`' own shape); `t2`'s bound `E2` gives `[xe2 − E2, xe2 +
E2]` for `log`'s. The formula is `absenc_lip_local` (Lipschitz-amplify + primitive round) composed
twice, then `absenc_sub`'s cross term — the same shape `EMLCertcomGrounded.lean`'s
`eml_var_var_pipeline_uniform_grounded` derives by hand for one fixed tree, here produced
automatically for any tree — UNCHANGED from this file's `var`+`eml`-only version, since it's already
generic in `E1`/`E2` regardless of where they came from. -/
noncomputable def emlTreeErrorBound : EMLTree → Real → Real
  | .const c, _ => u * abs c
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

/-- **Pointwise validity for any `EMLTree`**: at every `eml` node, the log argument's own error
envelope must stay strictly inside the positive reals — `emlTreeErrorBound t2 x < t2.eval x` — the
pointwise analogue of `EMLPfaffianValidOn`'s interval-wide positivity condition, sharpened to also
cover the compiled artifact's own rounding slop, not just the exact value's sign. `const`/`var` leaves
are trivially valid — no domain condition to check. -/
inductive EMLTreeValid (x : Real) : EMLTree → Prop
  | const (c : Real) : EMLTreeValid x (.const c)
  | var : EMLTreeValid x .var
  | eml (t1 t2 : EMLTree) (hmargin : emlTreeErrorBound t2 x < t2.eval x) :
      EMLTreeValid x t1 → EMLTreeValid x t2 → EMLTreeValid x (.eml t1 t2)

/-- `emlTreeErrorBound` is non-negative, GIVEN validity (the `1/lo2` term needs `lo2 > 0`, which only
holds under `EMLTreeValid`'s positivity margin — not an unconditional fact about the raw formula).
Proved by induction on the validity derivation itself, not on `EMLTree` directly, so `hmargin`/the IH
are available exactly where the `.eml` case's division needs them. -/
theorem emlTreeErrorBound_nonneg {x : Real} : ∀ {t : EMLTree}, EMLTreeValid x t →
    0 ≤ emlTreeErrorBound t x := by
  intro t hv
  induction hv with
  | const c => exact mul_nonneg u_nonneg (abs_nonneg c)
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

/-- **The compositional Certcom handshake — the full grammar.** For ANY `EMLTree` `t`, valid at the
point `x := realToR (env "x").toF` (`EMLTreeValid`): `toCertcomEML t` is in Certcom's own certified
nested-local fold fragment (`IsFoldLocal`), its exact real semantics are within `emlTreeErrorBound t
x` of `t.eval x` (an equality only at the `var` leaf — every `const` anywhere in the tree contributes
its own quantization error, amplified by whatever `exp`/`log` layers sit above it), and its COMPILED
evaluation is within the SAME explicit bound of `t.eval x`. One induction on `EMLTreeValid`, reusing
`absenc_lip_local`/`absenc_sub` directly at the `eml` case for the compiled-error conjunct (not
routed through `pipeline_nested_local`'s own existential, so the bound comes out in
`emlTreeErrorBound`'s EXACT closed form) and a parallel, simpler pure-Lipschitz argument (no
primitive rounding — `exactRn` is a real-valued computation, not a floating one) for the exact-error
conjunct — building `IsFoldLocal` too, alongside, as a reusable witness for anyone who also wants the
emitted-C connection via `pipeline_nested_local`/`emitC_correct`. -/
theorem eml_tree_grounded (env : Env) : ∀ (t : EMLTree),
    EMLTreeValid (realToR (env "x").toF) t →
      IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env (toCertcomEML t) ∧
      abs (exactRn realToR realOfEML env (toCertcomEML t) - t.eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound t (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env (toCertcomEML t)).toF
          - t.eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound t (realToR (env "x").toF) := by
  intro t hv
  induction hv with
  | const c =>
      refine ⟨IsFoldLocal.lit (floatOfR c), ?_, ?_⟩
      · show abs (realToR (floatOfR c) - c) ≤ u * abs c
        exact real_round_bounds (abs c) c (abs_nonneg c) (le_refl (abs c))
      · show abs (realToR (floatOfR c) - c) ≤ u * abs c
        exact real_round_bounds (abs c) c (abs_nonneg c) (le_refl (abs c))
  | var =>
      refine ⟨IsFoldLocal.var "x", ?_, ?_⟩
      · show abs (realToR (env "x").toF - realToR (env "x").toF) ≤ 0
        rw [sub_self]; exact le_of_eq abs_zero
      · show abs (realToR (env "x").toF - realToR (env "x").toF) ≤ 0
        rw [sub_self]; exact le_of_eq abs_zero
  | eml t1 t2 hmargin hv1 hv2 ih1 ih2 =>
      obtain ⟨hfold1, herr1_exact, herr1⟩ := ih1
      obtain ⟨hfold2, herr2_exact, herr2⟩ := ih2
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
      -- exact-value bounds, from herr1_exact/herr2_exact (SAME pattern as h1lo/h1hi, not equalities)
      have h1xe_lo : t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF)
          ≤ exactRn realToR realOfEML env (toCertcomEML t1) := by
        have h1 : -(emlTreeErrorBound t1 (realToR (env "x").toF))
            ≤ exactRn realToR realOfEML env (toCertcomEML t1) - t1.eval (realToR (env "x").toF) :=
          (abs_le_iff.mp herr1_exact).1
        have e4 : t1.eval (realToR (env "x").toF)
            + (exactRn realToR realOfEML env (toCertcomEML t1) - t1.eval (realToR (env "x").toF))
            = exactRn realToR realOfEML env (toCertcomEML t1) := by mach_ring
        have e3 : t1.eval (realToR (env "x").toF) + -(emlTreeErrorBound t1 (realToR (env "x").toF))
            = t1.eval (realToR (env "x").toF) - emlTreeErrorBound t1 (realToR (env "x").toF) := by
          mach_ring
        have h2' := add_le_add_left h1 (t1.eval (realToR (env "x").toF))
        rw [e3, e4] at h2'; exact h2'
      have h1xe_hi : exactRn realToR realOfEML env (toCertcomEML t1)
          ≤ t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF) := by
        have h1 : exactRn realToR realOfEML env (toCertcomEML t1) - t1.eval (realToR (env "x").toF)
              ≤ emlTreeErrorBound t1 (realToR (env "x").toF) := (abs_le_iff.mp herr1_exact).2
        have e4 : t1.eval (realToR (env "x").toF)
            + (exactRn realToR realOfEML env (toCertcomEML t1) - t1.eval (realToR (env "x").toF))
            = exactRn realToR realOfEML env (toCertcomEML t1) := by mach_ring
        have h2' := add_le_add_left h1 (t1.eval (realToR (env "x").toF))
        rw [e4] at h2'; exact h2'
      have h2xe_lo : t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)
          ≤ exactRn realToR realOfEML env (toCertcomEML t2) := by
        have h1 : -(emlTreeErrorBound t2 (realToR (env "x").toF))
            ≤ exactRn realToR realOfEML env (toCertcomEML t2) - t2.eval (realToR (env "x").toF) :=
          (abs_le_iff.mp herr2_exact).1
        have e4 : t2.eval (realToR (env "x").toF)
            + (exactRn realToR realOfEML env (toCertcomEML t2) - t2.eval (realToR (env "x").toF))
            = exactRn realToR realOfEML env (toCertcomEML t2) := by mach_ring
        have e3 : t2.eval (realToR (env "x").toF) + -(emlTreeErrorBound t2 (realToR (env "x").toF))
            = t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF) := by
          mach_ring
        have h2' := add_le_add_left h1 (t2.eval (realToR (env "x").toF))
        rw [e3, e4] at h2'; exact h2'
      have h2xe_hi : exactRn realToR realOfEML env (toCertcomEML t2)
          ≤ t2.eval (realToR (env "x").toF) + emlTreeErrorBound t2 (realToR (env "x").toF) := by
        have h1 : exactRn realToR realOfEML env (toCertcomEML t2) - t2.eval (realToR (env "x").toF)
              ≤ emlTreeErrorBound t2 (realToR (env "x").toF) := (abs_le_iff.mp herr2_exact).2
        have e4 : t2.eval (realToR (env "x").toF)
            + (exactRn realToR realOfEML env (toCertcomEML t2) - t2.eval (realToR (env "x").toF))
            = exactRn realToR realOfEML env (toCertcomEML t2) := by mach_ring
        have h2' := add_le_add_left h1 (t2.eval (realToR (env "x").toF))
        rw [e4] at h2'; exact h2'
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
      -- exact-error conjunct: pure Lipschitz composition, no primitive rounding
      have hexact_tri : abs (exactRn realToR realOfEML env (toCertcomEML (t1.eml t2))
            - (t1.eml t2).eval (realToR (env "x").toF))
          ≤ exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
              * emlTreeErrorBound t1 (realToR (env "x").toF)
            + (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
              * emlTreeErrorBound t2 (realToR (env "x").toF) := by
        have heq : exactRn realToR realOfEML env (toCertcomEML (t1.eml t2))
              - (t1.eml t2).eval (realToR (env "x").toF)
            = (exp (exactRn realToR realOfEML env (toCertcomEML t1))
                - exp (t1.eval (realToR (env "x").toF)))
              - (log (exactRn realToR realOfEML env (toCertcomEML t2))
                - log (t2.eval (realToR (env "x").toF))) := by
          show exp (exactRn realToR realOfEML env (toCertcomEML t1))
                - log (exactRn realToR realOfEML env (toCertcomEML t2))
              - (exp (t1.eval (realToR (env "x").toF)) - log (t2.eval (realToR (env "x").toF)))
            = (exp (exactRn realToR realOfEML env (toCertcomEML t1))
                - exp (t1.eval (realToR (env "x").toF)))
              - (log (exactRn realToR realOfEML env (toCertcomEML t2))
                - log (t2.eval (realToR (env "x").toF)))
          mach_ring
        rw [heq]
        have hexplip : abs (exp (exactRn realToR realOfEML env (toCertcomEML t1))
              - exp (t1.eval (realToR (env "x").toF)))
            ≤ exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
              * abs (exactRn realToR realOfEML env (toCertcomEML t1)
                - t1.eval (realToR (env "x").toF)) :=
          exp_lip_local _ _ _ _ h1xe_lo h1xe_hi h1eval_lo h1eval_hi
        have hloglip : abs (log (exactRn realToR realOfEML env (toCertcomEML t2))
              - log (t2.eval (realToR (env "x").toF)))
            ≤ (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
              * abs (exactRn realToR realOfEML env (toCertcomEML t2)
                - t2.eval (realToR (env "x").toF)) :=
          log_lip_local _ _ hlo2pos _ _ h2xe_lo h2xe_hi h2eval_lo h2eval_hi
        refine le_trans (abs_sub_le' _ _) (add_le_add ?_ ?_)
        · exact le_trans hexplip
            (mul_le_mul_of_nonneg_left herr1_exact
              (le_of_lt (exp_pos _)))
        · exact le_trans hloglip
            (mul_le_mul_of_nonneg_left herr2_exact
              (le_of_lt (one_div_pos_of_pos hlo2pos)))
      have hexact_loosen : exp (t1.eval (realToR (env "x").toF)
              + emlTreeErrorBound t1 (realToR (env "x").toF))
            * emlTreeErrorBound t1 (realToR (env "x").toF)
          + (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
            * emlTreeErrorBound t2 (realToR (env "x").toF)
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
        have hbig : (0:Real) ≤ u * ((exp (t1.eval (realToR (env "x").toF)
                + emlTreeErrorBound t1 (realToR (env "x").toF))
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
                  * emlTreeErrorBound t2 (realToR (env "x").toF)))) :=
          mul_nonneg u_nonneg
            (add_nonneg (add_nonneg (le_of_lt (exp_pos _))
                (add_nonneg (mul_nonneg u_nonneg (le_of_lt (exp_pos _)))
                  (mul_nonneg (le_of_lt (exp_pos _)) hE1nn)))
              (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
                (add_nonneg (mul_nonneg u_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)))
                  (mul_nonneg (le_of_lt (one_div_pos_of_pos hlo2pos)) hE2nn))))
        have hEx' : exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
              * emlTreeErrorBound t1 (realToR (env "x").toF)
            ≤ u * exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
              + exp (t1.eval (realToR (env "x").toF) + emlTreeErrorBound t1 (realToR (env "x").toF))
                * emlTreeErrorBound t1 (realToR (env "x").toF) :=
          le_add_of_nonneg_left (mul_nonneg u_nonneg (le_of_lt (exp_pos _)))
        have hEy' : (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
              * emlTreeErrorBound t2 (realToR (env "x").toF)
            ≤ u * (abs (log (t2.eval (realToR (env "x").toF)
                    - emlTreeErrorBound t2 (realToR (env "x").toF)))
                  + abs (log (t2.eval (realToR (env "x").toF)
                    + emlTreeErrorBound t2 (realToR (env "x").toF))))
              + (1 / (t2.eval (realToR (env "x").toF) - emlTreeErrorBound t2 (realToR (env "x").toF)))
                * emlTreeErrorBound t2 (realToR (env "x").toF) :=
          le_add_of_nonneg_left
            (mul_nonneg u_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)))
        exact le_trans (add_le_add hEx' hEy') (le_add_of_nonneg_left hbig)
      refine ⟨hfoldsub, le_trans hexact_tri hexact_loosen, le_trans hcombined hloosen⟩

/-- **Non-vacuity: genuine depth-2 nesting, not just the one hand-built tree.**
`eml (eml var var) var` — `exp(exp x − log x) − log x` — is a tree
`EMLCertcomGrounded.lean`'s hand-built `eml_var_var_pipeline_uniform_grounded` was never built for
(that file covers ONLY `eml var var`, depth 1). `eml_tree_grounded` applies to it directly, no new
proof: this is the "one reusable primitive-grounding lemma, arbitrary trees inherit automatically"
property stated as a working instance, not just a claim. `hv` (validity at depth 2) is taken as a
hypothesis here — same status as every domain/range hypothesis elsewhere in this codebase
(`pid_log_cosh_grounded`'s `hlo`, `EMLPfaffianValidOn`, …); discharging it CONCRETELY would need a
numeric value for `u`, which this codebase deliberately never fixes. -/
theorem eml_tree_grounded_depth2_instance (env : Env)
    (hv : EMLTreeValid (realToR (env "x").toF)
      (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)) :
    IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
        (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)) ∧
      abs (exactRn realToR realOfEML env
            (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var))
          - (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var).eval
            (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)
          (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var))).toF
          - (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var).eval
            (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var)
          (realToR (env "x").toF) :=
  eml_tree_grounded env _ hv

/-- **Non-vacuity: a genuine `const` node, the whole point of this round.**
`eml (const 1) var` — `exp(1) − log(x)` — the SAME kernel `eml_var_var_pipeline_uniform_grounded`
(`EMLCertcomGrounded.lean`) covers, but reached here as an ordinary instance of the fully general
theorem instead of a bespoke construction, confirming `const` genuinely composes through the same
machinery as `var`/`eml`. -/
theorem eml_tree_grounded_const_instance (env : Env) (c : Real)
    (hv : EMLTreeValid (realToR (env "x").toF) (EMLTree.eml (EMLTree.const c) EMLTree.var)) :
    IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
        (toCertcomEML (EMLTree.eml (EMLTree.const c) EMLTree.var)) ∧
      abs (exactRn realToR realOfEML env (toCertcomEML (EMLTree.eml (EMLTree.const c) EMLTree.var))
          - (EMLTree.eml (EMLTree.const c) EMLTree.var).eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.const c) EMLTree.var) (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (toCertcomEML (EMLTree.eml (EMLTree.const c) EMLTree.var))).toF
          - (EMLTree.eml (EMLTree.const c) EMLTree.var).eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.const c) EMLTree.var) (realToR (env "x").toF) :=
  eml_tree_grounded env _ hv

end Certcom
