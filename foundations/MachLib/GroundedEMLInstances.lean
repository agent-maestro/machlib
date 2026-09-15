import MachLib.GroundedPIDInstances

/-!
# `eml_tree_grounded` at `eml` nodes, and the `eml_var_var` family, instantiated

`eml_tree_grounded` (`EMLTreeGroundedPipeline.lean`) takes `EMLTreeFloatSafe`, whose `eml` constructor asks that the float
fed to `exp` be finite, that `exp`'s float result be finite with its exact result at least `DBL_MIN`, and that the float
difference `exp(…) − log(…)` be finite. `eml_var_var_pipeline_uniform_grounded` and
`eml_var_var_quantized_pointwise_grounded` (`EMLCertcomGrounded.lean`) take the same facts as separate hypotheses. Until
2026-09-14 nothing concluded that a runtime `exp` or `log` result was finite. `real_exp_finite` and `real_log_finite`
(`FPGrounding.lean`, owner-approved, measured) now do, `real_fpfinite` turns a bound on both into the difference's
finiteness, and `u_le_half` keeps a quantized input inside a stated range.

The difference needs an upper bound on `exp` that no trusted axiom states. `GroundedInstanceArith.lean` derives a crude
one, `exp n ≤ 4ⁿ`, from `1 + x ≤ exp x`; it is the reason the domains below stop at `500`.

## Instantiated, on these domains

  * `eml_tree_grounded` at `eml var var` (`exp x − log x`): the input `x` is a finite float with `0.5 ≤ realToR x ≤ 500`.
  * `eml_tree_grounded` at the depth-2 tree `eml (eml var var) var` (`exp(exp x − log x) − log x`): `0.5 ≤ realToR x ≤ 2`.
  * `eml_tree_grounded` at `eml (const 1) var` (`exp 1 − log x`, a constant quantized by `floatOfR`): `0.5 ≤ realToR x ≤ 500`.
  * `eml_var_var_pipeline_uniform_grounded`: `x` a finite float in `[A, B]` with `1 ≤ A` and `B ≤ 500`.
  * `eml_var_var_quantized_pointwise_grounded`: a real `x` in `(A, B)` with `0 ≤ B ≤ 200` and `2 + B ≤ 2A` (so `A − u·B ≥ 1`).

Each has a specimen at a concrete input: `floatOfR 2.0`, `floatOfR 1.0`, or, for the quantized form, `x = 3.5` in
`(3.0, 4.0)`.

## Not instantiated: `eml_var_var_certcom_witness_grounded`

Its `hδε` asks the explicit error `δ = u·((exp (B + u·B) + …) …) + (exp (B + u·B) + 1/(A − u·B))·(u·B)` to be below
`ε < 1`. With `u` known only to be at most `1/2`, `δ` is at least `u·exp (B + u·B)`, which no bound on `u` short of a
numeric one keeps below `1`; its `hMB` and `hA0 : A < ext 0` (`ext 0 = π/2`) constrain `A` and `B` further. It needs a
numeric bound on `u` (such as `u ≤ 2⁻⁵⁰`) on top of what was approved.
-/

namespace Certcom

open MachLib MachLib.Real

/-! ## 1. `exp a − log b`: finite, and how large -/

theorem two_pos_real : (0 : MachLib.Real) < 1 + 1 :=
  lt_of_lt_of_le zero_lt_one_ax (le_add_of_nonneg_right (le_of_lt zero_lt_one_ax))

/-- `0.5 ≤ y` from `1 ≤ y`. -/
theorem point_five_le_of_one_le {y : MachLib.Real} (h : 1 ≤ y) : (0.5 : MachLib.Real) ≤ y :=
  le_trans (le_trans (by grounded_decimal : (0.5 : MachLib.Real) ≤ 1.0) (le_of_eq realOfScientific_one_dot_zero)) h

/-- `|log y| ≤ M` for `0.5 ≤ y ≤ M` and `M ≥ 1`: `log y ≤ y − 1`, and `log y ≥ −1` because `exp (−1) ≤ 0.5`
(`exp 1 ≥ 2`, from `1 + x ≤ exp x`). -/
theorem abs_log_le_of_half_le {y : MachLib.Real} {M : Nat} (h : 0.5 ≤ y) (hy : y ≤ natCast M) (hM : 1 ≤ M) :
    abs (log y) ≤ natCast M := by
  have hy0 : 0 < y := lt_of_lt_of_le (realOfScientific_pos 5 true 1 (by decide)) h
  apply abs_le_iff.mpr
  refine ⟨?_, le_trans (log_le_sub_one hy0) (le_trans (sub_le_self (le_of_lt zero_lt_one_ax)) hy)⟩
  have hexp1 : (1 : MachLib.Real) + 1 ≤ exp 1 := one_add_le_exp 1
  have hinv : exp (-1) * exp 1 = 1 := by rw [mul_comm]; exact HyperbolicPreservation.exp_mul_exp_neg 1
  have he : exp (-1) ≤ 0.5 := by
    apply le_of_mul_le_mul_right_pos _ two_pos_real
    have h1 : exp (-1) * (1 + 1) ≤ exp (-1) * exp 1 := mul_le_mul_of_nonneg_left hexp1 (le_of_lt (exp_pos _))
    rw [hinv] at h1
    have e : (0.5 : MachLib.Real) * (1 + 1) = 1 := by
      rw [show (0.5 : MachLib.Real) * (1 + 1) = 0.5 + 0.5 from by mach_ring]; mach_decimal_ofnat
    rw [e]; exact h1
  have hl : log (exp (-1)) ≤ log y := log_le_log (exp_pos _) (le_trans he h)
  rw [log_exp] at hl
  exact le_trans (neg_le_neg (one_le_natCast_of hM)) hl

/-- **The runtime `exp a − log b`.** For finite floats with `|realToR a| ≤ N ≤ 500` and `0.5 ≤ realToR b ≤ M`, `M ≥ 1`, and
`2·(2·4ᴺ + 2·M) ≤ DBL_MAX`: `exp a` is finite (`real_exp_finite`) with `DBL_MIN ≤ exp (realToR a)`, `log b` is finite
(`real_log_finite`), their float difference is finite (`real_fpfinite`), and it is at most `2·(2·4ᴺ + 2·M)` in magnitude. -/
theorem exp_sub_log_facts {a b : Float} {N M : Nat} (hN : N ≤ 500) (hM : 1 ≤ M)
    (hsize : 2 * (2 * 4 ^ N + 2 * M) ≤ (2 ^ 53 - 1) * 2 ^ 971)
    (ha : a.isFinite = true) (haN : abs (realToR a) ≤ natCast N)
    (hb : b.isFinite = true) (hb1 : 0.5 ≤ realToR b) (hbM : realToR b ≤ natCast M) :
    (stdI1 leanPrims .exp a).isFinite = true ∧ dblMin ≤ exp (realToR a) ∧
    (stdI1 leanPrims .ln b).isFinite = true ∧
    (stdI1 leanPrims .exp a - stdI1 leanPrims .ln b).isFinite = true ∧
    abs (realToR (stdI1 leanPrims .exp a - stdI1 leanPrims .ln b)) ≤ natCast (2 * (2 * 4 ^ N + 2 * M)) := by
  obtain ⟨haL, haU⟩ := abs_le_iff.mp haN
  have hN500 : (natCast N : MachLib.Real) ≤ natCast 500 := natCast_le_natCast_of_nat_le hN
  have hexp : (stdI1 leanPrims .exp a).isFinite = true :=
    real_exp_finite a ha (le_trans haU (le_trans hN500 (natCast_le_natCast_of_nat_le (by decide))))
  have hnorm : dblMin ≤ exp (realToR a) := le_trans (dblMin_le_exp_neg hN500) (exp_monotone haL)
  have hb0 : 0 < realToR b := lt_of_lt_of_le (realOfScientific_pos 5 true 1 (by decide)) hb1
  have hlog : (stdI1 leanPrims .ln b).isFinite = true := real_log_finite b hb hb0
  have hE := real_exp_rounds (realToR a) a ha hexp hnorm (le_refl _)
  have hL := real_log_rounds (realToR b) (realToR b) b hb0 (le_refl _) (le_refl _)
  have hre : abs (realToR (stdI1 leanPrims .exp a)) ≤ natCast (2 * 4 ^ N) := by
    have h1 := abs_le_add_err hE
    rw [abs_of_nonneg (le_of_lt (exp_pos _))] at h1
    have h2 : (u + u) * exp (realToR a) ≤ exp (realToR a) := by
      have h3 := mul_le_mul_of_nonneg_right u_le_half (le_of_lt (exp_pos (realToR a)))
      rw [one_mul_thm] at h3; exact h3
    have h4 : exp (realToR a) + exp (realToR a) ≤ natCast (4 ^ N) + natCast (4 ^ N) :=
      add_le_add (exp_le_natCast_pow haU) (exp_le_natCast_pow haU)
    rw [← natCast_add] at h4
    have e : 2 * 4 ^ N = 4 ^ N + 4 ^ N := by omega
    rw [e]
    exact le_trans h1 (le_trans (add_le_add (le_refl _) h2) h4)
  have hrl : abs (realToR (stdI1 leanPrims .ln b)) ≤ natCast (2 * M) := by
    have hLog : abs (log (realToR b)) ≤ natCast M := abs_log_le_of_half_le hb1 hbM hM
    have h1 := abs_le_add_err hL
    have h2 : u * (abs (log (realToR b)) + abs (log (realToR b))) ≤ abs (log (realToR b)) := by
      have e : u * (abs (log (realToR b)) + abs (log (realToR b))) = (u + u) * abs (log (realToR b)) := by mach_ring
      rw [e]
      have h3 := mul_le_mul_of_nonneg_right u_le_half (abs_nonneg (log (realToR b)))
      rw [one_mul_thm] at h3; exact h3
    have h4 : abs (log (realToR b)) + abs (log (realToR b)) ≤ natCast M + natCast M := add_le_add hLog hLog
    rw [← natCast_add] at h4
    have e2 : 2 * M = M + M := by omega
    rw [e2]
    exact le_trans h1 (le_trans (add_le_add (le_refl _) h2) h4)
  have hdiff : abs (realToR (stdI1 leanPrims .exp a) - realToR (stdI1 leanPrims .ln b))
      ≤ natCast (2 * 4 ^ N + 2 * M) := by
    rw [natCast_add]; exact le_trans (abs_sub_le' _ _) (add_le_add hre hrl)
  have hdmax : (natCast (2 * 4 ^ N + 2 * M) : MachLib.Real) ≤ dblMax :=
    natCast_le_natCast_of_nat_le (by omega)
  have hsub := real_fpfinite.sub _ _ hexp hlog (le_trans hdiff hdmax)
  have hr := real_fpbridge.sub _ _ hsub
  have hmag : abs (realToR (stdI1 leanPrims .exp a - stdI1 leanPrims .ln b))
      ≤ (1 + 1) * natCast (2 * 4 ^ N + 2 * M) :=
    le_trans (abs_le_one_add (roundsW_abs hr))
      (mul_le_mul' one_add_u_nonneg one_add_u_le_two_of_lt_one (abs_nonneg _) hdiff)
  rw [← natCast_two, ← natCast_mul] at hmag
  exact ⟨hexp, hnorm, hlog, hsub, hmag⟩

/-! ## 2. `eml_tree_grounded` at `eml` nodes -/

set_option exponentiation.threshold 1100 in
/-- **`eml_tree_grounded`, instantiated at `eml var var`** (`exp x − log x`), on the domain "the input `x` is a finite
float with `0.5 ≤ realToR x ≤ 500`". -/
theorem eml_tree_grounded_eml_var_var_instantiated (env : Env) (hx : (env "x").toF.isFinite = true)
    (hlo : 0.5 ≤ realToR (env "x").toF) (hhi : realToR (env "x").toF ≤ natCast 500) :
    IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
        (toCertcomEML (EMLTree.eml EMLTree.var EMLTree.var)) ∧
      abs (exactRn realToR realOfEML env (toCertcomEML (EMLTree.eml EMLTree.var EMLTree.var))
          - (EMLTree.eml EMLTree.var EMLTree.var).eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml EMLTree.var EMLTree.var) (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (toCertcomEML (EMLTree.eml EMLTree.var EMLTree.var))).toF
          - (EMLTree.eml EMLTree.var EMLTree.var).eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml EMLTree.var EMLTree.var) (realToR (env "x").toF) := by
  have h0 : 0 < realToR (env "x").toF := lt_of_lt_of_le (realOfScientific_pos 5 true 1 (by decide)) hlo
  have habs : abs (realToR (env "x").toF) ≤ natCast 500 := by rw [abs_of_nonneg (le_of_lt h0)]; exact hhi
  obtain ⟨hexp, hnorm, _, hout, _⟩ :=
    exp_sub_log_facts (N := 500) (M := 500) (by decide) (by decide) (by decide) hx habs hx hlo hhi
  have hv : EMLTreeValid (realToR (env "x").toF) (EMLTree.eml EMLTree.var EMLTree.var) :=
    EMLTreeValid.eml _ _ (by show (0 : MachLib.Real) < realToR (env "x").toF; exact h0) EMLTreeValid.var EMLTreeValid.var
  exact eml_tree_grounded env _ hv (EMLTreeFloatSafe.eml _ _ hx hexp hnorm hout EMLTreeFloatSafe.var EMLTreeFloatSafe.var)

set_option exponentiation.threshold 1100 in
/-- **`eml_tree_grounded`, instantiated at the depth-2 tree `eml (eml var var) var`** (`exp(exp x − log x) − log x`), on
the domain "`x` is a finite float with `0.5 ≤ realToR x ≤ 2`". The inner difference is at most `72` in magnitude
(`exp_sub_log_facts` at `N = M = 2`), which is what the outer `exp` is fed. This is `eml_tree_grounded_depth2_instance`'s
two hypotheses discharged. -/
theorem eml_tree_grounded_depth2_instantiated (env : Env) (hx : (env "x").toF.isFinite = true)
    (hlo : 0.5 ≤ realToR (env "x").toF) (hhi : realToR (env "x").toF ≤ natCast 2) :
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
          (realToR (env "x").toF) := by
  have h0 : 0 < realToR (env "x").toF := lt_of_lt_of_le (realOfScientific_pos 5 true 1 (by decide)) hlo
  have habs : abs (realToR (env "x").toF) ≤ natCast 2 := by rw [abs_of_nonneg (le_of_lt h0)]; exact hhi
  obtain ⟨hexp1, hnorm1, _, hout1, hmag1⟩ :=
    exp_sub_log_facts (N := 2) (M := 2) (by decide) (by decide) (by decide) hx habs hx hlo hhi
  obtain ⟨hexp2, hnorm2, _, hout2, _⟩ :=
    exp_sub_log_facts (N := 2 * (2 * 4 ^ 2 + 2 * 2)) (M := 2) (by decide) (by decide) (by decide) hout1 hmag1
      hx hlo hhi
  have hv1 : EMLTreeValid (realToR (env "x").toF) (EMLTree.eml EMLTree.var EMLTree.var) :=
    EMLTreeValid.eml _ _ (by show (0 : MachLib.Real) < realToR (env "x").toF; exact h0) EMLTreeValid.var EMLTreeValid.var
  have hv : EMLTreeValid (realToR (env "x").toF) (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var) :=
    EMLTreeValid.eml _ _ (by show (0 : MachLib.Real) < realToR (env "x").toF; exact h0) hv1 EMLTreeValid.var
  exact eml_tree_grounded_depth2_instance env hv
    (EMLTreeFloatSafe.eml _ _ hout1 hexp2 hnorm2 hout2
      (EMLTreeFloatSafe.eml _ _ hx hexp1 hnorm1 hout1 EMLTreeFloatSafe.var EMLTreeFloatSafe.var) EMLTreeFloatSafe.var)

set_option exponentiation.threshold 1100 in
/-- **`eml_tree_grounded`, instantiated at `eml (const 1) var`** (`exp 1 − log x`, the constant compiled as `floatOfR 1`),
on the domain "`x` is a finite float with `0.5 ≤ realToR x ≤ 500`". This is `eml_tree_grounded_const_instance`'s two
hypotheses discharged at `c = 1`. -/
theorem eml_tree_grounded_eml_const_one_instantiated (env : Env) (hx : (env "x").toF.isFinite = true)
    (hlo : 0.5 ≤ realToR (env "x").toF) (hhi : realToR (env "x").toF ≤ natCast 500) :
    IsFoldLocal realToR (stdI1 leanPrims) (stdI2 leanPrims) realOfEML env
        (toCertcomEML (EMLTree.eml (EMLTree.const 1) EMLTree.var)) ∧
      abs (exactRn realToR realOfEML env (toCertcomEML (EMLTree.eml (EMLTree.const 1) EMLTree.var))
          - (EMLTree.eml (EMLTree.const 1) EMLTree.var).eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.const 1) EMLTree.var) (realToR (env "x").toF) ∧
      abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) env
            (toCertcomEML (EMLTree.eml (EMLTree.const 1) EMLTree.var))).toF
          - (EMLTree.eml (EMLTree.const 1) EMLTree.var).eval (realToR (env "x").toF))
        ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.const 1) EMLTree.var) (realToR (env "x").toF) := by
  have h0 : 0 < realToR (env "x").toF := lt_of_lt_of_le (realOfScientific_pos 5 true 1 (by decide)) hlo
  have hf1 : (floatOfR 1).isFinite = true := real_round_finite 1 (by rw [abs_one]; exact one_le_dblMax)
  have hone : abs (realToR (floatOfR 1)) ≤ natCast 2 := by
    rw [natCast_two]
    exact le_trans (abs_le_add_err realToR_floatOfR_one_close)
      (by rw [abs_one]; exact one_add_u_le_two_of_lt_one)
  obtain ⟨hexp, hnorm, _, hout, _⟩ :=
    exp_sub_log_facts (N := 2) (M := 500) (by decide) (by decide) (by decide) hf1 hone hx hlo hhi
  have hv : EMLTreeValid (realToR (env "x").toF) (EMLTree.eml (EMLTree.const 1) EMLTree.var) :=
    EMLTreeValid.eml _ _ (by show (0 : MachLib.Real) < realToR (env "x").toF; exact h0)
      (EMLTreeValid.const 1) EMLTreeValid.var
  exact eml_tree_grounded_const_instance env 1 hv
    (EMLTreeFloatSafe.eml _ _ hf1 hexp hnorm hout
      (EMLTreeFloatSafe.const 1 (Or.inr (by rw [abs_one]; exact dblMin_le_one)) (by rw [abs_one]; exact one_le_dblMax))
      EMLTreeFloatSafe.var)

/-! ## 3. The `eml_var_var` family -/

set_option exponentiation.threshold 1100 in
/-- **`eml_var_var_pipeline_uniform_grounded`, instantiated** on the domain "`x` is a finite float in `[A, B]`, with
`1 ≤ A` and `B ≤ 500`". -/
theorem eml_var_var_pipeline_uniform_instantiated (env : Env) (A B : MachLib.Real) (hA1 : 1 ≤ A)
    (hB : B ≤ natCast 500) (hx : (env "x").toF.isFinite = true)
    (hlo : A ≤ realToR (env "x").toF) (hhi : realToR (env "x").toF ≤ B) :
    AbsEnc (u * ((exp B + (u + u) * exp B) + (log B + u * (abs (log A) + abs (log B))))
        + ((u + u) * exp B + u * (abs (log A) + abs (log B))))
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC emlVarVar)).toF)
      (exp (realToR (env "x").toF) - log (realToR (env "x").toF)) := by
  have h1 : 1 ≤ realToR (env "x").toF := le_trans hA1 hlo
  have h0 : 0 < realToR (env "x").toF := lt_of_lt_of_le zero_lt_one_ax h1
  have habs : abs (realToR (env "x").toF) ≤ natCast 500 := by rw [abs_of_nonneg (le_of_lt h0)]; exact le_trans hhi hB
  obtain ⟨hexp, _, _, hout, _⟩ :=
    exp_sub_log_facts (N := 500) (M := 500) (by decide) (by decide) (by decide) hx habs hx
      (point_five_le_of_one_le h1) (le_trans hhi hB)
  have hout' : (evalC (stdR1 leanPrims) (stdR2 leanPrims) env (emitC emlVarVar)).toF.isFinite = true := by
    rw [emitC_correct (stdI1 leanPrims) (stdI2 leanPrims) (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims)
      (std_hrt2 leanPrims) emlVarVar env]
    exact hout
  exact eml_var_var_pipeline_uniform_grounded env A B hA1 hlo hhi hx hexp hout'

set_option exponentiation.threshold 1100 in
/-- **`eml_var_var_quantized_pointwise_grounded`, instantiated** on the domain "a real `x` in `(A, B)`, with `0 ≤ B ≤ 200`
and `2 + B ≤ 2A`". The last condition gives the certificate's `1 ≤ A − u·B` from `u + u ≤ 1`, and `floatOfR x` then reads
back in `[1, 400]`. -/
theorem eml_var_var_quantized_pointwise_instantiated (env : Env) (A B : MachLib.Real) (hB0 : 0 ≤ B)
    (hB200 : B ≤ natCast 200) (hAB : 1 + 1 + B ≤ A + A) (x : Real) (hxA : A < x) (hxB : x < B) :
    abs (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x)
        (emitC emlVarVar)).toF - (EMLTree.eml EMLTree.var EMLTree.var).eval x)
      ≤ u * ((exp (B + u * B) + (u + u) * exp (B + u * B))
            + (log (B + u * B) + u * (abs (log (A - u * B)) + abs (log (B + u * B)))))
          + ((u + u) * exp (B + u * B) + u * (abs (log (A - u * B)) + abs (log (B + u * B))))
        + (exp (B + u * B) + 1 / (A - u * B)) * (u * B) := by
  have huB : u * B + u * B ≤ B := by
    have h := mul_le_mul_of_nonneg_right u_le_half hB0
    rw [one_mul_thm] at h
    have e : (u + u) * B = u * B + u * B := by mach_ring
    rw [e] at h; exact h
  have huB1 : u * B ≤ B := by
    have h := mul_le_mul_of_nonneg_right (le_of_lt u_lt_one) hB0
    rw [one_mul_thm] at h; exact h
  have hAρ : 1 ≤ A - u * B := by
    apply le_of_add_self_le_add_self
    have e : (A - u * B) + (A - u * B) = (A + A) - (u * B + u * B) := by mach_ring
    rw [e]
    have h1 : (A + A) - B ≤ (A + A) - (u * B + u * B) := sub_le_sub_left huB (A + A)
    have h2 : (1 : MachLib.Real) + 1 ≤ (A + A) - B := by
      have h3 := sub_le_sub_right hAB B
      have e2 : 1 + 1 + B - B = (1 : MachLib.Real) + 1 := by mach_ring
      rw [e2] at h3; exact h3
    exact le_trans h2 h1
  have hA1 : 1 ≤ A := le_trans hAρ (sub_le_self (mul_nonneg u_nonneg hB0))
  have hx1 : 1 ≤ x := le_trans hA1 (le_of_lt hxA)
  have hx0 : 0 ≤ x := le_trans (le_of_lt zero_lt_one_ax) hx1
  have hBmax : B ≤ dblMax := le_trans hB200 (natCast_le_natCast_of_nat_le (by decide))
  have hxabs : abs x = x := abs_of_nonneg hx0
  have hxM : abs x ≤ B := by rw [hxabs]; exact le_of_lt hxB
  have hfl : (floatOfR x).isFinite = true := real_round_finite x (le_trans hxM hBmax)
  have hclose : abs (realToR (floatOfR x) - x) ≤ u * B :=
    real_round_bounds B x hB0 hBmax hxM (Or.inr (by rw [hxabs]; exact le_trans dblMin_le_one hx1))
  obtain ⟨hcl, hcu⟩ := abs_le_iff.mp hclose
  have hback : x + (realToR (floatOfR x) - x) = realToR (floatOfR x) := by mach_mpoly [x, realToR (floatOfR x)]
  have hr1 : 1 ≤ realToR (floatOfR x) := by
    have h := add_le_add_left hcl x
    have e1 : x + -(u * B) = x - u * B := by mach_mpoly [x, u * B]
    rw [e1, hback] at h
    exact le_trans hAρ (le_trans (sub_le_sub_right (le_of_lt hxA) (u * B)) h)
  have hr400 : realToR (floatOfR x) ≤ natCast 400 := by
    have h := add_le_add_left hcu x
    rw [hback] at h
    have h2 : x + u * B ≤ natCast 200 + natCast 200 :=
      add_le_add (le_trans (le_of_lt hxB) hB200) (le_trans huB1 hB200)
    rw [← natCast_add] at h2
    exact le_trans h h2
  have hr500 : realToR (floatOfR x) ≤ natCast 500 := le_trans hr400 (natCast_le_natCast_of_nat_le (by decide))
  have habs : abs (realToR (floatOfR x)) ≤ natCast 500 := by
    rw [abs_of_nonneg (le_trans (le_of_lt zero_lt_one_ax) hr1)]; exact hr500
  obtain ⟨hexp, _, _, hout, _⟩ :=
    exp_sub_log_facts (N := 500) (M := 500) (by decide) (by decide) (by decide) hfl habs hfl
      (point_five_le_of_one_le hr1) hr500
  have hout' : (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt env floatOfR x) (emitC emlVarVar)).toF.isFinite
      = true := by
    rw [emitC_correct (stdI1 leanPrims) (stdI2 leanPrims) (stdR1 leanPrims) (stdR2 leanPrims) (std_hrt1 leanPrims)
      (std_hrt2 leanPrims) emlVarVar (envAt env floatOfR x)]
    show (stdI1 leanPrims .exp (envAt env floatOfR x "x").toF
      - stdI1 leanPrims .ln (envAt env floatOfR x "x").toF).isFinite = true
    rw [envAt_x_toF]; exact hout
  exact eml_var_var_quantized_pointwise_grounded env A B hB0 hBmax hAρ x hxA hxB hfl hexp hout'

/-! ## 4. Specimens -/

/-- Every input is `floatOfR 2.0`, which reads back in `[1, 4]`. -/
noncomputable def emlSpecimenEnv : Env := fun _ => Val.scalar (floatOfR 2.0)

/-- Every input is `floatOfR 1.0`, which reads back in `[0.5, 2]`. -/
noncomputable def emlSpecimenEnvOne : Env := fun _ => Val.scalar (floatOfR 1.0)

set_option exponentiation.threshold 1100 in
theorem emlSpecimen_facts :
    (floatOfR 2.0).isFinite = true ∧ 1 ≤ realToR (floatOfR 2.0) ∧ realToR (floatOfR 2.0) ≤ natCast 4 := by
  obtain ⟨hf, hlo, hhi⟩ := floatOfR_decimal_facts 20 1 (by decide) (by decide) (by decide)
  refine ⟨hf, le_trans (le_of_eq (realOfScientific_one_dot_zero.symm.trans (by grounded_decimal))) hlo,
    le_trans hhi ?_⟩
  rw [realOfScientific_two_dot_zero, natCast_four]
  exact le_of_eq (by mach_ring)

set_option exponentiation.threshold 1100 in
theorem emlSpecimenOne_facts :
    (floatOfR 1.0).isFinite = true ∧ 0.5 ≤ realToR (floatOfR 1.0) ∧ realToR (floatOfR 1.0) ≤ natCast 2 := by
  obtain ⟨hf, hlo, hhi⟩ := floatOfR_decimal_facts 10 1 (by decide) (by decide) (by decide)
  refine ⟨hf, le_trans (le_of_eq (by grounded_decimal)) hlo, le_trans hhi ?_⟩
  rw [realOfScientific_one_dot_zero, natCast_two]
  exact le_refl _

/-- Specimen for `eml_tree_grounded_eml_var_var_instantiated`, at `x = floatOfR 2.0`. -/
theorem eml_tree_grounded_eml_var_var_specimen :
    abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) emlSpecimenEnv
          (toCertcomEML (EMLTree.eml EMLTree.var EMLTree.var))).toF
        - (EMLTree.eml EMLTree.var EMLTree.var).eval (realToR (floatOfR 2.0)))
      ≤ emlTreeErrorBound (EMLTree.eml EMLTree.var EMLTree.var) (realToR (floatOfR 2.0)) :=
  (eml_tree_grounded_eml_var_var_instantiated emlSpecimenEnv emlSpecimen_facts.1
    (point_five_le_of_one_le emlSpecimen_facts.2.1)
    (le_trans emlSpecimen_facts.2.2 (natCast_le_natCast_of_nat_le (by decide)))).2.2

/-- Specimen for `eml_tree_grounded_depth2_instantiated`, at `x = floatOfR 1.0`. -/
theorem eml_tree_grounded_depth2_specimen :
    abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) emlSpecimenEnvOne
          (toCertcomEML (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var))).toF
        - (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var).eval (realToR (floatOfR 1.0)))
      ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) EMLTree.var) (realToR (floatOfR 1.0)) :=
  (eml_tree_grounded_depth2_instantiated emlSpecimenEnvOne emlSpecimenOne_facts.1 emlSpecimenOne_facts.2.1
    emlSpecimenOne_facts.2.2).2.2

/-- Specimen for `eml_tree_grounded_eml_const_one_instantiated`, at `x = floatOfR 2.0`. -/
theorem eml_tree_grounded_eml_const_one_specimen :
    abs (realToR (evalEML (stdI1 leanPrims) (stdI2 leanPrims) emlSpecimenEnv
          (toCertcomEML (EMLTree.eml (EMLTree.const 1) EMLTree.var))).toF
        - (EMLTree.eml (EMLTree.const 1) EMLTree.var).eval (realToR (floatOfR 2.0)))
      ≤ emlTreeErrorBound (EMLTree.eml (EMLTree.const 1) EMLTree.var) (realToR (floatOfR 2.0)) :=
  (eml_tree_grounded_eml_const_one_instantiated emlSpecimenEnv emlSpecimen_facts.1
    (point_five_le_of_one_le emlSpecimen_facts.2.1)
    (le_trans emlSpecimen_facts.2.2 (natCast_le_natCast_of_nat_le (by decide)))).2.2

/-- Specimen for `eml_var_var_pipeline_uniform_instantiated`, at `x = floatOfR 2.0`, `A = 1`, `B = 4`. -/
theorem eml_var_var_pipeline_uniform_specimen :
    AbsEnc (u * ((exp (natCast 4) + (u + u) * exp (natCast 4))
          + (log (natCast 4) + u * (abs (log 1) + abs (log (natCast 4)))))
        + ((u + u) * exp (natCast 4) + u * (abs (log 1) + abs (log (natCast 4)))))
      (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) emlSpecimenEnv (emitC emlVarVar)).toF)
      (exp (realToR (floatOfR 2.0)) - log (realToR (floatOfR 2.0))) :=
  eml_var_var_pipeline_uniform_instantiated emlSpecimenEnv 1 (natCast 4) (le_refl 1)
    (natCast_le_natCast_of_nat_le (by decide)) emlSpecimen_facts.1 emlSpecimen_facts.2.1 emlSpecimen_facts.2.2

/-- Specimen for `eml_var_var_quantized_pointwise_instantiated`, at `x = 3.5` in `(3.0, 4.0)`. -/
theorem eml_var_var_quantized_pointwise_specimen :
    abs (realToR (evalC (stdR1 leanPrims) (stdR2 leanPrims) (envAt emlSpecimenEnv floatOfR 3.5)
        (emitC emlVarVar)).toF - (EMLTree.eml EMLTree.var EMLTree.var).eval 3.5)
      ≤ u * ((exp (4.0 + u * 4.0) + (u + u) * exp (4.0 + u * 4.0))
            + (log (4.0 + u * 4.0) + u * (abs (log (3.0 - u * 4.0)) + abs (log (4.0 + u * 4.0)))))
          + ((u + u) * exp (4.0 + u * 4.0) + u * (abs (log (3.0 - u * 4.0)) + abs (log (4.0 + u * 4.0))))
        + (exp (4.0 + u * 4.0) + 1 / (3.0 - u * 4.0)) * (u * 4.0) :=
  eml_var_var_quantized_pointwise_instantiated emlSpecimenEnv 3.0 4.0
    (le_of_lt (realOfScientific_pos 40 true 1 (by decide)))
    (le_trans (decimal_le_natCast 40 1 (by decide)) (natCast_le_natCast_of_nat_le (by decide)))
    (by rw [← realOfScientific_two_dot_zero]; grounded_decimal) 3.5 (by grounded_decimal) (by grounded_decimal)

end Certcom
