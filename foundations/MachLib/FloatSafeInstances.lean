import MachLib.FloatSafeDischarge

/-!
# Grounded certificates instantiated on the range axioms

Until 2026-09-14 no theorem or axiom here concluded that a float is finite, so the float side conditions of the grounded
certificates (`FloatSafe`, `EMLTreeFloatSafe`) could not be established for any input with an arithmetic node, and only a
constant leaf of `eml_tree_grounded` was instantiated (`FloatSafeDischarge.lean`). Three disclosed axioms, approved by
the owner that day and measured before they were added, change that:

  * `real_fpfinite : FPFiniteOfRange realToR` (`FPGrounding.lean`): finite operands and an exact result at most
    `DBL_MAX` in magnitude give a finite `+`, `−` or `×`, and negation keeps a float finite;
  * `real_round_finite` (`EMLCertcomGrounded.lean`): `floatOfR x` is finite for `|x| ≤ DBL_MAX`;
  * `u_lt_one` (`FPModel.lean`): `u < 1`.

## What is instantiated, and on which domain

  * **`pipeline_det_grounded`**, as `pipeline_det_grounded_instantiated`, for the cancelling determinant `x·y − z·w`.
    Domain: each of the four inputs is a finite float whose real value is at most `B` in magnitude and is `0` or at least
    `α` in magnitude, where `DBL_MIN ≤ α·α` and `4·(B·B) ≤ DBL_MAX`. The bound keeps every node's exact result within
    `DBL_MAX` (the difference's operands are rounded products, at most `(1 + u)·B·B ≤ 2·B·B` by `u_lt_one`), so
    `real_fpfinite` gives `FloatFinite`; the floor gives `ProductsNormal` (`productsNormal_detEML`).
    `pipeline_det_grounded_specimen` shows the domain non-empty at `α = 2⁻⁵¹¹` and `B = 2⁵¹⁰`, the parameters at which it
    admits every input of magnitude `0` or in `[2⁻⁵¹¹, 2⁵¹⁰]`, with the four inputs `floatOfR 0`. The certificate there
    says the computed determinant reads back as exactly `0`.
  * **`pipeline_arith_grounded`**, as `pipeline_arith_grounded_sum_instantiated`, at the sum `x + y`. Domain: both inputs
    finite floats with real values at most `B` in magnitude, and `B + B ≤ DBL_MAX`. `pipeline_arith_grounded_sum_specimen`
    shows it non-empty at `B = 2¹⁰²²` with both inputs `floatOfR 1`, whose real value is strictly positive by `u_lt_one`,
    so the specimen's exact sum is not `0`.

## What `u < 1` does not buy: the `DBL_MIN` branch of a product

`ProductsNormal` asks each exact product to be `0` or at least `DBL_MIN`, and the determinant specimen meets it through the
zero branch. The `DBL_MIN` branch needs a lower bound on a nonzero float's real value, and every lower bound available
carries a factor `1 − u`: `real_round_bounds` puts `realToR (floatOfR x)` no closer to `0` than `(1 − u)·|x|`, and each
rounding through `real_fpbridge` costs another factor `1 − u`. `u < 1` makes `1 − u` positive and says nothing about how
small it is, so no product of two such values is provably at least `DBL_MIN` from it. The sum specimen can be nonzero
because a sum carries no `DBL_MIN` condition. Later on 2026-09-14 the owner approved `u_le_half` (`u + u ≤ 1`, so
`1 − u ≥ 1/2`), and `pipeline_det_grounded_nonzero_specimen` (`GroundedPIDInstances.lean`) reaches the `DBL_MIN` branch.

## What was not instantiated here, and where it is now

  * `pid_grounded`, every `pid_<prim>_grounded`, and the `LibmBudget` restatements multiply the literal gains `1.5`, `0.4`
    and `0.05`, and when this module was written no axiom said that a `Float` literal is finite or what its real value is;
    `pid_exp_grounded`, `pid_sinh_grounded`, `pid_cosh_grounded` and `pid_log_cosh_grounded` also needed a finite `exp`,
    `sinh` or `cosh` result. `GroundedPIDInstances.lean` instantiates `pid_grounded` and fourteen of the primitive forms on
    the literal and libm-finiteness axioms approved later that day; `GroundedLogCoshInstance.lean` and
    `GroundedBudgetInstances.lean` instantiate `pid_log_cosh_grounded` and the `LibmBudget` forms on two axioms approved
    later still.
  * `eml_tree_grounded` at an `eml` node, and the `eml_var_var` family, needed finite `exp` and `log` results.
    `GroundedEMLInstances.lean` instantiates `eml_tree_grounded` at three `eml` trees and two of the three `eml_var_var`
    forms, and says why `eml_var_var_certcom_witness_grounded` cannot be instantiated for binary64.
-/

namespace Certcom

open MachLib MachLib.Real

/-! ## 1. Reading back `floatOfR 0` and `floatOfR 1` -/

/-- `1 + u ≤ 2`, from `u < 1`. -/
theorem one_add_u_le_two_of_lt_one : (1 : MachLib.Real) + u ≤ 1 + 1 :=
  add_le_add_left (le_of_lt u_lt_one) 1

/-- `floatOfR 0` reads back as exactly `0` (`real_round_bounds` at `M = 0`). -/
theorem realToR_floatOfR_zero : realToR (floatOfR 0) = 0 := by
  have h := real_round_bounds 0 0 (le_refl 0) dblMax_nonneg (by rw [abs_zero]; exact le_refl 0) (Or.inl rfl)
  rw [mul_zero, sub_zero] at h
  exact eq_zero_of_abs_le_zero h

/-- `floatOfR 1` reads back within `u` of `1`. -/
theorem realToR_floatOfR_one_close : abs (realToR (floatOfR 1) - 1) ≤ u := by
  have h := real_round_bounds 1 1 (le_of_lt zero_lt_one_ax) one_le_dblMax (by rw [abs_one]; exact le_refl 1)
    (Or.inr (by rw [abs_one]; exact dblMin_le_one))
  rw [mul_one_ax] at h
  exact h

/-- **`floatOfR 1` reads back as a positive real.** `real_round_bounds` puts it no closer to `0` than `1 − u`, and
`u_lt_one` makes that positive. With `u = 1`, which `u_le_one` allowed, this did not follow. -/
theorem realToR_floatOfR_one_pos : 0 < realToR (floatOfR 1) := by
  have h1 : -(realToR (floatOfR 1) - 1) ≤ u := neg_le_of_abs_le realToR_floatOfR_one_close
  have e : -(realToR (floatOfR 1) - 1) = 1 - realToR (floatOfR 1) := by mach_ring
  rw [e] at h1
  have h2 : 1 - realToR (floatOfR 1) < 1 := lt_of_le_of_lt h1 u_lt_one
  have h3 := sub_pos_of_lt h2
  have e2 : ∀ r : MachLib.Real, (1 : MachLib.Real) - (1 - r) = r := fun r => by mach_mpoly [r]
  rw [e2] at h3
  exact h3

/-! ## 2. `pipeline_arith_grounded` at the sum `x + y` -/

/-- The sum of the inputs `x` and `y`. -/
def sumXY : EML := .bin .add (.var "x") (.var "y")

/-- `sumXY` is in the arithmetic fragment. -/
theorem isArith_sumXY : IsArith sumXY := .add _ _ (.var "x") (.var "y")

/-- **`pipeline_arith_grounded`, instantiated at `x + y`.** On the domain "both inputs are finite floats whose real
values are at most `B` in magnitude, with `B + B ≤ DBL_MAX`", the float side condition `FloatSafe` holds
(`real_fpfinite.add`), so the emitted C's sum, read through `realToR`, is within `absErr` of the exact sum. -/
theorem pipeline_arith_grounded_sum_instantiated (env : Env) {B : MachLib.Real} (hBmax : B + B ≤ dblMax)
    (hxf : (env "x").toF.isFinite = true) (hyf : (env "y").toF.isFinite = true)
    (hxB : abs (realToR (env "x").toF) ≤ B) (hyB : abs (realToR (env "y").toF) ≤ B) :
    AbsEnc (absErr realToR env sumXY)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC sumXY)).toF)
      (exactR realToR env sumXY) :=
  pipeline_arith_grounded env sumXY isArith_sumXY
    (FloatSafe.add _ _ (FloatSafe.var "x") (FloatSafe.var "y")
      (real_fpfinite.add _ _ hxf hyf (le_trans (abs_add _ _) (le_trans (add_le_add hxB hyB) hBmax))))

/-! ## 3. `pipeline_det_grounded` on a domain of bounds and floors -/

/-- **`pipeline_det_grounded`, instantiated.** On the domain "each of `x`, `y`, `z`, `w` is a finite float whose real value
is at most `B` in magnitude and is `0` or at least `α` in magnitude, with `DBL_MIN ≤ α·α` and `4·(B·B) ≤ DBL_MAX`", the
certificate's `hsafe` is discharged: `real_fpfinite` gives both products and the difference finite (the difference's
operands are rounded products, at most `(1 + u)·(B·B) ≤ 2·(B·B)` by `u_lt_one`), and the floor gives each product `0` or
at least `DBL_MIN`. So the emitted C's determinant, read through `realToR`, is within `u·(2 + u)·(|X·Y| + |Z·W|)` of the
exact `X·Y − Z·W`. -/
theorem pipeline_det_grounded_instantiated (env : Env) {α B : MachLib.Real}
    (hα : 0 ≤ α) (hαα : dblMin ≤ α * α) (hBmax : (1 + 1 + 1 + 1) * (B * B) ≤ dblMax)
    (hxf : (env "x").toF.isFinite = true) (hyf : (env "y").toF.isFinite = true)
    (hzf : (env "z").toF.isFinite = true) (hwf : (env "w").toF.isFinite = true)
    (hxB : abs (realToR (env "x").toF) ≤ B) (hyB : abs (realToR (env "y").toF) ≤ B)
    (hzB : abs (realToR (env "z").toF) ≤ B) (hwB : abs (realToR (env "w").toF) ≤ B)
    (hx : realToR (env "x").toF = 0 ∨ α ≤ abs (realToR (env "x").toF))
    (hy : realToR (env "y").toF = 0 ∨ α ≤ abs (realToR (env "y").toF))
    (hz : realToR (env "z").toF = 0 ∨ α ≤ abs (realToR (env "z").toF))
    (hw : realToR (env "w").toF = 0 ∨ α ≤ abs (realToR (env "w").toF)) :
    AbsEnc (u * (1 + 1 + u) * (abs (realToR (env "x").toF * realToR (env "y").toF)
                              + abs (realToR (env "z").toF * realToR (env "w").toF)))
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) env (emitC detEML)).toF)
      (realToR (env "x").toF * realToR (env "y").toF
        - realToR (env "z").toF * realToR (env "w").toF) := by
  have hB0 : 0 ≤ B := le_trans (abs_nonneg _) hxB
  have hBB : 0 ≤ B * B := mul_nonneg hB0 hB0
  have hxy : abs (realToR (env "x").toF * realToR (env "y").toF) ≤ B * B := by
    rw [abs_mul]; exact mul_le_mul' (abs_nonneg _) hxB (abs_nonneg _) hyB
  have hzw : abs (realToR (env "z").toF * realToR (env "w").toF) ≤ B * B := by
    rw [abs_mul]; exact mul_le_mul' (abs_nonneg _) hzB (abs_nonneg _) hwB
  have hBB4 : B * B ≤ (1 + 1 + 1 + 1) * (B * B) := by
    have e : (1 + 1 + 1 + 1) * (B * B) = B * B + (1 + 1 + 1) * (B * B) := by mach_ring
    rw [e]
    have h3 : (0 : MachLib.Real) ≤ 1 + 1 + 1 := by rw [← natCast_three]; exact Real.natCast_nonneg 3
    exact le_add_of_nonneg_right (mul_nonneg h3 hBB)
  have hf1 : ((env "x").toF * (env "y").toF).isFinite = true :=
    real_fpfinite.mul _ _ hxf hyf (le_trans hxy (le_trans hBB4 hBmax))
  have hf2 : ((env "z").toF * (env "w").toF).isFinite = true :=
    real_fpfinite.mul _ _ hzf hwf (le_trans hzw (le_trans hBB4 hBmax))
  have hr1 := real_fpbridge.mul _ _ hf1 (mul_normal_of_floors hα hα hαα hx hy)
  have hr2 := real_fpbridge.mul _ _ hf2 (mul_normal_of_floors hα hα hαα hz hw)
  have hp1 : abs (realToR ((env "x").toF * (env "y").toF)) ≤ (1 + 1) * (B * B) :=
    le_trans (abs_le_one_add (roundsW_abs hr1))
      (mul_le_mul' one_add_u_nonneg one_add_u_le_two_of_lt_one (abs_nonneg _) hxy)
  have hp2 : abs (realToR ((env "z").toF * (env "w").toF)) ≤ (1 + 1) * (B * B) :=
    le_trans (abs_le_one_add (roundsW_abs hr2))
      (mul_le_mul' one_add_u_nonneg one_add_u_le_two_of_lt_one (abs_nonneg _) hzw)
  have hsum : (1 + 1) * (B * B) + (1 + 1) * (B * B) = (1 + 1 + 1 + 1) * (B * B) := by mach_ring
  have hdiff : abs (realToR ((env "x").toF * (env "y").toF) - realToR ((env "z").toF * (env "w").toF))
      ≤ dblMax := by
    refine le_trans (abs_sub_le' _ _) (le_trans (add_le_add hp1 hp2) ?_)
    rw [hsum]; exact hBmax
  have hd := real_fpfinite.sub _ _ hf1 hf2 hdiff
  have hfin : FloatFinite (fun _ _ => 0) (fun _ _ _ => 0) env detEML :=
    FloatFinite.sub _ _ (FloatFinite.mul _ _ (.var "x") (.var "y") hf1)
      (FloatFinite.mul _ _ (.var "z") (.var "w") hf2) hd
  exact pipeline_det_grounded_of_floor env hfin hα hαα hx hy hz hw

/-! ## 4. Specimens -/

/-- `natCast` is monotone (`natCast_add`, with `b = a + (b − a)`). -/
theorem natCast_le_natCast_of_nat_le {a b : Nat} (h : a ≤ b) : (natCast a : MachLib.Real) ≤ natCast b := by
  rw [← Nat.add_sub_of_le h, natCast_add]
  exact le_add_of_nonneg_right (Real.natCast_nonneg _)

/-- Every input is `floatOfR 0`. -/
noncomputable def zeroInputEnv : Env := fun _ => Val.scalar (floatOfR 0)

/-- Every input is `floatOfR 1`. -/
noncomputable def unitInputEnv : Env := fun _ => Val.scalar (floatOfR 1)

set_option exponentiation.threshold 1100 in
/-- The floor `α = 2⁻⁵¹¹` meets `DBL_MIN ≤ α·α`, with equality. -/
theorem dblMin_le_floor511_sq : dblMin ≤ (1 / natCast (2 ^ 511)) * (1 / natCast (2 ^ 511)) := by
  have hn0 : (0 : MachLib.Real) < natCast (2 ^ 511) := natCast_pos (Nat.two_pow_pos 511)
  have hNN : (0 : MachLib.Real) < natCast (2 ^ 511) * natCast (2 ^ 511) := mul_pos hn0 hn0
  have h1 : 1 / natCast (2 ^ 511) * natCast (2 ^ 511) = (1 : MachLib.Real) := div_mul_cancel (Ne.symm (ne_of_lt hn0))
  have hN1 := mul_inv (natCast (2 ^ 511) * natCast (2 ^ 511)) (Ne.symm (ne_of_lt hNN))
  have key : ∀ a b c : MachLib.Real, (a * a) * ((b * b) * c) = ((a * b) * (a * b)) * c :=
    fun a b c => by mach_mpoly [a, b, c]
  have e : (1 / natCast (2 ^ 511)) * (1 / natCast (2 ^ 511))
      = (1 : MachLib.Real) / (natCast (2 ^ 511) * natCast (2 ^ 511)) := by
    calc (1 / natCast (2 ^ 511)) * (1 / natCast (2 ^ 511))
        = ((1 / natCast (2 ^ 511)) * (1 / natCast (2 ^ 511)))
            * ((natCast (2 ^ 511) * natCast (2 ^ 511)) * (1 / (natCast (2 ^ 511) * natCast (2 ^ 511)))) := by
          rw [hN1, mul_one_ax]
      _ = ((1 / natCast (2 ^ 511) * natCast (2 ^ 511)) * (1 / natCast (2 ^ 511) * natCast (2 ^ 511)))
            * (1 / (natCast (2 ^ 511) * natCast (2 ^ 511))) := key _ _ _
      _ = 1 / (natCast (2 ^ 511) * natCast (2 ^ 511)) := by rw [h1, mul_one_ax, one_mul_thm]
  rw [e, ← natCast_mul]
  exact le_of_eq rfl

set_option exponentiation.threshold 1100 in
/-- The bound `B = 2⁵¹⁰` meets `4·(B·B) ≤ DBL_MAX`. -/
theorem bound510_size : (1 + 1 + 1 + 1) * (natCast (2 ^ 510) * natCast (2 ^ 510)) ≤ dblMax := by
  rw [← natCast_four, ← natCast_mul, ← natCast_mul]
  exact natCast_le_natCast_of_nat_le (by decide)

/-- **Specimen for `pipeline_det_grounded_instantiated`.** Every hypothesis discharged at `α = 2⁻⁵¹¹`, `B = 2⁵¹⁰`, with the
four inputs `floatOfR 0`: finite by `real_round_finite`, exactly `0` by `real_round_bounds`, so each product takes the zero
branch of `ProductsNormal`. The certificate then says the computed determinant reads back as exactly `0`. -/
theorem pipeline_det_grounded_specimen :
    realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) zeroInputEnv (emitC detEML)).toF = 0 := by
  have hf0 : (floatOfR 0).isFinite = true := real_round_finite 0 (by rw [abs_zero]; exact dblMax_nonneg)
  have hr0 : realToR (floatOfR 0) = 0 := realToR_floatOfR_zero
  have hB : abs (realToR (floatOfR 0)) ≤ natCast (2 ^ 510) := by rw [hr0, abs_zero]; exact Real.natCast_nonneg _
  have hα : (0 : MachLib.Real) ≤ 1 / natCast (2 ^ 511) :=
    le_of_lt (MachLib.Real.one_div_pos_of_pos (natCast_pos (Nat.two_pow_pos 511)))
  have h := pipeline_det_grounded_instantiated zeroInputEnv hα dblMin_le_floor511_sq bound510_size hf0 hf0 hf0 hf0
    hB hB hB hB (Or.inl hr0) (Or.inl hr0) (Or.inl hr0) (Or.inl hr0)
  have hx0 : realToR (zeroInputEnv "x").toF = 0 := hr0
  have hy0 : realToR (zeroInputEnv "y").toF = 0 := hr0
  have hz0 : realToR (zeroInputEnv "z").toF = 0 := hr0
  have hw0 : realToR (zeroInputEnv "w").toF = 0 := hr0
  rw [hx0, hy0, hz0, hw0] at h
  simp only [mul_zero, abs_zero, add_zero, sub_zero, AbsEnc] at h
  exact eq_zero_of_abs_le_zero h

set_option exponentiation.threshold 1100 in
/-- **Specimen for `pipeline_arith_grounded_sum_instantiated`, with nonzero inputs.** Every hypothesis discharged at
`B = 2¹⁰²²`, with both inputs `floatOfR 1`: finite by `real_round_finite`, at most `1 + u ≤ 2` in magnitude by
`real_round_bounds` and `u_lt_one`. Their real value is strictly positive (`realToR_floatOfR_one_pos`), so the exact sum
the certificate bounds the computation against is not `0`. -/
theorem pipeline_arith_grounded_sum_specimen :
    0 < exactR realToR unitInputEnv sumXY ∧
    AbsEnc (absErr realToR unitInputEnv sumXY)
      (realToR (evalC (fun _ _ => 0) (fun _ _ _ => 0) unitInputEnv (emitC sumXY)).toF)
      (exactR realToR unitInputEnv sumXY) := by
  have hf1 : (floatOfR 1).isFinite = true := real_round_finite 1 (by rw [abs_one]; exact one_le_dblMax)
  have hb : abs (realToR (floatOfR 1)) ≤ natCast (2 ^ 1022) := by
    have h := abs_le_add_err realToR_floatOfR_one_close
    rw [abs_one] at h
    refine le_trans h (le_trans one_add_u_le_two_of_lt_one ?_)
    rw [← natCast_two]; exact natCast_le_natCast_of_nat_le (by decide)
  have hmax : (natCast (2 ^ 1022) : MachLib.Real) + natCast (2 ^ 1022) ≤ dblMax := by
    rw [← natCast_add]; exact natCast_le_natCast_of_nat_le (by decide)
  have hpos := realToR_floatOfR_one_pos
  refine ⟨?_, pipeline_arith_grounded_sum_instantiated unitInputEnv hmax hf1 hf1 hb hb⟩
  show 0 < realToR (floatOfR 1) + realToR (floatOfR 1)
  exact lt_of_lt_of_le hpos (le_add_of_nonneg_right (le_of_lt hpos))

end Certcom
