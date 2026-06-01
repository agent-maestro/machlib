import MachLib.EML
import MachLib.Ring

/-!
# EML Atlas witness footholds

Small checked witnesses that connect Atlas review-queue entries to concrete
MachLib names. These are deliberately narrow: one local identity at a time,
with no universality, theorem-discovery, or public Atlas-promotion claim.
-/

namespace MachLib
namespace Real

/-- Atlas witness for `exp_from_eml`: `eml(x, 1)` recovers `exp(x)`. -/
theorem atlas_exp_from_eml_witness (x : Real) :
    eml x 1 = exp x :=
  eml_arg2_one x

/-- Atlas witness for `subtraction_boundary`:
`eml(log(v), exp(u))` recovers `v - u` when `v` is positive. -/
theorem atlas_subtraction_boundary_witness (v u : Real) (hv : 0 < v) :
    eml (log v) (exp u) = v - u := by
  unfold eml
  rw [exp_log hv, log_exp]

/-- Affine-offset family witness for `subtraction_boundary`: after shifting
the positive log coordinate by `y`, EML subtracts the offset back out. This is
a proof/teaching-shape witness only; standard subtraction remains the runtime
lowering. -/
theorem subtraction_boundary_affine_offset_witness (x y : Real) (hxy : 0 < x + y) :
    eml (log (x + y)) (exp y) = x := by
  rw [atlas_subtraction_boundary_witness (x + y) y hxy]
  rw [sub_def, add_assoc, add_neg, add_zero]

/-- Two-stage nested-chain witness for `subtraction_boundary`: one checked
subtraction-boundary rewrite feeds the exponent coordinate of the next. This
is a scoped proof/teaching-shape witness only; standard subtraction remains the
runtime lowering. -/
theorem subtraction_boundary_two_stage_chain_witness (v w u : Real) (hv : 0 < v) (hw : 0 < w) :
    eml (log v) (exp (eml (log w) (exp u))) = v - (w - u) := by
  rw [atlas_subtraction_boundary_witness w u hw]
  rw [atlas_subtraction_boundary_witness v (w - u) hv]

/-- Affine-nested chain witness for `subtraction_boundary`: the outer
positive log coordinate is shifted by `y`, while the inner subtraction-boundary
coordinate subtracts the same offset. This is a scoped proof/teaching-shape
witness only; standard subtraction remains the runtime lowering. -/
theorem subtraction_boundary_affine_nested_chain_witness (x y z : Real) (hxy : 0 < x + y) (hz : 0 < z) :
    eml (log (x + y)) (exp (eml (log z) (exp y))) = (x + y) - (z - y) := by
  exact subtraction_boundary_two_stage_chain_witness (x + y) z y hxy hz

/-- Atlas witness for `constants_zero_and_e`: the three small EML constant
boundary identities selected by EML-D9. The local foundation writes Euler's
constant as `exp 1`. -/
theorem constants_zero_one_e_boundary_witness :
    eml 0 (exp 1) = 0 ∧ eml 0 1 = 1 ∧ eml 1 1 = exp 1 := by
  exact ⟨eml_zero_exp_one_zero, eml_zero_one_one, eml_one_one_exp_one⟩

/-- Atlas witness for `ln_from_eml`: the nested EML reconstruction of
`log y` on the positive real branch. This is a proof/teaching-shape witness
only; standard `log y` remains the runtime lowering. -/
theorem ln_from_eml_boundary_witness (y : Real) (hy : 0 < y) :
    eml 1 (eml (eml 1 y) 1) = log y := by
  have _branch_guard : 0 < y := hy
  unfold eml
  rw [log_one, sub_zero, log_exp]
  rw [sub_def, sub_def, neg_add, neg_neg_helper]
  rw [← add_assoc, add_neg, zero_add]

end Real
end MachLib
