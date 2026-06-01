import MachLib.EML

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

/-- Atlas witness for `constants_zero_and_e`: the three small EML constant
boundary identities selected by EML-D9. The local foundation writes Euler's
constant as `exp 1`. -/
theorem constants_zero_one_e_boundary_witness :
    eml 0 (exp 1) = 0 ∧ eml 0 1 = 1 ∧ eml 1 1 = exp 1 := by
  exact ⟨eml_zero_exp_one_zero, eml_zero_one_one, eml_one_one_exp_one⟩

end Real
end MachLib
