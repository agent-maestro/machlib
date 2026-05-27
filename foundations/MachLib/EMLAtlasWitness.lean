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

end Real
end MachLib
