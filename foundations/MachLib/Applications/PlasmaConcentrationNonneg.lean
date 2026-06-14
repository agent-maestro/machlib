import MachLib.Exp
import MachLib.Forge

/-!
# Forge kernel application — Pharmacokinetic plasma concentration non-negativity

**Domain:** pharmacology — IV-bolus two-compartment dosing (anaesthesia
target-controlled infusion, oncology, ICU sedation).
**Safety class:** DO-178C / IEC-61508 / ISO-26262 (kernel level),
with downstream IEC 62304 Class C + FDA 510(k) applications.

## The kernel (from Forge, `pk_two_compartment.eml`)

```eml
fn plasma_concentration(A, α, B, β, t) -> PlasmaConcentration
{
  A · exp(-α · t) + B · exp(-β · t)
}
```

The bi-exponential central-compartment concentration after an IV-bolus
dose. A, B are positive coefficients, α, β are decay-rate constants,
t is elapsed time in minutes.

## The verify obligation (was `sorry` in `MachLib/Discovered/pk_two_compartment.lean`)

```
@verify(lean, theorem = "plasma_concentration_nonneg")
```

A safety-critical pharma controller (target-controlled infusion pump,
ICU monitor) must never report a negative concentration — a negative
reading would silently corrupt downstream dosing decisions. The
obligation: under the kernel preconditions (A, B ≥ 0, α, β ∈
[RATE_MIN, RATE_MAX], t ≥ 0), the output is non-negative.

## The proof

Direct from MachLib's nonneg combinators:
  * each term `A · exp(-α · t)` is `(non-negative) · (positive)`, hence
    non-negative by `mul_nonneg` + `exp_nonneg`.
  * the sum of two non-negatives is non-negative by `add_nonneg`.

No appeal to the Khovanskii framework is needed here — the function's
shape is structurally sign-preserving. The framework's `exp_pos`
underwrites the proof; the Khovanskii reduction would close
zero-counting obligations for the same kernel family if asked
(e.g., "plasma_concentration crosses a therapeutic threshold at most
twice"). -/

namespace MachLib
namespace Forge
namespace PkTwoCompartment

open MachLib.Real

/-! ## Constants (matching the Forge .eml) -/

noncomputable def T_MAX    : Real := 1440.0
noncomputable def RATE_MIN : Real := 1.0e-06
noncomputable def RATE_MAX : Real := 1
noncomputable def COEF_MAX : Real := 1000.0

/-! ## The plasma concentration function (exactly matches the .eml) -/

noncomputable def plasma_concentration
    (coef_a rate_alpha coef_b rate_beta time_min : Real) : Real :=
  coef_a * Real.exp (-rate_alpha * time_min)
   + coef_b * Real.exp (-rate_beta * time_min)

/-! ## The safety obligation -/

/-- **Plasma concentration is non-negative** under the Forge kernel
preconditions. This is the safety-critical claim: the bi-exponential
central-compartment readout cannot go negative, so a TCI pump or ICU
monitor never propagates a corrupted reading downstream. -/
theorem plasma_concentration_nonneg
    (coef_a rate_alpha coef_b rate_beta time_min : Real)
    (h_a_nonneg : 0 ≤ coef_a)
    (h_b_nonneg : 0 ≤ coef_b) :
    0 ≤ plasma_concentration coef_a rate_alpha coef_b rate_beta time_min := by
  show 0 ≤ coef_a * Real.exp (-rate_alpha * time_min)
         + coef_b * Real.exp (-rate_beta * time_min)
  apply add_nonneg
  · exact mul_nonneg h_a_nonneg (exp_nonneg _)
  · exact mul_nonneg h_b_nonneg (exp_nonneg _)

end PkTwoCompartment
end Forge
end MachLib
