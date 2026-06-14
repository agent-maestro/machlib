import MachLib.Exp
import MachLib.Forge

/-!
# Forge kernel application — Defibrillator discharge voltage safety

**Domain:** medical devices — AED (automated external defibrillator),
ICU defibrillator, transthoracic and implantable cardioverter-defibrillator.
**Safety class:** DO-178C / IEC-61508 / ISO-26262 (kernel level), with
downstream **IEC 62304 Class C** (highest medical software safety class).

## The kernel (from Forge, `defibrillator_energy.eml`)

```eml
fn discharge_voltage(initial_voltage, duration, capacitance, impedance) -> Voltage
{
  initial_voltage · exp(-duration / (impedance · capacitance))
}
```

Biphasic-truncated-exponential (BTE) defibrillator discharge: the
voltage across the capacitor decays exponentially through the patient
impedance over the phase duration.

## The verify obligation

The Forge stub ships:
```
theorem discharge_voltage_decays_exponentially ... : True := by trivial
```

i.e. an aspirational name with a vacuous body. The clinically meaningful
strengthening — the one a Class C medical certification would require —
is **sign preservation** under the kernel preconditions: a non-negative
initial voltage produces a non-negative discharge voltage. (No polarity
inversion mid-discharge; the BTE pulse cannot accidentally re-shock the
patient with reversed polarity.)

The companion bound — `abs(discharge_voltage) ≤ abs(initial_voltage)` —
also holds and follows the same shape; we ship sign preservation as the
canonical contract here.

## The proof

`discharge_voltage = initial_voltage · exp(-duration / (impedance · capacitance))`.
The exp factor is positive (`exp_pos`), so non-negative. The product of
a non-negative `initial_voltage` and a non-negative exp factor is
non-negative (`mul_nonneg`). The kernel's actual `impedance · capacitance`
positivity is not used in the sign-preservation direction — the exp
factor is positive regardless of its argument.

The Khovanskii framework does not enter here; this is a direct
`exp_pos` / `mul_nonneg` application. The framework would close
zero-counting obligations for related kernels (multi-phase
defibrillator waveforms, biphasic energy crossings) where the
sign-preservation argument doesn't suffice. -/

namespace MachLib
namespace Forge
namespace DefibrillatorEnergy

open MachLib.Real

/-! ## Constants (matching the Forge .eml) -/

noncomputable def C_MIN : Real := 5.0e-05    -- 50 µF
noncomputable def C_MAX : Real := 5.0e-04    -- 500 µF
noncomputable def R_MIN : Real := 25.0       -- ohms
noncomputable def R_MAX : Real := 200.0
noncomputable def V_MAX : Real := 5000.0
noncomputable def T_MAX : Real := 5.0e-02

/-! ## The discharge voltage (exactly matches the .eml) -/

noncomputable def discharge_voltage
    (initial_voltage duration capacitance impedance : Real) : Real :=
  initial_voltage * Real.exp (-duration / (impedance * capacitance))

/-! ## The safety obligation (strengthened from `True`) -/

/-- **Sign preservation under non-negative initial voltage.** This is
the safety-critical claim that replaces the vacuous `True` placeholder
in `MachLib/Discovered/defibrillator_energy.lean`. A non-negative
initial voltage yields a non-negative discharge voltage — no polarity
inversion mid-phase. -/
theorem discharge_voltage_signpreserving
    (initial_voltage duration capacitance impedance : Real)
    (h_iv_nonneg : 0 ≤ initial_voltage) :
    0 ≤ discharge_voltage initial_voltage duration capacitance impedance := by
  show 0 ≤ initial_voltage * Real.exp (-duration / (impedance * capacitance))
  exact mul_nonneg h_iv_nonneg (exp_nonneg _)

end DefibrillatorEnergy
end Forge
end MachLib
