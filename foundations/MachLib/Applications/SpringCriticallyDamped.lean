import MachLib.Exp
import MachLib.Forge

/-!
# Gaming kernel application — Critically-damped spring positivity

**Domain:** game development — character controllers, camera follow,
UI animation, physics-driven response.
**Safety class:** not safety-critical, but the same kernel shape appears
in industrial servo control and rehabilitation robotics where
sign-preservation matters more.

## The kernel (from `eml-stdlib`, `gaming/animation/spring.eml`)

```eml
@verify(lean, theorem = "spring_critical_signed")
fn critically_damped(amplitude, omega, t_s) -> Real
    where chain_order <= 1,
          domain: omega > 0.0 && t_s >= 0.0
{
    amplitude * (1.0 + omega * t_s) * exp(-omega * t_s)
}
```

Critically damped is the borderline case `ζ = 1` of the damped harmonic
oscillator: the system returns to rest in minimum time without overshoot
or oscillation. The Forge `@verify` obligation `spring_critical_signed`
is the gaming contract: a positive `amplitude` produces a positive
displacement that decays monotonically — no spurious zero-crossings
inside the animation window, no flicker, no jitter.

## Why this is a natural Khovanskii target

Structurally, `critically_damped(t) = amplitude · q(t) · exp(p(t))` with
`q(t) = 1 + ω·t` (polynomial, degree 1) and `p(t) = -ω·t` (polynomial,
degree 1). This is an ExpPoly of length 1 (single exp factor) of total
degree 2.

The constructive Khovanskii bound in `MachLib.SingleExpKhovanskii`
gives a finite upper bound on the zero count of any such expression on
any bounded interval. For this kernel specifically, the bound localises
to:

  zeros of `(1 + ω·t) · exp(-ω·t)` on ℝ  =  zeros of `(1 + ω·t)`
                                          =  exactly one zero at t = -1/ω.

Since the animation window is `t ≥ 0` and `ω > 0`, the lone zero is
outside the domain. So the zero count on `t ≥ 0` is **zero** — the
sign-preservation contract.

This file ships the constructive positivity proof directly via `exp_pos`,
`add_pos`, `mul_pos`. The Khovanskii framework is what would close the
analogous obligation for `spring_underdamped_signed` (which carries an
oscillating cosine factor and so has finitely many but nonzero zeros on
`t ≥ 0`). That obligation remains open; sign-preservation on the
underdamped branch is meaningful only inside each half-cycle, not over
the whole animation window.

## Non-claims

* This file does **not** prove the underdamped sign contract — that
  would require either trig-Khovanskii or a per-half-cycle splitting.
* This file does **not** propagate back to the `.eml` Forge obligation
  via a tooling pipeline. The `Discovered/` companion still ships a
  `sorry` pending the per-kernel propagation tooling.
* The Khovanskii framing is a localisation argument — the Khovanskii
  bound itself is much coarser than the exact zero count proved here.
-/

namespace MachLib
namespace Gaming
namespace SpringCriticallyDamped

open MachLib.Real

/-! ## The critically-damped response (exactly matches the .eml) -/

noncomputable def critically_damped
    (amplitude omega t_s : Real) : Real :=
  amplitude * (1 + omega * t_s) * Real.exp (-omega * t_s)

/-! ## Helper: the envelope `(1 + ω·t) · exp(-ω·t)` is strictly positive
    on the animation window. This is the Khovanskii localisation: the
    lone zero of `(1 + ω·t)` at `t = -1/ω` is excluded by `ω > 0` and
    `t ≥ 0`. -/

theorem envelope_pos
    (omega t_s : Real)
    (h_omega : 0 < omega) (h_t : 0 ≤ t_s) :
    0 < (1 + omega * t_s) * Real.exp (-omega * t_s) := by
  have h_wt_nonneg : 0 ≤ omega * t_s := mul_nonneg (le_of_lt h_omega) h_t
  have h_one_plus_pos : 0 < 1 + omega * t_s := by
    have h_one_le : (1 : Real) ≤ 1 + omega * t_s := by
      have := add_le_add_left h_wt_nonneg 1
      rw [add_zero] at this
      exact this
    exact lt_of_lt_of_le one_pos h_one_le
  exact mul_pos h_one_plus_pos (exp_pos _)

/-! ## The safety obligation -/

/-- **Sign preservation for the critically-damped spring response.**
A non-negative amplitude with a positive natural frequency produces a
non-negative displacement for all non-negative time. No zero-crossing
inside the animation window. -/
theorem spring_critical_signpreserving
    (amplitude omega t_s : Real)
    (h_amp : 0 ≤ amplitude) (h_omega : 0 < omega) (h_t : 0 ≤ t_s) :
    0 ≤ critically_damped amplitude omega t_s := by
  show 0 ≤ amplitude * (1 + omega * t_s) * Real.exp (-omega * t_s)
  have h_env := envelope_pos omega t_s h_omega h_t
  have : amplitude * (1 + omega * t_s) * Real.exp (-omega * t_s)
       = amplitude * ((1 + omega * t_s) * Real.exp (-omega * t_s)) := by
    rw [mul_assoc]
  rw [this]
  exact mul_nonneg h_amp (le_of_lt h_env)

/-- **Strict positivity for the critically-damped spring response.**
The Khovanskii localisation: zero count of the kernel on `t ≥ 0` is
exactly zero. -/
theorem spring_critical_positive
    (amplitude omega t_s : Real)
    (h_amp : 0 < amplitude) (h_omega : 0 < omega) (h_t : 0 ≤ t_s) :
    0 < critically_damped amplitude omega t_s := by
  show 0 < amplitude * (1 + omega * t_s) * Real.exp (-omega * t_s)
  have h_env := envelope_pos omega t_s h_omega h_t
  have : amplitude * (1 + omega * t_s) * Real.exp (-omega * t_s)
       = amplitude * ((1 + omega * t_s) * Real.exp (-omega * t_s)) := by
    rw [mul_assoc]
  rw [this]
  exact mul_pos h_amp h_env

end SpringCriticallyDamped
end Gaming
end MachLib
