import MachLib.MultiVarTwoExpRolle
import MachLib.BivariateDeriv

/-!
# General-curve Khovanskii–Rolle count via the bivariate parametrization (Gate 2d, IFT gate — capstone)

Closes the IFT-gate arc: connects the bivariate parametrization (`curve_tangent_and_chain`) to the
Khovanskii–Rolle counting (`khovanskii_rolle_count`), so a **general nonlinear curve** `{f = 0}` — not just
an explicitly-parametrized line — gets counted. Along the curve `y = yc x` (jointly differentiable `f, g`
with `fᵧ ≠ 0`, `f ≡ 0`), the implicit derivative `yc' = −fₓ/fᵧ` makes the T.1 hypotheses hold at every
point: the tangent condition and the chain rule for `g` along the curve are *derived*, not assumed.

`khovanskii_rolle_count_curve`: the number of intersections of `{f = 0}` and `{g = 0}` on the arc is
`≤ #{Jacobian zeros} + 1`. This is `khovanskii_rolle_count` with its parametrization hypotheses discharged
by the IFT bridge — the general-curve form the two-exponential theorem needs (`yc` exists and is unique
in-model via `exists_unique_root`; differentiable via the bivariate bridge axioms).
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-- **Khovanskii–Rolle counting on a general parametrized curve.** With `f, g` jointly differentiable along
`y = yc x` (`fᵧ ≠ 0`, `f ≡ 0`), the intersections of `{f=0}` and `{g=0}` on the arc number `≤ #{Jacobian
zeros} + 1`. The parametrization hypotheses (tangent, chain rule) are discharged by `curve_tangent_and_chain`
at each point; `N` bounds the Jacobian zeros (the recursion / base case). -/
theorem khovanskii_rolle_count_curve
    (f g : Real → Real → Real) (fx fy gx gy yc : Real → Real) (a b : Real) (hab : a < b)
    (hf2 : ∀ z : Real, a < z → z < b → HasDerivAt2 f (fx z) (fy z) z (yc z))
    (hg2 : ∀ z : Real, a < z → z < b → HasDerivAt2 g (gx z) (gy z) z (yc z))
    (hfy : ∀ z : Real, a < z → z < b → fy z ≠ 0)
    (hid : ∀ s : Real, f s (yc s) = 0)
    (N : Nat)
    (hJ_bound : ∀ zeros_J : List Real, zeros_J.Nodup →
        (∀ z ∈ zeros_J, a < z ∧ z < b ∧ fx z * gy z - fy z * gx z = 0) →
        zeros_J.length ≤ N) :
    ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ g z (yc z) = 0) →
      zeros_g.length ≤ N + 1 := by
  apply khovanskii_rolle_count
    (fun s => g s (yc s)) (fun z => -fx z / fy z) fx fy gx gy a b hab
  · intro z hza hzb
    obtain ⟨_, _, hchain⟩ := curve_tangent_and_chain f g (fx z) (fy z) (gx z) (gy z) yc z
      (hf2 z hza hzb) (hg2 z hza hzb) (hfy z hza hzb) hid
    rw [show gx z + gy z * (-fx z / fy z) = gx z * 1 + gy z * (-fx z / fy z) from by rw [mul_one_ax]]
    exact hchain
  · intro z hza hzb
    exact (curve_tangent_and_chain f g (fx z) (fy z) (gx z) (gy z) yc z
      (hf2 z hza hzb) (hg2 z hza hzb) (hfy z hza hzb) hid).2.1
  · exact hJ_bound

end TwoExp
end MultiVarMod
end MachLib
