import MachLib.Rolle
import MachLib.Ring

/-!
# The Khovanskii–Rolle step, parametrized (Gate 2d, two-exponential frontier, T.0)

The inductive step of Khovanskii's finiteness theorem — the genuine multivariate-Rolle tool the
two-independent-exponentials case (`{P(x,y,eˣ,eʸ)=0, Q=0}`) needs — reduced to single-variable `rolle_ct`.

Along an arc of the curve `{f = 0}` parametrized by `x` (`y = yc(x)`), `g(x, yc x)` restricted to the curve
is a single real function; between two of its zeros `rolle_ct` gives an interior critical point, where the
**Jacobian** `J = f_x g_y − f_y g_x` vanishes. This confirms the scoping's central claim: the multivariate
Rolle IS single-variable `rolle_ct` composed with a curve parametrization — **no new analytic axiom**. The
parametrization (the curve-tangent condition `f_x + f_y·y' = 0`, from differentiating `f(x,yc x)=0`) is
taken as a hypothesis here, exactly as `bezout_of_fibration` takes the fibration as given; supplying it is
the implicit-function-theorem gate (T.*), the real distance to a theorem.

Notably the Jacobian vanishing needs **no** `f_y ≠ 0`: it is the linear combination `g_y·(f_x+f_y y') −
f_y·(g_x+g_y y')` of the two tangency conditions.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real

/-- **Parametrized Khovanskii–Rolle step.** On `[a,b]`, with `Gc = g` along the curve vanishing at both
ends and differentiable (chain-rule derivative `g_x + g_y·y'`), and the curve-tangent condition
`f_x + f_y·y' = 0`, `rolle_ct` yields an interior point where BOTH tangency conditions hold. -/
theorem khovanskii_rolle_step
    (Gc yc' fx fy gx gy : Real → Real) (a b : Real) (hab : a < b)
    (hGa : Gc a = 0) (hGb : Gc b = 0)
    (hGderiv : ∀ x, a ≤ x → x ≤ b → HasDerivAt Gc (gx x + gy x * yc' x) x)
    (hcurve : ∀ x, a ≤ x → x ≤ b → fx x + fy x * yc' x = 0) :
    ∃ xstar, a < xstar ∧ xstar < b ∧
      fx xstar + fy xstar * yc' xstar = 0 ∧ gx xstar + gy xstar * yc' xstar = 0 := by
  obtain ⟨xstar, hax, hxb, hderiv0⟩ := rolle_ct Gc a b hab (by rw [hGa, hGb])
    (fun x hxa hxb => ⟨gx x + gy x * yc' x, hGderiv x hxa hxb⟩)
  exact ⟨xstar, hax, hxb, hcurve xstar (le_of_lt_r hax) (le_of_lt_r hxb),
    (HasDerivAt_unique Gc 0 (gx xstar + gy xstar * yc' xstar) xstar hderiv0
      (hGderiv xstar (le_of_lt_r hax) (le_of_lt_r hxb))).symm⟩

/-- The Jacobian cancellation: `f_x + f_y·y' = 0` and `g_x + g_y·y' = 0` force `J = f_x g_y − f_y g_x = 0`
(a linear combination `g_y·⟨tangency_f⟩ − f_y·⟨tangency_g⟩`, no `f_y ≠ 0`). -/
theorem jac_cancel (Fx Fy Gx Gy Yc : Real) (h1 : Fx + Fy * Yc = 0) (h2 : Gx + Gy * Yc = 0) :
    Fx * Gy - Fy * Gx = 0 := by
  have hcomb : Gy * (Fx + Fy * Yc) - Fy * (Gx + Gy * Yc) = Fx * Gy - Fy * Gx := by
    mach_mpoly [Fx, Fy, Gx, Gy, Yc]
  rw [← hcomb, h1, h2]; mach_ring

/-- **Khovanskii–Rolle: the Jacobian vanishes between two curve intersections.** `J = f_x g_y − f_y g_x`
vanishes at the interior critical point — a linear combination of the two tangency conditions, needing no
`f_y ≠ 0`. This is the inductive step: intersections of `{f=0}` and `{g=0}` are bounded by intersections of
`{f=0}` and `{J=0}` (plus arc/boundary terms — the T.1 counting). -/
theorem khovanskii_rolle_jacobian
    (Gc yc' fx fy gx gy : Real → Real) (a b : Real) (hab : a < b)
    (hGa : Gc a = 0) (hGb : Gc b = 0)
    (hGderiv : ∀ x, a ≤ x → x ≤ b → HasDerivAt Gc (gx x + gy x * yc' x) x)
    (hcurve : ∀ x, a ≤ x → x ≤ b → fx x + fy x * yc' x = 0) :
    ∃ xstar, a < xstar ∧ xstar < b ∧
      fx xstar * gy xstar - fy xstar * gx xstar = 0 := by
  obtain ⟨xstar, hax, hxb, hf0, hg0⟩ :=
    khovanskii_rolle_step Gc yc' fx fy gx gy a b hab hGa hGb hGderiv hcurve
  exact ⟨xstar, hax, hxb,
    jac_cancel (fx xstar) (fy xstar) (gx xstar) (gy xstar) (yc' xstar) hf0 hg0⟩

end TwoExp
end MultiVarMod
end MachLib
