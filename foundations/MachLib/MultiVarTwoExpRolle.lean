import MachLib.Rolle
import MachLib.Ring
import MachLib.MultiVarBezoutFiber

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

/-- **Khovanskii–Rolle counting step (parametrized).** On an arc of `{f=0}` (parametrized by `y=yc(x)`,
curve-tangent `f_x + f_y·y' = 0`), the number of intersections of `{f=0}` and `{g=0}` is
`≤ #{Jacobian zeros on the arc} + 1`. This is the inductive step of Khovanskii's theorem: it trades the
transcendental intersections `{f=0}∩{g=0}` for the Jacobian intersections `{f=0}∩{J=0}` (one fewer
"level"), paying a `+1` per arc. Reduces to the single-variable Rolle count `zero_count_bound_by_deriv`
applied to `g` along the curve, each critical point mapped to a Jacobian zero by `jac_cancel`. `N` bounds
the Jacobian zeros (the recursive/base bound); parametrization and arc taken as hypotheses (the IFT gate).
-/
theorem khovanskii_rolle_count
    (Gc yc' fx fy gx gy : Real → Real) (a b : Real) (hab : a < b)
    (hGderiv : ∀ z, a < z → z < b → HasDerivAt Gc (gx z + gy z * yc' z) z)
    (hcurve : ∀ z, a < z → z < b → fx z + fy z * yc' z = 0)
    (N : Nat)
    (hJ_bound : ∀ zeros_J : List Real, zeros_J.Nodup →
        (∀ z ∈ zeros_J, a < z ∧ z < b ∧ fx z * gy z - fy z * gx z = 0) →
        zeros_J.length ≤ N) :
    ∀ zeros_g : List Real, zeros_g.Nodup →
      (∀ z ∈ zeros_g, a < z ∧ z < b ∧ Gc z = 0) →
      zeros_g.length ≤ N + 1 := by
  apply zero_count_bound_by_deriv Gc a b hab
    (fun c hc1 hc2 => ⟨gx c + gy c * yc' c, hGderiv c hc1 hc2⟩) N
  intro zeros_f' hnd hprops
  apply hJ_bound zeros_f' hnd
  intro z hz
  obtain ⟨hza, hzb, f'', hderiv, hf''0⟩ := hprops z hz
  refine ⟨hza, hzb, ?_⟩
  have hg0 : gx z + gy z * yc' z = 0 := by
    rw [HasDerivAt_unique Gc (gx z + gy z * yc' z) f'' z (hGderiv z hza hzb) hderiv, hf''0]
  exact jac_cancel (fx z) (fy z) (gx z) (gy z) (yc' z) (hcurve z hza hzb) hg0

/-- **Khovanskii–Rolle multi-arc bound.** The curve `{f=0}` generally splits into several arcs; the total
number of intersections of `{f=0}` and `{g=0}` is the sum over arcs. Given `≤ M` arcs (each carrying its
`Nodup` list of intersection points), and each arc's count `≤ N+1` (the per-arc `khovanskii_rolle_count`,
with `N` bounding the Jacobian zeros on that arc), the total is `≤ M·(N+1)`. Fibered form (arcs given), as
in `bezout_of_fibration`; combined with a bound `M` on the number of arcs (connected components of `{f=0}`)
and `N` on the Jacobian zeros, this is the global Khovanskii bound for the two-curve intersection. -/
theorem khovanskii_rolle_multiarc {γ : Type} (arcs : List (γ × List Real)) (M N : Nat)
    (hM : arcs.length ≤ M) (harc : ∀ arc ∈ arcs, arc.2.length ≤ N + 1) :
    (arcs.flatMap (fun arc => arc.2)).length ≤ M * (N + 1) :=
  Nat.le_trans (MultiVarMod.length_flatMap_le' (N + 1) arcs harc)
    (Nat.mul_le_mul hM (Nat.le_refl _))

end TwoExp
end MultiVarMod
end MachLib
