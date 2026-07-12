import MachLib.MultiVarExpBridge
import MachLib.ExpPolyEffectiveBound

/-!
# Rung 1 capstone: effective zero-count for a plane system with one exponential (Gate 2d)

Assembles the two halves into the first **multivariate-transcendental** Khovanskii bound in the library.
For a system `{P, Q}` in `MultiVar 3` `(x, y, u)` counted along the curve `u = eˣ` — i.e. counting real `x`
for which `∃ y, P(x, y, eˣ) = 0 ∧ Q(x, y, eˣ) = 0` — the distinct `x`-coordinates in a bounded interval
`(a,b)` are bounded effectively in the degrees, WITHOUT any multivariate-Rolle principle:

* **Elimination (Rung 1.0):** `prsResultant3_vanish_uncond` — the `(x,u)`-resultant `R = Res_y(P,Q)`
  vanishes at every common zero, unconditionally.
* **Substitution (Rung 1.1):** `eval_toExpPoly` — `toExpPoly R` is the single-variable `ExpPoly`
  `x ↦ R(x, eˣ)`, so a common-zero `x`-coordinate is a zero of it.
* **Count:** the proven single-variable Khovanskii bound `expPoly_effective_bound` (`rolle_ct`).

`rung1_one_exp_xcoord_bound` is the result: `#{x-coords} ≤ |coeffs| + Σ simplified-degrees` of the ExpPoly
`R(x, eˣ)`. The transcendence is confined to the single-variable step; the axiom footprint is `rolle_ct`
(via ExpPoly) + Classical — **no new analytic axiom, no multivariate Rolle.** The honest boundary: this
covers an exponential of *one* variable (`u = eˣ`); a mixed exponential (`u = e^{xy}`) resists elimination
and remains the genuine multivariate-Rolle frontier.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.MultiVarMod.MultiVar
open MachLib.SingleExpKhovanskii (ExpPoly)
open MachLib.SingleExpKhovanskii.ExpPoly
open MachLib.Real

/-- **Rung 1 — effective x-coordinate count for a plane system with one exponential.** Counting real `x`
in `(a,b)` such that `∃ y, P(x,y,eˣ) = 0 ∧ Q(x,y,eˣ) = 0` (each witnessed by an `env3` with `u = eˣ`), the
number of distinct such `x` is `≤ |coeffs| + Σ simplified-degrees` of the eliminated ExpPoly
`x ↦ Res_y(P,Q)(x, eˣ)` — modulo only the non-degeneracy `hne` (the resultant is not identically zero
along `u = eˣ`). Reduces to the single-variable Khovanskii bound; no multivariate Rolle. -/
theorem rung1_one_exp_xcoord_bound (P Q : MultiVar 3) (a b : Real) (hab : a < b)
    (hne : ∃ x : Real, a < x ∧ x < b
      ∧ (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).eval x ≠ 0)
    (xs : List Real) (hnd : xs.Nodup)
    (hxs : ∀ x₀ ∈ xs, a < x₀ ∧ x₀ < b ∧
      ∃ env3 : Fin 3 → Real, env3 0 = x₀ ∧ env3 2 = exp x₀ ∧
        MultiVar.eval P env3 = 0 ∧ MultiVar.eval Q env3 = 0) :
    xs.length
      ≤ (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).coeffs.length
        + sumSimplifiedDegrees (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))).coeffs := by
  apply expPoly_effective_bound (toExpPoly (prsResultant3 P Q (prsFuel3 P Q))) a b hab hne xs hnd
  intro x₀ hx₀
  obtain ⟨ha, hb, env3, h_x0, h_u, hP, hQ⟩ := hxs x₀ hx₀
  refine ⟨ha, hb, ?_⟩
  rw [eval_toExpPoly (prsResultant3 P Q (prsFuel3 P Q)) x₀]
  have hf0 : (fun j => if j = (0 : Fin 2) then x₀ else exp x₀) (0 : Fin 2) = env3 0 := by
    rw [h_x0]; exact if_pos rfl
  have hf2 : (fun j => if j = (0 : Fin 2) then x₀ else exp x₀) (1 : Fin 2) = env3 2 := by
    rw [h_u]; exact if_neg (by decide)
  exact prsResultant3_vanish_uncond P Q env3
    (fun j => if j = (0 : Fin 2) then x₀ else exp x₀) hf0 hf2 hP hQ

end MultiVarMod
end MachLib
