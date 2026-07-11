import MachLib.MultiVar
import MachLib.PolynomialRootCount

/-!
# Fiber count for `MultiVar` — bridging to the univariate root count (Gate 2d, Rung 0.5, obligation B)

Restricting a `MultiVar k` to a line through `env` in the `live` direction (all other variables fixed to
their `env` values) yields a **univariate polynomial** in the live coordinate — a `Poly`. `toPoly1`
is that restriction; via it the fiber count reduces to monogate's *already-proven* single-variable
polynomial root bound `PolynomialRootCount.poly_root_count_bound` (a `Poly` non-vanishing somewhere has
`≤ degreeUpper` distinct zeros on any interval).

`fiber_count` is the payoff: on a fixed vertical line `x = env`, the solutions of `p = 0` in the live
variable number `≤ degVar live p`. This is **Bezout obligation B** (fiber size `≤ deg`) — closed
end-to-end, reusing the single-variable machinery, no new analytic axiom. The only remaining polynomial-
Bezout obligation is A (the resultant / number of fibers).
-/

namespace MachLib
namespace MultiVarMod

open MachLib.PolynomialEvidence (Poly)
open MachLib.PolynomialRootCount

/-- Restrict a `MultiVar k` to the line `{x_live = t, x_j = env j for j ≠ live}`: the `live` variable
becomes the `Poly` variable, every other variable is frozen to its `env` value. The result is a
univariate `Poly` in the live coordinate. -/
def toPoly1 {k : Nat} (live : Fin k) (env : Fin k → Real) : MultiVar k → Poly
  | .const c => Poly.const c
  | .var j   => if j = live then Poly.var else Poly.const (env j)
  | .add p q => Poly.add (toPoly1 live env p) (toPoly1 live env q)
  | .sub p q => Poly.sub (toPoly1 live env p) (toPoly1 live env q)
  | .mul p q => Poly.mul (toPoly1 live env p) (toPoly1 live env q)

/-- **Eval correspondence.** Evaluating the restricted `Poly` at `t` equals evaluating the original
`MultiVar` on the line (`x_live := t`, other coordinates from `env`). -/
theorem eval_toPoly1 {k : Nat} (live : Fin k) (env : Fin k → Real) (t : Real) :
    ∀ p : MultiVar k,
      Poly.eval (toPoly1 live env p) t
        = MultiVar.eval p (fun j => if j = live then t else env j)
  | .const _ => rfl
  | .var j   => by
      show Poly.eval (if j = live then Poly.var else Poly.const (env j)) t
          = (if j = live then t else env j)
      by_cases h : j = live
      · rw [if_pos h, if_pos h]; rfl
      · rw [if_neg h, if_neg h]; rfl
  | .add p q => by
      show Poly.eval (toPoly1 live env p) t + Poly.eval (toPoly1 live env q) t
          = MultiVar.eval p (fun j => if j = live then t else env j)
            + MultiVar.eval q (fun j => if j = live then t else env j)
      rw [eval_toPoly1 live env t p, eval_toPoly1 live env t q]
  | .sub p q => by
      show Poly.eval (toPoly1 live env p) t - Poly.eval (toPoly1 live env q) t
          = MultiVar.eval p (fun j => if j = live then t else env j)
            - MultiVar.eval q (fun j => if j = live then t else env j)
      rw [eval_toPoly1 live env t p, eval_toPoly1 live env t q]
  | .mul p q => by
      show Poly.eval (toPoly1 live env p) t * Poly.eval (toPoly1 live env q) t
          = MultiVar.eval p (fun j => if j = live then t else env j)
            * MultiVar.eval q (fun j => if j = live then t else env j)
      rw [eval_toPoly1 live env t p, eval_toPoly1 live env t q]

/-- **Degree correspondence.** The restricted `Poly`'s formal degree is `≤` the original's formal degree
in the `live` variable — so a `≤ deg` fiber bound in the live coordinate is inherited. -/
theorem degreeUpper_toPoly1_le {k : Nat} (live : Fin k) (env : Fin k → Real) :
    ∀ p : MultiVar k, degreeUpper (toPoly1 live env p) ≤ MultiVar.degVar live p
  | .const _ => Nat.le_refl 0
  | .var j   => by
      show degreeUpper (if j = live then Poly.var else Poly.const (env j))
          ≤ (if j = live then 1 else 0)
      by_cases h : j = live
      · rw [if_pos h, if_pos h]; exact Nat.le_refl _
      · rw [if_neg h, if_neg h]; exact Nat.le_refl _
  | .add p q => by
      show Nat.max (degreeUpper (toPoly1 live env p)) (degreeUpper (toPoly1 live env q))
          ≤ Nat.max (MultiVar.degVar live p) (MultiVar.degVar live q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (degreeUpper_toPoly1_le live env p) (Nat.le_max_left _ _),
        Nat.le_trans (degreeUpper_toPoly1_le live env q) (Nat.le_max_right _ _)⟩
  | .sub p q => by
      show Nat.max (degreeUpper (toPoly1 live env p)) (degreeUpper (toPoly1 live env q))
          ≤ Nat.max (MultiVar.degVar live p) (MultiVar.degVar live q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (degreeUpper_toPoly1_le live env p) (Nat.le_max_left _ _),
        Nat.le_trans (degreeUpper_toPoly1_le live env q) (Nat.le_max_right _ _)⟩
  | .mul p q => by
      show degreeUpper (toPoly1 live env p) + degreeUpper (toPoly1 live env q)
          ≤ MultiVar.degVar live p + MultiVar.degVar live q
      exact Nat.add_le_add (degreeUpper_toPoly1_le live env p) (degreeUpper_toPoly1_le live env q)

/-- **Bezout obligation B — the fiber count.** On the line `x_live = ·` through `env`, if `p` does not
vanish identically (non-degeneracy: it is not a component of the solution set), the solutions of `p = 0`
in the live coordinate lying in any interval `(a,b)` number `≤ degVar live p ≤ deg p`. Reduces to the
single-variable `poly_root_count_bound` through the `toPoly1` bridge — no new analytic axiom. -/
theorem fiber_count {k : Nat} (live : Fin k) (env : Fin k → Real) (p : MultiVar k)
    (a b : Real) (hab : a < b)
    (hne : ∃ t, MultiVar.eval p (fun j => if j = live then t else env j) ≠ 0)
    (ys : List Real) (hnd : ys.Nodup)
    (hys : ∀ t ∈ ys, a < t ∧ t < b ∧ MultiVar.eval p (fun j => if j = live then t else env j) = 0) :
    ys.length ≤ MultiVar.degVar live p := by
  refine Nat.le_trans ?_ (degreeUpper_toPoly1_le live env p)
  refine poly_root_count_bound (toPoly1 live env p) a b hab ?_ ys hnd ?_
  · obtain ⟨t, ht⟩ := hne
    exact ⟨t, by rw [eval_toPoly1 live env t p]; exact ht⟩
  · intro z hz
    obtain ⟨hza, hzb, hz0⟩ := hys z hz
    exact ⟨hza, hzb, by rw [eval_toPoly1 live env z p]; exact hz0⟩

end MultiVarMod
end MachLib
