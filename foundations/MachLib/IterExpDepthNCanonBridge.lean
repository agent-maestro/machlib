import MachLib.IterExpDepthNCanonDegree
import MachLib.MultiPolyReconstruct

/-!
# Phase C, brick 1 — the phantom / non-phantom bridge for the canonical `y`-degree (∀N)

The eval-invariant measure descends under the reduce via a **phantom / non-phantom split** (the base
case `chain2MeasureCanonEvalInv_descends` is exactly this): when the top `y_i`-coefficient is
*non-phantom* (not canon-zero) the canonical degree/leading-coefficient coincide with the syntactic
ones — so the eval-invariant measure equals the syntactic one and the (deep) syntactic descent applies;
when *phantom* the canonical degree `cdegYAt` strictly drops, giving a first-component descent outright.

This brick supplies the two directions of that split, index- and depth-generic (the depth-2 originals
`cdegY1_eq_degreeY1_of_top` / `cdegY1_lt_degreeY1_of_top` / `canonLcY1_eq_top` were `MultiPoly 2`,
index `⟨1⟩`):

* `ytopAt i q` — the syntactic top (highest-power) `y_i`-coefficient.
* `cdegYAt_eq_degreeYAt_of_top` / `canonLcYAt_eq_ytop` — **non-phantom** ⇒ canonical = syntactic.
* `cdegYAt_lt_degreeYAt_of_top` — **phantom** (+ positive syntactic degree) ⇒ `cdegYAt` strictly drops.
* `canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom` — non-phantom ⇒ the canonical leading coefficient is
  eval-equal to the syntactic `leadingCoeffY` (what the measure-equality will consume).

No `sorry`; footprint as Phase A.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.MultiPolyReconstruct

/-! ### Generic list helpers (the depth-2 originals are `private`; re-declared here). -/

private theorem reverse_head_eq_getLast {α : Type} (L : List α) (hne : L ≠ [])
    {a : α} {t : List α} (hrev : L.reverse = a :: t) : a = L.getLast hne := by
  have hh : L.reverse.head? = L.getLast? := List.head?_reverse L
  rw [hrev, List.head?_cons, List.getLast?_eq_getLast L hne] at hh
  exact Option.some.inj hh

private theorem length_dropWhile_le'' {α : Type} (p : α → Bool) :
    ∀ l : List α, (l.dropWhile p).length ≤ l.length
  | [] => Nat.le_refl 0
  | a :: as => by
    by_cases hp : p a = true
    · have hd : (a :: as).dropWhile p = as.dropWhile p := by simp [List.dropWhile, hp]
      rw [hd]; exact Nat.le_succ_of_le (length_dropWhile_le'' p as)
    · have hd : (a :: as).dropWhile p = a :: as := by simp [List.dropWhile, hp]
      rw [hd]; exact Nat.le_refl _

private theorem rdw_full_of_getLast_neg {α : Type} (p : α → Bool) (L : List α) (hne : L ≠ [])
    (hlast : p (L.getLast hne) = false) : L.reverse.dropWhile p = L.reverse := by
  rcases hrev : L.reverse with _ | ⟨a, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) hne
  · rw [List.dropWhile_cons, reverse_head_eq_getLast L hne hrev, hlast, if_neg (by decide)]

private theorem rdw_lt_of_getLast_pos {α : Type} (p : α → Bool) (L : List α) (hne : L ≠ [])
    (hlast : p (L.getLast hne) = true) : (L.reverse.dropWhile p).length < L.length := by
  rcases hrev : L.reverse with _ | ⟨a, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) hne
  · have hpos0 : 0 < L.length := Nat.pos_of_ne_zero (fun h => hne (List.length_eq_zero.mp h))
    have htlen : t.length = L.length - 1 := by
      have hc := congrArg List.length hrev
      rw [List.length_reverse, List.length_cons] at hc
      omega
    rw [List.dropWhile_cons, reverse_head_eq_getLast L hne hrev, hlast, if_pos rfl]
    calc (t.dropWhile p).length ≤ t.length := length_dropWhile_le'' p t
      _ < L.length := by omega

/-! ### The syntactic top `y_i`-coefficient and the phantom / non-phantom bridges. -/

/-- The syntactic top (highest-power) `y_i`-coefficient of `q`. -/
noncomputable def ytopAt {n : Nat} (i : Fin n) (q : MultiPoly n) : MultiPoly n :=
  (yCoeffsAt i q).getLast (yCoeffsAt_nonempty i q)

/-- **Non-phantom ⇒ canonical `y_i`-degree equals the syntactic one** (nothing dropped). -/
theorem cdegYAt_eq_degreeYAt_of_top {n : Nat} (i : Fin n) (q : MultiPoly n)
    (hlast : canonZeroB (ytopAt i q) = false) :
    cdegYAt i q = MultiPoly.degreeY i q := by
  unfold ytopAt at hlast
  unfold cdegYAt
  rw [rdw_full_of_getLast_neg canonZeroB _ (yCoeffsAt_nonempty i q) hlast,
      List.length_reverse, yCoeffsAt_length_eq]
  omega

/-- **Non-phantom ⇒ the canonical leading `y_i`-coefficient IS the syntactic top coefficient.** -/
theorem canonLcYAt_eq_ytop {n : Nat} (i : Fin n) (q : MultiPoly n)
    (hlast : canonZeroB (ytopAt i q) = false) :
    canonLcYAt i q = ytopAt i q := by
  unfold canonLcYAt
  rw [rdw_full_of_getLast_neg canonZeroB _ (yCoeffsAt_nonempty i q) hlast]
  rcases hrev : (yCoeffsAt i q).reverse with _ | ⟨a, t⟩
  · exact absurd (List.reverse_eq_nil_iff.mp hrev) (yCoeffsAt_nonempty i q)
  · show a = ytopAt i q
    exact reverse_head_eq_getLast _ (yCoeffsAt_nonempty i q) hrev

/-- **Phantom top + positive syntactic degree ⇒ `cdegYAt` strictly drops.** -/
theorem cdegYAt_lt_degreeYAt_of_top {n : Nat} (i : Fin n) (q : MultiPoly n)
    (hlast : canonZeroB (ytopAt i q) = true)
    (hpos : 0 < MultiPoly.degreeY i q) :
    cdegYAt i q < MultiPoly.degreeY i q := by
  unfold cdegYAt
  have hlt := rdw_lt_of_getLast_pos canonZeroB _ (yCoeffsAt_nonempty i q) hlast
  rw [yCoeffsAt_length_eq] at hlt
  omega

/-- **Non-phantom ⇒ the canonical leading coefficient is eval-equal to the syntactic `leadingCoeffY`.**
(`canonLcYAt = ytopAt`, and `ytopAt` — the `getLast` of `yCoeffsAt` — is eval-equal to `leadingCoeffY`.) -/
theorem canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom {n : Nat} (i : Fin n) (q : MultiPoly n)
    (hlast : canonZeroB (ytopAt i q) = false)
    (x : Real) (env : Fin n → Real) :
    MultiPoly.eval (canonLcYAt i q) x env = MultiPoly.eval (MultiPoly.leadingCoeffY i q) x env := by
  rw [canonLcYAt_eq_ytop i q hlast]
  exact (eval_leadingCoeffY_eq_eval_yCoeffsAt_getLast_general i q (yCoeffsAt_nonempty i q) x env).symm

end MachLib.IterExpDepthN
