import MachLib.EMLRationalGerm
import MachLib.FieldLemmas
import MachLib.GermDeriv
import MachLib.GermClearedSpecimen

/-!
# `RatGerm` algebra — the level-0 class, closed under what it should be

Split out of `LogGermAssembly` on 2026-09-10. **None of this is about logarithms**, and that is the
whole reason for the split: it was written while proving `¬ RatGerm (log ∘ S)` and it sat in that
module, where nobody looking for "is `RatGerm` closed under products" would ever find it.

That is not a hypothetical filing complaint. On 2026-09-09 this same arc re-proved
`cross_of_div_eq_div` and `logRat_cross_identity` because they lived in `LogRatDeriv` — a module
named after the route, not after the lemmas — and were not found. Leaving `ratGerm_add` inside a
log-specific file sets the identical trap for whoever next needs it.

The corpus had **no** `RatGerm` closure lemmas before this arc; `ratGerm_sub_const` (subtract a
constant, `EMLGermSign`) was the only one. For a class the germ layer is stratified by, that is a
gap worth having filled in a findable place.
-/

namespace MachLib
open Real

/-- `p/q ≠ 0` for `p, q ≠ 0`. -/
theorem div_ne_zero' {p q : Real} (hp : p ≠ 0) (hq : q ≠ 0) : p / q ≠ 0 := by
  rw [div_def p q hq]
  exact mul_ne_zero hp (one_div_ne_zero hq)

/-- `a / 1 = a`. -/
private theorem div_one' (a : Real) : a / 1 = a := by
  rw [div_def a 1 (ne_of_gt zero_lt_one_ax),
      show (1 : Real) / 1 = 1 * (1 / 1) from by rw [one_mul_thm],
      mul_inv 1 (ne_of_gt zero_lt_one_ax), mul_one_ax]

/-- **A polynomial is a rational germ**, with denominator `1`. -/
theorem ratGerm_pev (L : List Real) : RatGerm (fun x => pev L x) :=
  ⟨L, [1], 1, le_refl 1,
   fun x _ => by rw [pev_one]; exact ne_of_gt zero_lt_one_ax,
   fun x _ => by rw [pev_one, div_one']⟩

/-! ### `RatGerm` is closed under the field operations

The instantiation step needs `RatGerm A` and `RatGerm B` for the `A`, `B` that
`substituted_coeff_splits` exhibits, and those are sums and products of the relation's
coefficients with `s` and `1/S`. **The corpus had no closure lemmas at all** — only
`ratGerm_sub_const`, which subtracts a constant. These are the general ones; they are reusable well
beyond this route, since `RatGerm` is the level-0 class the whole germ layer is stratified by. -/

/-- `(a·d + c·b)/(b·d) = a/b + c/d`. -/
private theorem div_add_div' {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a * d + c * b) / (b * d) = a / b + c / d := by
  refine div_of_eq_mul (mul_ne_zero hb hd) ?_
  rw [show (b * d) * (a / b + c / d) = d * (b * (a / b)) + b * (d * (c / d)) from by mach_ring,
      mul_div_cancel_left hb, mul_div_cancel_left hd]
  mach_ring

/-- `(a·c)/(b·d) = (a/b)·(c/d)`. -/
private theorem div_mul_div' {a b c d : Real} (hb : b ≠ 0) (hd : d ≠ 0) :
    (a * c) / (b * d) = (a / b) * (c / d) := by
  refine div_of_eq_mul (mul_ne_zero hb hd) ?_
  rw [show (b * d) * ((a / b) * (c / d)) = (b * (a / b)) * (d * (c / d)) from by mach_ring,
      mul_div_cancel_left hb, mul_div_cancel_left hd]

/-- **`RatGerm` is closed under sum.** Common denominator `Qa·Qb`, on the merged ray. -/
theorem ratGerm_add {f g : Real → Real} (hf : RatGerm f) (hg : RatGerm g) :
    RatGerm (fun x => f x + g x) := by
  obtain ⟨Pa, Qa, Xa, hXa, hQa, hfa⟩ := hf
  obtain ⟨Pb, Qb, Xb, hXb, hQb, hgb⟩ := hg
  obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hXa hXb
  refine ⟨padd (pmul Pa Qb) (pmul Pb Qa), pmul Qa Qb, Y, hY, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pev_pmul]
    exact mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))
  · show f x + g x = _
    rw [pev_padd, pev_pmul, pev_pmul, pev_pmul,
        hfa x (le_trans hYa hx), hgb x (le_trans hYb hx)]
    exact (div_add_div' (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))).symm

/-- **`RatGerm` is closed under product.** -/
theorem ratGerm_mul {f g : Real → Real} (hf : RatGerm f) (hg : RatGerm g) :
    RatGerm (fun x => f x * g x) := by
  obtain ⟨Pa, Qa, Xa, hXa, hQa, hfa⟩ := hf
  obtain ⟨Pb, Qb, Xb, hXb, hQb, hgb⟩ := hg
  obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hXa hXb
  refine ⟨pmul Pa Pb, pmul Qa Qb, Y, hY, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pev_pmul]
    exact mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))
  · show f x * g x = _
    rw [pev_pmul, pev_pmul, hfa x (le_trans hYa hx), hgb x (le_trans hYb hx)]
    exact (div_mul_div' (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))).symm

/-- **`RatGerm` is closed under negation**, in the `0 − ·` form the corpus writes. -/
theorem ratGerm_neg {f : Real → Real} (hf : RatGerm f) :
    RatGerm (fun x => 0 - f x) := by
  obtain ⟨P, Q, X, hX, hQ, hfe⟩ := hf
  refine ⟨pscale (0 - 1) P, Q, X, hX, hQ, fun x hx => ?_⟩
  show (0 : Real) - f x = _
  rw [pev_pscale, hfe x hx]
  -- `neg_div` does not apply: the goal has `0 - _`, not `-(_)`, and `rw` matches syntactically
  refine (div_of_eq_mul (hQ x hx) ?_).symm
  rw [show pev Q x * (0 - pev P x / pev Q x) = 0 - pev Q x * (pev P x / pev Q x) from by mach_ring,
      mul_div_cancel_left (hQ x hx)]
  mach_ring

/-- **An explicit quotient of polynomials is a rational germ.** The definition, packaged — this is
what `S' = (P'Q − PQ')/Q²` and every other cleared derivative in the corpus already looks like. -/
theorem ratGerm_of_pev_div {N D : List Real} {X : Real} (hX : 1 ≤ X)
    (hD : ∀ x : Real, X ≤ x → pev D x ≠ 0) :
    RatGerm (fun x => pev N x / pev D x) :=
  ⟨N, D, X, hX, hD, fun _ _ => rfl⟩

/-- **The reciprocal of a non-vanishing rational germ is one**, `1/(P/Q) = Q/P`. Needs the
NUMERATOR non-vanishing too, which is exactly the `1/S` side condition route A carries. -/
theorem ratGerm_inv_of_pev {P Q : List Real} {X : Real} (hX : 1 ≤ X)
    (hP : ∀ x : Real, X ≤ x → pev P x ≠ 0)
    (hQ : ∀ x : Real, X ≤ x → pev Q x ≠ 0) :
    RatGerm (fun x => 1 / (pev P x / pev Q x)) := by
  refine ⟨Q, P, X, hX, hP, fun x hx => ?_⟩
  show 1 / (pev P x / pev Q x) = pev Q x / pev P x
  refine div_eq_div_of_cross (div_ne_zero' (hP x hx) (hQ x hx)) (hP x hx) ?_
  rw [one_mul_thm, mul_div_cancel_left (hQ x hx)]

/-! ### Coefficientwise rationality is preserved by the list operations

`substituted_coeff_splits` exhibits `A` and `B` as combinations of `es`, `gyd cs`, `s` and `1/S`.
For `log_separation` those must be rational germs, so rationality has to survive `gadd`, `gscale`
and `gyd`. Stated over MEMBERSHIP rather than indices: `gadd`'s elements are heads, tails or sums,
which membership sees directly, whereas an index-based statement has to case on the two lists'
relative lengths at every step (`gadd_getElem` needs both, `gadd_getElem_left_none` the overhang). -/

/-- The zero germ is rational. -/
theorem ratGerm_zero : RatGerm (fun _ : Real => (0 : Real)) := by
  refine ⟨[], [1], 1, le_refl 1, fun x _ => by rw [pev_one]; exact ne_of_gt zero_lt_one_ax,
    fun x _ => ?_⟩
  show (0 : Real) = pev ([] : List Real) x / pev ([1] : List Real) x
  rw [pev_one, show pev ([] : List Real) x = 0 from rfl, zero_div]

/-- `gadd` preserves coefficientwise rationality. -/
theorem allRatGerm_gadd : ∀ (a b : List (Real → Real)),
    (∀ c ∈ a, RatGerm c) → (∀ c ∈ b, RatGerm c) → ∀ c ∈ gadd a b, RatGerm c := by
  intro a
  induction a with
  | nil => intro b _ hb c hc; exact hb c hc
  | cons d ds ih =>
      intro b ha hb c hc
      cases b with
      | nil => exact ha c hc
      | cons e es =>
          rcases List.mem_cons.mp hc with hhead | htail
          · rw [hhead]
            exact ratGerm_add (ha d (List.Mem.head _)) (hb e (List.Mem.head _))
          · exact ih es (fun z hz => ha z (List.Mem.tail _ hz))
              (fun z hz => hb z (List.Mem.tail _ hz)) c htail

/-- `gscale` preserves coefficientwise rationality, given a rational scalar. -/
theorem allRatGerm_gscale {v : Real → Real} (hv : RatGerm v) :
    ∀ (cs : List (Real → Real)), (∀ c ∈ cs, RatGerm c) → ∀ c ∈ gscale v cs, RatGerm c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; cases hc
  | cons d ds ih =>
      intro hcs c hc
      rcases List.mem_cons.mp hc with hhead | htail
      · rw [hhead]; exact ratGerm_mul hv (hcs d (List.Mem.head _))
      · exact ih (fun z hz => hcs z (List.Mem.tail _ hz)) c htail

/-- **`gyd` preserves coefficientwise rationality.** The formal `y`-derivative is built from `gadd`
and a zero-headed shift, so this is the two lemmas above plus `ratGerm_zero`. -/
theorem allRatGerm_gyd : ∀ (cs : List (Real → Real)),
    (∀ c ∈ cs, RatGerm c) → ∀ c ∈ gyd cs, RatGerm c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; cases hc
  | cons d ds ih =>
      intro hcs c hc
      have hds : ∀ z ∈ ds, RatGerm z := fun z hz => hcs z (List.Mem.tail _ hz)
      refine allRatGerm_gadd ds ((fun _ => (0 : Real)) :: gyd ds) hds ?_ c hc
      intro z hz
      rcases List.mem_cons.mp hz with hhead | htail
      · rw [hhead]; exact ratGerm_zero
      · exact ih hds z htail

/-- **`RatGerm` is closed under difference.** Same construction as `ratGerm_add` with `psub`. -/
theorem ratGerm_sub {f g : Real → Real} (hf : RatGerm f) (hg : RatGerm g) :
    RatGerm (fun x => f x - g x) := by
  obtain ⟨Pa, Qa, Xa, hXa, hQa, hfa⟩ := hf
  obtain ⟨Pb, Qb, Xb, hXb, hQb, hgb⟩ := hg
  obtain ⟨Y, hY, hYa, hYb⟩ := two_bounds' hXa hXb
  refine ⟨psub (pmul Pa Qb) (pmul Pb Qa), pmul Qa Qb, Y, hY, fun x hx => ?_, fun x hx => ?_⟩
  · rw [pev_pmul]
    exact mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))
  · show f x - g x = _
    rw [pev_psub, pev_pmul, pev_pmul, pev_pmul,
        hfa x (le_trans hYa hx), hgb x (le_trans hYb hx)]
    refine (div_of_eq_mul (mul_ne_zero (hQa x (le_trans hYa hx)) (hQb x (le_trans hYb hx))) ?_).symm
    rw [show (pev Qa x * pev Qb x)
           * (pev Pa x / pev Qa x - pev Pb x / pev Qb x)
         = pev Qb x * (pev Qa x * (pev Pa x / pev Qa x))
           - pev Qa x * (pev Qb x * (pev Pb x / pev Qb x)) from by mach_ring,
        mul_div_cancel_left (hQa x (le_trans hYa hx)),
        mul_div_cancel_left (hQb x (le_trans hYb hx))]
    mach_ring

/-! ### Germ congruence, and the abstract-`S` form the route needs

`not_ratGerm_log_of_pole` concludes about `fun x => log (pev P x / pev Q x)` LITERALLY, while route
A carries an abstract `S` that merely agrees with `P/Q` on a ray. `RatGerm` is a germ property, so
the transfer is sound — but it was being done INLINE (`EMLLogNotRational`'s
`fun x hx => by rw [← h x]; exact hg x hx`), and this would have been the second copy. The corpus's
own rule is to generalise at the second instance, so here it is as a lemma. -/

/-- **`RatGerm` only sees the germ.** Two functions agreeing on a ray are rational together. -/
theorem ratGerm_congr {f g : Real → Real} {X : Real} (hX : 1 ≤ X)
    (h : ∀ x : Real, X ≤ x → f x = g x) (hg : RatGerm g) : RatGerm f := by
  obtain ⟨P, Q, Xg, hXg, hQ, hge⟩ := hg
  obtain ⟨Y, hY, hYX, hYg⟩ := two_bounds' hX hXg
  exact ⟨P, Q, Y, hY, fun x hx => hQ x (le_trans hYg hx),
    fun x hx => by rw [h x (le_trans hYX hx)]; exact hge x (le_trans hYg hx)⟩

end MachLib
