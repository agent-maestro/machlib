import MachLib.IntermediateValue
import MachLib.PevDeriv
import MachLib.EMLGermSign

/-!
# One sign per cut-free interval

`ZeroCountOn.glueOverCuts` (`ZeroCountGlue`) reduces an interval-independent zero bound to a bound on
each **cut-free** interval. For a one-query germ `N(x, F(P(x)/Q(x)))` the cuts are the roots of
`pev P` and `pev Q`, and what a cut-free interval must buy is this: **`P/Q` does not change sign
inside it**, so exactly one of the two branch trees (`toEML (queryTerm …)` where `S > 0`,
`negGermTree` where `S ≤ 0`) describes the whole of it.

That is what this module proves, for `pev` directly.

## The mirrored intermediate value

`intermediate_value` (`IntermediateValue`) fires in one direction only — left-negative,
right-positive, `a < b`. Both orders are needed here, so the reversed case goes through
`0 - pev L`, whose roots are exactly `pev L`'s and whose derivative is available from
`HasDerivAt_sub`. `pev_root_between_of_opposite_signs` packages both orders once so the sign argument
never has to think about it again.

## What it costs

`pev_sign_constant_on_cutFree` cites **40 axioms**, and the composition is worth reading: derivative
rules, `hasDerivAt_continuousAt` and `sup_exists` — the intermediate value theorem's own inputs —
and **no `analytic_*`, no `rolle`, no `zero_count_bound_classical`**. Sign-constancy is bought with
*completeness*, not with the zero-counting lane this arc is careful about. A later step that needs
`encBound_bounds` will pay that lane separately, and this module does not pre-pay it.

## What it does NOT give

Nothing here says the germ is non-zero *somewhere* in a cut-free interval, which is the other
hypothesis `encBound_bounds` takes. `¬ EvZeroF` supplies such a point only on a tail, and a bounded
cut-free interval between two poles is where no tail reaches. That gap is named in `(ey)` and is
deliberately not turned into an obligation here.
-/

namespace MachLib

open Real

/-- `pev L` is continuous everywhere — it is differentiable everywhere (`hasDerivAt_pev`) and this
corpus gets continuity from differentiability by axiom (`hasDerivAt_continuousAt`). -/
theorem pev_continuousAt (L : List Real) (x : Real) : ContinuousAt (fun y => pev L y) x :=
  hasDerivAt_continuousAt (hasDerivAt_pev L x)

/-- A root strictly between two points of opposite strict sign, in **either** order.

`intermediate_value` only fires left-negative / right-positive, so the reversed case goes through
`0 - pev L`, whose roots are exactly `pev L`'s. -/
theorem pev_root_between_of_opposite_signs (L : List Real) {x y : Real}
    (hx : pev L x < 0) (hy : 0 < pev L y) :
    ∃ c : Real, ((x < c ∧ c < y) ∨ (y < c ∧ c < x)) ∧ pev L c = 0 := by
  rcases lt_total x y with hxy | hxy | hxy
  · obtain ⟨c, hc1, hc2, hc0⟩ :=
      intermediate_value (fun z => pev L z) x y hxy (fun z _ _ => pev_continuousAt L z) hx hy
    exact ⟨c, Or.inl ⟨hc1, hc2⟩, hc0⟩
  · exact absurd (hxy ▸ hx) (fun h => lt_irrefl_ax (pev L y) (lt_trans_ax h hy))
  · -- `y < x`: mirror through `0 - pev L`
    have hcont : ∀ z : Real, ContinuousAt (fun w => 0 - pev L w) z := by
      intro z
      exact hasDerivAt_continuousAt
        (HasDerivAt_sub (fun _ => 0) (fun w => pev L w) 0 (pev (pderiv L) z) z
          (HasDerivAt_const 0 z) (hasDerivAt_pev L z))
    have hly : (0 : Real) - pev L y < 0 := by
      have e : (0 : Real) - pev L y = 0 - pev L y := rfl
      have h := add_lt_add_left hy (0 - pev L y)
      have l : (0 : Real) - pev L y + 0 = 0 - pev L y := by mach_ring
      have r : (0 : Real) - pev L y + pev L y = 0 := by mach_ring
      rw [l, r] at h; exact h
    have hgx : (0 : Real) < 0 - pev L x := by
      have h := add_lt_add_left hx (0 - pev L x)
      have l : (0 : Real) - pev L x + pev L x = 0 := by mach_ring
      have r : (0 : Real) - pev L x + 0 = 0 - pev L x := by mach_ring
      rw [l, r] at h; exact h
    obtain ⟨c, hc1, hc2, hc0⟩ :=
      intermediate_value (fun z => 0 - pev L z) y x hxy (fun z _ _ => hcont z) hly hgx
    refine ⟨c, Or.inr ⟨hc1, hc2⟩, ?_⟩
    have e : pev L c = 0 - (0 - pev L c) := by mach_ring
    rw [e, hc0]
    mach_ring

/-- **No root strictly inside an interval ⟹ constant strict sign strictly inside.**

This is the step that lets a *cut-free* interval pick one branch of `Fbasis`: with the roots of
`pev P` and `pev Q` as cuts, `P/Q` cannot change sign inside a cut-free interval, so exactly one of
the two germ trees describes the whole of it. -/
theorem pev_sign_constant_of_no_root (L : List Real) (u v : Real)
    (hnr : ∀ x : Real, u < x → x < v → pev L x ≠ 0) :
    (∀ x : Real, u < x → x < v → 0 < pev L x) ∨ (∀ x : Real, u < x → x < v → pev L x < 0) := by
  by_cases hall : ∀ x : Real, u < x → x < v → 0 < pev L x
  · exact Or.inl hall
  · refine Or.inr (fun y hy1 hy2 => ?_)
    have hex : ∃ x : Real, u < x ∧ x < v ∧ ¬ (0 < pev L x) :=
      Classical.byContradiction (fun hne =>
        hall (fun x h1 h2 => Classical.byContradiction (fun hp => hne ⟨x, h1, h2, hp⟩)))
    obtain ⟨x0, hx1, hx2, hx0⟩ := hex
    have hx0neg : pev L x0 < 0 := by
      rcases lt_total (pev L x0) 0 with h | h | h
      · exact h
      · exact absurd h (hnr x0 hx1 hx2)
      · exact absurd h hx0
    rcases lt_total (pev L y) 0 with h | h | h
    · exact h
    · exact absurd h (hnr y hy1 hy2)
    · exfalso
      obtain ⟨c, hc, hc0⟩ := pev_root_between_of_opposite_signs L hx0neg h
      rcases hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hnr c (lt_trans_ax hx1 h1) (lt_trans_ax h2 hy2) hc0
      · exact hnr c (lt_trans_ax hy1 h1) (lt_trans_ax h2 hx2) hc0

/-- **The cut-free form.** With a list containing every root of `pev L`, an interval in which no
member lies strictly inside has constant strict sign — which is how `glueOverCuts`'s hypothesis is
discharged. -/
theorem pev_sign_constant_on_cutFree (L : List Real) (R : List Real)
    (hR : ∀ x : Real, pev L x = 0 → x ∈ R) (u v : Real)
    (hcf : ∀ c ∈ R, ¬ (u < c ∧ c < v)) :
    (∀ x : Real, u < x → x < v → 0 < pev L x) ∨ (∀ x : Real, u < x → x < v → pev L x < 0) :=
  pev_sign_constant_of_no_root L u v (fun x h1 h2 h0 => hcf x (hR x h0) ⟨h1, h2⟩)

/-! ## The quotient — one branch per cut-free interval -/

/-- **`P/Q` has constant strict sign on a cut-free interval**, where the cuts include every root of
`pev P` and of `pev Q`.

This is the statement `glueOverCuts` consumes: `0 < S` throughout selects the `Fbasis` branch and
`toEML (queryTerm …)`; `S < 0` throughout selects `negGermTree`. There is no third case *inside* the
interval, because `S = 0` would need a root of `pev P`, which is a cut.

All four sign combinations are already in the corpus (`div_pos_of_pos_pos`, `div_pos_of_neg_neg`,
`div_neg_of_pos_neg`, `div_neg_of_neg_pos`), so this is a case split and nothing more. -/
theorem ratGerm_sign_constant_on_cutFree (P Q : List Real) (cuts : List Real)
    (hP : ∀ x : Real, pev P x = 0 → x ∈ cuts) (hQ : ∀ x : Real, pev Q x = 0 → x ∈ cuts)
    (u v : Real) (hcf : ∀ c ∈ cuts, ¬ (u < c ∧ c < v)) :
    (∀ x : Real, u < x → x < v → 0 < pev P x / pev Q x)
      ∨ (∀ x : Real, u < x → x < v → pev P x / pev Q x < 0) := by
  rcases pev_sign_constant_on_cutFree P cuts hP u v hcf with hp | hp <;>
    rcases pev_sign_constant_on_cutFree Q cuts hQ u v hcf with hq | hq
  · exact Or.inl (fun x h1 h2 => div_pos_of_pos_pos (hp x h1 h2) (hq x h1 h2))
  · exact Or.inr (fun x h1 h2 => div_neg_of_pos_neg (hp x h1 h2) (hq x h1 h2))
  · exact Or.inr (fun x h1 h2 => div_neg_of_neg_pos (hp x h1 h2) (hq x h1 h2))
  · exact Or.inl (fun x h1 h2 => div_pos_of_neg_neg (hp x h1 h2) (hq x h1 h2))

/-- **`pev Q` is non-vanishing on a cut-free interval** — the other side condition every branch tree
carries, and it falls out of the same sign constancy. -/
theorem pev_ne_zero_on_cutFree (Q : List Real) (cuts : List Real)
    (hQ : ∀ x : Real, pev Q x = 0 → x ∈ cuts)
    (u v : Real) (hcf : ∀ c ∈ cuts, ¬ (u < c ∧ c < v)) :
    ∀ x : Real, u < x → x < v → pev Q x ≠ 0 :=
  fun x h1 h2 h0 => hcf x (hQ x h0) ⟨h1, h2⟩

end MachLib
