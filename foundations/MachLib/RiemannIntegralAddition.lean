import MachLib.GaussianLaplaceRoute

/-!
# Value-level additivity of the Riemann integral over a sum of integrands

`riemann_integral_add`: for continuous `f, g` on `[a,b]`, the Riemann-integral VALUE of `f + g`
equals the sum of the values of `f` and `g`. This is the `∫(f+g) = ∫f + ∫g` fact that
`GaussianLaplaceRoute.lean`'s §6 header explicitly flagged as "genuinely hard" for the general
case and deliberately avoided (the Leibniz rule only needed a one-directional inequality). It is
NOT `RiemannIntegralAdditivity.lean`'s `riemann_integral_additivity`, which is the *interval*-
splitting fact `∫_a^c = ∫_a^b + ∫_b^c` — a different theorem entirely.

**How it closes for continuous integrands on a fixed bounded interval**, despite the general
difficulty: the two one-directional Darboux inequalities `upperSumCont_add_le`/
`lowerSumCont_add_ge` (`GaussianLaplaceRoute.lean`, proven earlier for the Leibniz bound's own
narrower purpose) sandwich `∫(f+g)` between `∫f + ∫g`'s upper and lower Darboux sums at every
dyadic level; the sandwich width is controlled by `f`'s and `g`'s OWN gaps (the `f+g` gap is not
even needed), transported to a common refinement level `K := max k₁ k₂` via the dyadic
anti/mono-tonicity facts, then squeezed to equality with `eq_of_forall_pos_abs_sub_lt`. Same
`K := max(k₁,k₂)`-refinement + eps/2+eps/2 pattern as `hasDerivAt_GFn`.

Stage S0 of the scalar Bayesian/MMSE-optimality arc (the "probability pillar"): the pivotal
general-purpose lemma every "complete the square and integrate" step downstream rests on. Built
and verified FIRST, in isolation, as the arc's highest-uncertainty risk probe.

`sorryAx`-free, no new axioms — rests only on the existing continuous-Riemann-integral
infrastructure plus the already-proven one-directional Darboux additivity.
-/

namespace MachLib
namespace Real

/-- `a - b < B` and `b - a < B` together give `|a - b| < B`. -/
private theorem abs_sub_lt_of_both {a b B : Real} (h1 : a - b < B) (h2 : b - a < B) :
    abs (a - b) < B := by
  rcases lt_total (a - b) 0 with h | h | h
  · rw [abs_of_nonpos (le_of_lt h), show -(a - b) = b - a from by mach_mpoly [a, b]]; exact h2
  · rw [h, abs_zero]; rw [h] at h1; exact h1
  · rw [abs_of_nonneg (le_of_lt h)]; exact h1

/-- `A ≤ B` and `C ≤ D` give `A - D ≤ B - C` (subtraction is monotone up in the minuend, down in
the subtrahend). -/
private theorem sub_le_sub_mono {A B C D : Real} (h1 : A ≤ B) (h2 : C ≤ D) : A - D ≤ B - C := by
  have h3 := add_le_add_both h1 (neg_le_neg h2)
  rwa [show A + -D = A - D from by mach_mpoly [A, D], show B + -C = B - C from by mach_mpoly [B, C]]
    at h3

private theorem sum_sub_sum_eq (U1 U2 L1 L2 : Real) :
    (U1 + U2) - (L1 + L2) = (U1 - L1) + (U2 - L2) := by mach_mpoly [U1, U2, L1, L2]

private theorem half_add_half (X : Real) : X / (1 + 1) + X / (1 + 1) = X := by
  rw [← mul_two_eq_add_self (X / (1 + 1))]
  exact div_mul_cancel (ne_of_gt two_pos)

/-- **`∫(f+g) = ∫f + ∫g`** at the Riemann-integral value level, for continuous integrands on a
fixed bounded interval. -/
theorem riemann_integral_add {f g : Real → Real} {a b : Real} (hab : a ≤ b)
    (hfcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt f z)
    (hgcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt g z)
    (hfgcont : ∀ z : Real, a ≤ z → z ≤ b → ContinuousAt (fun x => f x + g x) z) :
    Classical.choose (continuous_riemann_integrable (fun x => f x + g x) a b hab hfgcont)
      = Classical.choose (continuous_riemann_integrable f a b hab hfcont)
        + Classical.choose (continuous_riemann_integrable g a b hab hgcont) := by
  have hfgspec := Classical.choose_spec (continuous_riemann_integrable (fun x => f x + g x) a b hab hfgcont)
  have hfspec := Classical.choose_spec (continuous_riemann_integrable f a b hab hfcont)
  have hgspec := Classical.choose_spec (continuous_riemann_integrable g a b hab hgcont)
  apply eq_of_forall_pos_abs_sub_lt
  intro ε hε
  have hε2 : 0 < ε / (1 + 1) := div_pos_of_pos_pos hε two_pos
  obtain ⟨k1, hk1⟩ := hfspec.2 (ε / (1 + 1)) hε2
  obtain ⟨k2, hk2⟩ := hgspec.2 (ε / (1 + 1)) hε2
  obtain ⟨d1, hd1⟩ := Nat.le.dest (Nat.le_max_left k1 k2)
  obtain ⟨d2, hd2⟩ := Nat.le.dest (Nat.le_max_right k1 k2)
  -- f's gap, transported from k1 up to K := max k1 k2, stays < ε/2.
  have hgapf : upperSumCont f a b hab hfcont (2 ^ Nat.max k1 k2) (two_pow_pos (Nat.max k1 k2))
      - lowerSumCont f a b hab hfcont (2 ^ Nat.max k1 k2) (two_pow_pos (Nat.max k1 k2))
      < ε / (1 + 1) := by
    have hanti := upperSumCont_dyadic_anti f a b hab hfcont k1 d1 (two_pow_pos k1)
    have hmono := lowerSumCont_dyadic_mono f a b hab hfcont k1 d1 (two_pow_pos k1)
    rw [hd1] at hanti hmono
    exact lt_of_le_of_lt (sub_le_sub_mono hanti hmono) hk1
  have hgapg : upperSumCont g a b hab hgcont (2 ^ Nat.max k1 k2) (two_pow_pos (Nat.max k1 k2))
      - lowerSumCont g a b hab hgcont (2 ^ Nat.max k1 k2) (two_pow_pos (Nat.max k1 k2))
      < ε / (1 + 1) := by
    have hanti := upperSumCont_dyadic_anti g a b hab hgcont k2 d2 (two_pow_pos k2)
    have hmono := lowerSumCont_dyadic_mono g a b hab hgcont k2 d2 (two_pow_pos k2)
    rw [hd2] at hanti hmono
    exact lt_of_le_of_lt (sub_le_sub_mono hanti hmono) hk2
  -- Combined gap < ε.
  have hgapsum := add_lt_add_both hgapf hgapg
  rw [half_add_half ε] at hgapsum
  -- The two one-directional Darboux inequalities at level K.
  have hUp := upperSumCont_add_le hab hfcont hgcont hfgcont (2 ^ Nat.max k1 k2)
    (two_pow_pos (Nat.max k1 k2))
  have hLow := lowerSumCont_add_ge hab hfcont hgcont hfgcont (2 ^ Nat.max k1 k2)
    (two_pow_pos (Nat.max k1 k2))
  -- Sandwich bounds at level K.
  have hfL := (hfspec.1 (Nat.max k1 k2)).1
  have hfU := (hfspec.1 (Nat.max k1 k2)).2
  have hgL := (hgspec.1 (Nat.max k1 k2)).1
  have hgU := (hgspec.1 (Nat.max k1 k2)).2
  have hfgL := (hfgspec.1 (Nat.max k1 k2)).1
  have hfgU := (hfgspec.1 (Nat.max k1 k2)).2
  -- Upper: Ifg - (If + Ig) ≤ (Uf + Ug) - (Lf + Lg) = gap_f + gap_g < ε.
  have hupper := sub_le_sub_mono (le_trans hfgU hUp) (add_le_add_both hfL hgL)
  rw [sum_sub_sum_eq _ _ _ _] at hupper
  have hupper' := lt_of_le_of_lt hupper hgapsum
  -- Lower: (If + Ig) - Ifg ≤ (Uf + Ug) - (Lf + Lg) = gap_f + gap_g < ε.
  have hlower := sub_le_sub_mono (add_le_add_both hfU hgU) (le_trans hLow hfgL)
  rw [sum_sub_sum_eq _ _ _ _] at hlower
  have hlower' := lt_of_le_of_lt hlower hgapsum
  exact abs_sub_lt_of_both hupper' hlower'

end Real
end MachLib
