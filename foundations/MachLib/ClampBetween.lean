import MachLib.LyapunovSafety
import MachLib.FPModel

/-!
# A clamp difference lies between two values

`clamp` is monotone and translation-equivariant: shifting the argument and both bounds by the same
`d` shifts the result by `d`. Together with `clamp_lipschitz`, that pins down where the difference
of two clamps can land:

* same bounds — `clamp a lo hi − clamp b lo hi` lies between `0` and `a − b`
  (`clamp_sub_between`);
* both bounds shifted by the same `d` — `clamp a lo hi − clamp a' lo' hi'` lies between `a − a'`
  and `d` (`clamp_sub_between_shift`).

The second form is what an error-dependent integrator clamp needs (`AntiWindupPITracking`). Two
loops clamp against bounds that move with their own errors, and move by the same amount, so the
difference of the stored integrators always lies between the difference they would have had
unclamped and the difference of the bounds. "Between" is then consumed by `affine_between` and
`abs_between_le_max`, which turn a clamped step into something no larger than the worse of two
linear steps — without naming a convex weight, so without division, and without a case split on
which loop is saturated.

Nothing here adds trust: `min`, `max`, `abs` and `clamp` are the corpus's own definitions.
-/

namespace MachLib

namespace Real

/-- Adding the same constant to both arguments commutes with `max`. -/
theorem max_add_const (x y d : Real) : max (x + d) (y + d) = max x y + d := by
  unfold MachLib.Real.max
  by_cases h : x ≤ y
  · have h' : x + d ≤ y + d := add_le_add_both h (le_refl d)
    rw [if_pos h, if_pos h']
  · have h' : ¬ (x + d ≤ y + d) := by
      intro hc
      apply h
      have e := sub_le_sub_right hc d
      have ex : x + d - d = x := by mach_mpoly [x, d]
      have ey : y + d - d = y := by mach_mpoly [y, d]
      rw [ex, ey] at e
      exact e
    rw [if_neg h, if_neg h']

/-- Adding the same constant to both arguments commutes with `min`. -/
theorem min_add_const (x y d : Real) : min (x + d) (y + d) = min x y + d := by
  unfold MachLib.Real.min
  by_cases h : x ≤ y
  · have h' : x + d ≤ y + d := add_le_add_both h (le_refl d)
    rw [if_pos h, if_pos h']
  · have h' : ¬ (x + d ≤ y + d) := by
      intro hc
      apply h
      have e := sub_le_sub_right hc d
      have ex : x + d - d = x := by mach_mpoly [x, d]
      have ey : y + d - d = y := by mach_mpoly [y, d]
      rw [ex, ey] at e
      exact e
    rw [if_neg h, if_neg h']

/-- **`clamp` is translation-equivariant.** -/
theorem clamp_add_const (a lo hi d : Real) :
    clamp (a + d) (lo + d) (hi + d) = clamp a lo hi + d := by
  unfold clamp
  rw [max_add_const, min_add_const]

theorem max_mono_left {a b : Real} (h : a ≤ b) (c : Real) : max a c ≤ max b c :=
  max_le (le_trans h (le_max_left b c)) (le_max_right b c)

theorem min_mono_left {a b : Real} (h : a ≤ b) (c : Real) : min a c ≤ min b c :=
  le_min (le_trans (min_le_left a c) h) (min_le_right a c)

/-- **`clamp` is monotone in its argument.** -/
theorem clamp_mono {a b : Real} (h : a ≤ b) (lo hi : Real) :
    clamp a lo hi ≤ clamp b lo hi := by
  unfold clamp
  exact min_mono_left (max_mono_left h lo) hi

theorem max_eq_left_of_le {a b : Real} (h : b ≤ a) : max a b = a := by
  unfold MachLib.Real.max
  by_cases hab : a ≤ b
  · rw [if_pos hab]
    exact le_antisymm h hab
  · rw [if_neg hab]

theorem min_eq_left_of_le {a b : Real} (h : a ≤ b) : min a b = a := by
  unfold MachLib.Real.min
  rw [if_pos h]

/-- **A clamp leaves a value already inside its bounds alone.** -/
theorem clamp_eq_self {v lo hi : Real} (h1 : lo ≤ v) (h2 : v ≤ hi) : clamp v lo hi = v := by
  unfold clamp
  rw [max_eq_left_of_le h1, min_eq_left_of_le h2]

/-- **Same bounds: the clamp difference lies between `0` and `a − b`.** Monotonicity fixes its sign,
`clamp_lipschitz` its size. -/
theorem clamp_sub_between (a b lo hi : Real) :
    (a - b ≤ clamp a lo hi - clamp b lo hi ∧ clamp a lo hi - clamp b lo hi ≤ 0) ∨
    (0 ≤ clamp a lo hi - clamp b lo hi ∧ clamp a lo hi - clamp b lo hi ≤ a - b) := by
  rcases le_total_real a b with hab | hba
  · left
    have hmono := clamp_mono hab lo hi
    have hn : 0 ≤ clamp b lo hi - clamp a lo hi := sub_nonneg_of_le hmono
    have hd : 0 ≤ b - a := sub_nonneg_of_le hab
    have hl := clamp_lipschitz b a lo hi
    rw [abs_of_nonneg hn, abs_of_nonneg hd] at hl
    have e1 : -(b - a) = a - b := by mach_mpoly [a, b]
    have e2 : -(clamp b lo hi - clamp a lo hi) = clamp a lo hi - clamp b lo hi := by
      mach_mpoly [clamp a lo hi, clamp b lo hi]
    constructor
    · have hneg := neg_le_neg hl
      rw [e1, e2] at hneg
      exact hneg
    · have hs := sub_le_sub_right hmono (clamp b lo hi)
      have e0 : clamp b lo hi - clamp b lo hi = 0 := by mach_mpoly [clamp b lo hi]
      rw [e0] at hs
      exact hs
  · right
    have hn : 0 ≤ clamp a lo hi - clamp b lo hi := sub_nonneg_of_le (clamp_mono hba lo hi)
    have hd : 0 ≤ a - b := sub_nonneg_of_le hba
    have hl := clamp_lipschitz a b lo hi
    rw [abs_of_nonneg hn, abs_of_nonneg hd] at hl
    exact ⟨hn, hl⟩

/-- **Both bounds shifted by the same `d`: the clamp difference lies between `a − a'` and `d`.**

Reduced to `clamp_sub_between` by translation: `clamp a' lo' hi' = clamp (a' + d) lo hi − d`. -/
theorem clamp_sub_between_shift (a a' lo hi lo' hi' d : Real)
    (hlo : lo = lo' + d) (hhi : hi = hi' + d) :
    (a - a' ≤ clamp a lo hi - clamp a' lo' hi' ∧ clamp a lo hi - clamp a' lo' hi' ≤ d) ∨
    (d ≤ clamp a lo hi - clamp a' lo' hi' ∧ clamp a lo hi - clamp a' lo' hi' ≤ a - a') := by
  have hsh : clamp a' lo' hi' = clamp (a' + d) lo hi - d := by
    rw [hlo, hhi, clamp_add_const]
    mach_mpoly [clamp a' lo' hi', d]
  have hD : clamp a lo hi - clamp a' lo' hi'
      = (clamp a lo hi - clamp (a' + d) lo hi) + d := by
    rw [hsh]
    mach_mpoly [clamp a lo hi, clamp (a' + d) lo hi, d]
  have ha : a - (a' + d) + d = a - a' := by mach_mpoly [a, a', d]
  have hz : (0 : Real) + d = d := zero_add d
  rw [hD]
  rcases clamp_sub_between a (a' + d) lo hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · left
    constructor
    · have t := add_le_add_both h1 (le_refl d)
      rw [ha] at t
      exact t
    · have t := add_le_add_both h2 (le_refl d)
      rw [hz] at t
      exact t
  · right
    constructor
    · have t := add_le_add_both h1 (le_refl d)
      rw [hz] at t
      exact t
    · have t := add_le_add_both h2 (le_refl d)
      rw [ha] at t
      exact t

/-- A value between two others is no larger in modulus than the larger of their moduli. -/
theorem abs_between_le_max {u v w : Real} (h : (u ≤ w ∧ w ≤ v) ∨ (v ≤ w ∧ w ≤ u)) :
    abs w ≤ max (abs u) (abs v) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_le_of (le_trans h2 (le_trans (le_abs_self v) (le_max_right _ _)))
      (le_trans (neg_le_neg h1) (le_trans (neg_le_abs u) (le_max_left _ _)))
  · exact abs_le_of (le_trans h2 (le_trans (le_abs_self u) (le_max_left _ _)))
      (le_trans (neg_le_neg h1) (le_trans (neg_le_abs v) (le_max_right _ _)))

/-- An affine map preserves betweenness (reversing it when the slope is negative). -/
theorem affine_between (α β t s1 s2 : Real) (h : (s1 ≤ t ∧ t ≤ s2) ∨ (s2 ≤ t ∧ t ≤ s1)) :
    (α + β * s1 ≤ α + β * t ∧ α + β * t ≤ α + β * s2) ∨
    (α + β * s2 ≤ α + β * t ∧ α + β * t ≤ α + β * s1) := by
  have mono : ∀ {x y : Real}, x ≤ y → 0 ≤ β → α + β * x ≤ α + β * y := fun hxy hb =>
    add_le_add_both (le_refl α) (mul_le_mul_of_nonneg_left hxy hb)
  have anti : ∀ {x y : Real}, x ≤ y → β ≤ 0 → α + β * y ≤ α + β * x := by
    intro x y hxy hb
    have hm := mul_le_mul_of_nonneg_left hxy (neg_nonneg_of_nonpos hb)
    have hn := neg_le_neg hm
    have ey : -(-β * y) = β * y := by mach_mpoly [β, y]
    have ex : -(-β * x) = β * x := by mach_mpoly [β, x]
    rw [ey, ex] at hn
    exact add_le_add_both (le_refl α) hn
  rcases le_total_real 0 β with hb | hb
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨mono h1 hb, mono h2 hb⟩
    · exact Or.inr ⟨mono h1 hb, mono h2 hb⟩
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inr ⟨anti h2 hb, anti h1 hb⟩
    · exact Or.inl ⟨anti h2 hb, anti h1 hb⟩

end Real

end MachLib
