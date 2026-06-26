import MachLib.Basic
import MachLib.Trig
import MachLib.Forge
import MachLib.Ring
import MachLib.Linarith
import MachLib.MPolyRing

/-
MachLib.Decompose — reusable "decompose before nlinarith" lemmas.

Doctrine (learned closing the monogate-engine obligation bundle, 2026-06-25):
most ordered-field bounds that *look* like they need `nlinarith` close with an
existing lemma once you pick the right algebraic decomposition. These four are
the patterns that recurred — promoted from hand-written per-file helpers to named
primitives so the next obligation (and the eml-stdlib sweep) reuses them:

  * `abs_le_sqrt`        — `v² ≤ y ⇒ |v| ≤ √y`             (normalise-by-√ shapes)
  * `mul_mem_symm_band`  — `|w| ≤ 1, 0 ≤ L ⇒ L·w ∈ [−L,L]` (scaled-bound closers)
  * `lerp_le_of_le`      — convex interpolant ≤ common upper bound (smin/clamp)
  * `quad_denom_pos`     — `0 < 1 + a² − 2ab` via sign-split (Mie/HG/rotation)

The collecting algebra inside each (e.g. `M − lerp = (M−b)(1−β)+(M−a)β`) is closed
by `mach_mpoly` (ring-v3), which `mach_ring` cannot do.
-/

namespace MachLib.Real

/-- **sqrt bound from a square bound.** `v² ≤ y ⇒ |v| ≤ √y` (both arms).
The workhorse behind every "normalise by `x/√(x²+ε)`" obligation (IK, etc.). -/
theorem abs_le_sqrt {v y : Real} (hsq : v * v ≤ y) :
    v ≤ sqrt y ∧ -v ≤ sqrt y := by
  refine ⟨?_, ?_⟩
  · rcases lt_total 0 v with h | h | h
    · exact le_sqrt_of_sq_le (le_of_lt h) hsq
    · exact le_sqrt_of_sq_le ((le_iff_lt_or_eq _ _).mpr (Or.inr h)) hsq
    · exact le_trans (le_of_lt h) (sqrt_nonneg _)
  · rcases lt_total 0 (-v) with h | h | h
    · exact le_sqrt_of_sq_le (le_of_lt h) (by rw [neg_mul_neg]; exact hsq)
    · exact le_sqrt_of_sq_le ((le_iff_lt_or_eq _ _).mpr (Or.inr h)) (by rw [neg_mul_neg]; exact hsq)
    · exact le_trans (le_of_lt h) (sqrt_nonneg _)

/-- **Symmetric band under scaling.** `|w| ≤ 1, 0 ≤ L ⇒ L·w ∈ [−L, L]`.
The closer for `length · (bounded) ∈ [−length, length]` shapes. -/
theorem mul_mem_symm_band {L w : Real} (hL : 0 ≤ L) (hlo : -1 ≤ w) (hhi : w ≤ 1) :
    -L ≤ L * w ∧ L * w ≤ L := by
  refine ⟨?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hlo hL
    rw [show L * (-1) = -L from by mach_ring] at h; exact h
  · have h := mul_le_mul_of_nonneg_left hhi hL
    rw [mul_one_ax] at h; exact h

/-- **Convex/lerp upper bound.** For `β ∈ [0,1]`, the interpolant
`b + (a−b)·β` stays ≤ any common upper bound of `a` and `b`. Proven by the
SOS split `M − lerp = (M−b)(1−β) + (M−a)β`. The smin-bound workhorse. -/
theorem lerp_le_of_le {a b M β : Real} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (ha : a ≤ M) (hb : b ≤ M) : b + (a - b) * β ≤ M :=
  le_of_sub_nonneg (by
    rw [show M - (b + (a - b) * β) = (M - b) * (1 - β) + (M - a) * β from by mach_mpoly [a, b, M, β]]
    exact add_nonneg (mul_nonneg (sub_nonneg_of_le hb) (sub_nonneg_of_le hβ1))
                     (mul_nonneg (sub_nonneg_of_le ha) hβ0))

/-- **Sign-split denominator positivity.** `0 < 1 + a² − 2ab` for
`a ∈ (−1,1)`, `b ∈ [−1,1]` — the Mie/Henyey-Greenstein/rotation denominator.
Avoids Cauchy-Schwarz entirely: split on `sign a` and write the quadratic as a
strictly-positive square plus a nonneg term. -/
theorem quad_denom_pos {a b : Real} (ha : -1 < a) (ha' : a < 1)
    (hb : -1 ≤ b) (hb' : b ≤ 1) : 0 < 1 + a * a - (1 + 1) * a * b := by
  have h1pa : (0 : Real) < 1 + a := by
    rw [show (1 : Real) + a = a - -1 from by mach_mpoly [a]]; exact sub_pos_of_lt ha
  rcases lt_total 0 a with hpos | hz | hneg
  · rw [show 1 + a * a - (1 + 1) * a * b = (1 - a) * (1 - a) + (1 + 1) * a * (1 - b) from by mach_mpoly [a, b]]
    exact lt_of_lt_of_le (mul_pos (sub_pos_of_lt ha') (sub_pos_of_lt ha'))
      (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by mach_positivity) (le_of_lt hpos)) (sub_nonneg_of_le hb')))
  · rw [← hz, show 1 + (0 : Real) * 0 - (1 + 1) * 0 * b = 1 from by mach_mpoly [b]]; exact zero_lt_one_ax
  · rw [show 1 + a * a - (1 + 1) * a * b = (1 + a) * (1 + a) + (1 + 1) * (-a) * (1 + b) from by mach_mpoly [a, b]]
    have h1pb : (0 : Real) ≤ 1 + b := by
      have := sub_nonneg_of_le hb; rw [show b - -1 = 1 + b from by mach_mpoly [b]] at this; exact this
    exact lt_of_lt_of_le (mul_pos h1pa h1pa)
      (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by mach_positivity) (le_of_lt (neg_pos_of_neg hneg))) h1pb))

end MachLib.Real
