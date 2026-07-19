import MachLib.AsinTaylorRemainder

/-!
# `arccos` Taylor-remainder bound — a one-line corollary of `arcsin`'s

`eml_acos.v` computes `acos(x) = π/2 - asin(x)` directly (the RTL's own comment), using the
IDENTICAL 4-term `asin` Taylor series. Rather than re-deriving the whole 8-level `h`-power
derivative chain with flipped signs, this file proves the identity `arccos x = π/2 − arcsin x`
ONCE (from the axioms `arccos_zero`/`arcsin_zero` giving equality at `0`, plus `HasDerivAt_arccos`
being literally `-HasDerivAt_arcsin` giving equality of derivatives everywhere on `abs x < 1`, so
the difference has zero derivative and is zero at `0`, hence zero everywhere via
`abs_mvt_step_bounded` with bound `0`) — after which `Racos0`'s bound is a direct corollary of
`Rasin0_bound`, no new derivative machinery needed at all.
-/

namespace MachLib.Real

theorem eq_zero_of_abs_le_zero {a : Real} (h : abs a ≤ 0) : a = 0 := by
  have h1 : a ≤ 0 := le_trans (le_abs_self a) h
  have h2 : -a ≤ 0 := le_trans (neg_le_abs a) h
  have h3 : 0 ≤ a := by
    have h4 := neg_le_neg h2
    rwa [neg_neg_helper, neg_zero] at h4
  exact le_antisymm h1 h3

/-- **The key identity**: `arccos x = π/2 − arcsin x` for `abs x < 1`. Not assumed elsewhere in
`MachLib` (`InverseTrig.lean` deliberately keeps `arccos`/`arcsin` as independent primitives) —
proved here from the shared value at `0` and the shared (negated) derivative. -/
theorem arccos_eq_half_pi_sub_arcsin {x : Real} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    arccos x = pi / (1 + 1) - arcsin x := by
  have hDelta0 : arccos 0 - (pi / (1 + 1) - arcsin 0) = 0 := by
    rw [arccos_zero, arcsin_zero]; mach_ring
  have hderiv : ∀ c : Real, 0 ≤ c → c < 1 →
      HasDerivAt (fun y => arccos y - (pi / (1 + 1) - arcsin y)) 0 c := by
    intro c hc0 hc1
    have habs : abs c < 1 := by rw [abs_of_nonneg hc0]; exact hc1
    have h1 := HasDerivAt_arccos c habs
    have h2 := HasDerivAt_arcsin c habs
    have h3 := HasDerivAt_sub (fun _ => pi / (1 + 1)) arcsin 0 (1 / sqrt (1 - c * c)) c
      (HasDerivAt_const (pi / (1 + 1)) c) h2
    have h4 := HasDerivAt_sub arccos (fun y => pi / (1 + 1) - arcsin y)
      (-(1 / sqrt (1 - c * c))) (0 - 1 / sqrt (1 - c * c)) c h1 h3
    refine hasDerivAt_congr_val h4 ?_
    mach_ring
  have hbound := abs_mvt_step_bounded (fun y => arccos y - (pi / (1 + 1) - arcsin y))
    (fun _ => (0 : Real)) x 0 1 hx0 hx1 (le_refl 0) hderiv hDelta0
    (fun _ _ _ => by rw [abs_zero]; exact le_refl 0)
  rw [zero_mul] at hbound
  have hz : arccos x - (pi / (1 + 1) - arcsin x) = 0 := eq_zero_of_abs_le_zero hbound
  have hz2 : arccos x = pi / (1 + 1) - arcsin x + (arccos x - (pi / (1 + 1) - arcsin x)) := by
    mach_ring
  rwa [hz, add_zero] at hz2

/-- **THE TARGET**: `Racos0(y) := arccos(y) − (π/2 − (y + y³/6 + 3y⁵/40 + 15y⁷/336))`, exactly
`eml_acos.v`'s claimed computation, subtracted from the true `arccos`. -/
noncomputable def Racos0 (y : Real) : Real :=
  arccos y - (pi / (1 + 1) - (y + y * y * y * (1 / natCast 6)
    + natCast 3 * (1 / natCast 40) * (y * y * y * y * y)
    + natCast 15 * (1 / natCast 336) * (y * y * y * y * y * y * y)))

theorem Racos0_eq_neg_Rasin0 {y : Real} (hy0 : 0 ≤ y) (hy1 : y < 1) : Racos0 y = -Rasin0 y := by
  unfold Racos0 Rasin0
  rw [arccos_eq_half_pi_sub_arcsin hy0 hy1]
  mach_mpoly [y, arcsin y, natCast 3, natCast 15, (1 / natCast 6 : Real),
    (1 / natCast 40 : Real), (1 / natCast 336 : Real), pi]

theorem Racos0_bound (x : Real) (hx0 : 0 ≤ x) (hxR : x ≤ asinR) :
    abs (Racos0 x) ≤ NTop * hAsinPow 15 asinR * x * x * x * x * x * x * x * x := by
  rw [Racos0_eq_neg_Rasin0 hx0 (lt_of_le_of_lt hxR asinR_lt_one), abs_neg]
  exact Rasin0_bound x hx0 hxR

end MachLib.Real
