import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.MPolyRing
import MachLib.FPModel
import MachLib.Iteration
import MachLib.ErrorAlgebra

/-!
# True forward-error algebra (two-sided)

`ErrorAlgebra`'s `mul_grow`/`add_grow` bound the **magnitude** of a computed value
(`|v| ≤ (1+w)^d·F`) — the upper half only. The *forward error* `|v − ve|` needs
the **two-sided** enclosure (FPModel's `length_sq*_fwd_error` use exactly this).
This file supplies it, so the certifier emits genuine forward-error bounds
matching FPModel and unifying with the transcendental rules (`exp_grow` etc.,
which already bound `|v − ve|`).

`Renc d w v ve` ("relative enclosure"): for nonneg exact `ve`,
`(1−w)^d·ve ≤ v ≤ (1+w)^d·ve`. It composes (`renc_mul`, `renc_add`) and yields
the forward error `|v − ve| ≤ ((1+w)^d − 1)·ve` (`renc_fwd`). `sorryAx`-free.
-/

namespace MachLib.Real

/-- Two-sided relative enclosure of computed `v` around nonneg exact `ve`. -/
def Renc (d : Nat) (w v ve : Real) : Prop :=
  npow d (1 - w) * ve ≤ v ∧ v ≤ npow d (1 + w) * ve

/-! fresh-var ring identities (recursion-bound `npow d _` / obtain'd `δ` terms
can't go through `mach_mpoly`'s atom parser directly). -/
theorem fe_sub (P ve : Real) : P * ve - ve = (P - 1) * ve := by mach_mpoly [P, ve]
theorem fe_sub2 (P ve : Real) : ve - P * ve = (1 - P) * ve := by mach_mpoly [P, ve]
theorem fe_key (w A B : Real) :
    (1 - w) * A + (1 + w) * B = (A + B) + w * (B - A) := by mach_mpoly [w, A, B]
theorem fe_mul4 (a b c d : Real) : (a * b) * (c * d) = (a * c) * (b * d) := by
  mach_mpoly [a, b, c, d]
theorem fe_comm (a t : Real) : (1 + t) * a = a * (1 + t) := by mach_mpoly [a, t]
theorem fe_rearr (P Q R : Real) : (P * Q) * R = (R * P) * Q := by mach_mpoly [P, Q, R]
theorem fe_negsub (a b : Real) : -(a - b) = b - a := by mach_mpoly [a, b]
theorem fe_lower {A B : Real} (h : 1 + 1 ≤ A + B) : 1 - A ≤ B - 1 := by
  have h0 : 0 ≤ (A + B) - (1 + 1) := sub_nonneg_of_le h
  have e : (A + B) - (1 + 1) = (B - 1) - (1 - A) := by mach_mpoly [A, B]
  rw [e] at h0; exact le_of_sub_nonneg h0

/-- `npow` monotone in the **base** (both nonneg). -/
theorem npow_base_mono {a b : Real} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ d, npow d a ≤ npow d b
  | 0     => le_refl _
  | d + 1 => by
      rw [npow_succ, npow_succ]
      exact le_trans (mul_le_mul_of_nonneg_right hab (npow_nonneg ha d))
                     (mul_le_mul_of_nonneg_left (npow_base_mono ha hab d) (le_trans ha hab))

/-- `(1−w)^d + (1+w)^d ≥ 2` — the convexity fact that puts the lower error side
under the `(1+w)^d − 1` bound. -/
theorem two_le_pow_sum {w : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    ∀ d, (1 : Real) + 1 ≤ npow d (1 - w) + npow d (1 + w)
  | 0     => le_refl _
  | d + 1 => by
      rw [npow_succ, npow_succ, fe_key w (npow d (1 - w)) (npow d (1 + w))]
      have hle : 1 - w ≤ 1 + w := by
        have e : (1 + w) - (1 - w) = w + w := by mach_ring
        exact le_of_sub_nonneg (e ▸ add_nonneg_ea hw0 hw0)
      have hAB : npow d (1 - w) ≤ npow d (1 + w) :=
        npow_base_mono (sub_nonneg_of_le hw1) hle d
      exact le_trans (two_le_pow_sum hw0 hw1 d)
        (le_add_of_nonneg_right (mul_nonneg hw0 (sub_nonneg_of_le hAB)))

/-- Leaf: an exact nonneg input encloses itself at exponent 0. -/
theorem renc_leaf {w x : Real} (hx : 0 ≤ x) : Renc 0 w x x := by
  have e1 : npow 0 (1 - w) * x = x := by
    rw [show npow 0 (1 - w) = 1 from rfl]; exact one_mul_thm x
  have e2 : npow 0 (1 + w) * x = x := by
    rw [show npow 0 (1 + w) = 1 from rfl]; exact one_mul_thm x
  exact ⟨le_of_eq e1, le_of_eq e2.symm⟩

/-- **Product** composition: exponents add (`a + b + 1`). -/
theorem renc_mul {w x y p xe ye : Real} {a b : Nat}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hxe : 0 ≤ xe) (hye : 0 ≤ ye)
    (hx : Renc a w x xe) (hy : Renc b w y ye)
    (hp : RoundsW w p (x * y)) :
    Renc (a + b + 1) w p (xe * ye) := by
  obtain ⟨hxl, hxu⟩ := hx; obtain ⟨hyl, hyu⟩ := hy
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  have h1w_nn  : 0 ≤ 1 - w := sub_nonneg_of_le hw1
  have h1w'_nn : 0 ≤ 1 + w := le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw0)
  have hyb_nn  : 0 ≤ npow b (1 - w) * ye := mul_nonneg (npow_nonneg h1w_nn b) hye
  have hxa'_nn : 0 ≤ npow a (1 + w) * xe := mul_nonneg (npow_nonneg h1w'_nn a) hxe
  have hx_nn : 0 ≤ x := le_trans (mul_nonneg (npow_nonneg h1w_nn a) hxe) hxl
  have hy_nn : 0 ≤ y := le_trans hyb_nn hyl
  have hxy_nn : 0 ≤ x * y := mul_nonneg hx_nn hy_nn
  have hd_lo : 1 - w ≤ 1 + δ := by
    have h := add_le_add_left hδl 1; rwa [show (1 : Real) + (-w) = 1 - w from by mach_ring] at h
  have hd_up : 1 + δ ≤ 1 + w := add_le_add_left hδu 1
  have ep : (1 + δ) * (x * y) = p := by rw [hpeq]; exact fe_comm (x * y) δ
  constructor
  · have hl2 : npow (a + b) (1 - w) * (xe * ye) ≤ x * y := by
      have hl1 : (npow a (1 - w) * xe) * (npow b (1 - w) * ye) ≤ x * y :=
        le_trans (mul_le_mul_of_nonneg_right hxl hyb_nn)
                 (mul_le_mul_of_nonneg_left hyl hx_nn)
      rwa [fe_mul4 (npow a (1 - w)) xe (npow b (1 - w)) ye, ← npow_add (1 - w) a b] at hl1
    have e : npow (a + b + 1) (1 - w) * (xe * ye)
        = (1 - w) * (npow (a + b) (1 - w) * (xe * ye)) := by
      rw [npow_succ]; exact (ea_assoc3 (1 - w) (npow (a + b) (1 - w)) (xe * ye)).symm
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_left hl2 h1w_nn)
            (le_trans (mul_le_mul_of_nonneg_right hd_lo hxy_nn) (le_of_eq ep))
  · have hu2 : x * y ≤ npow (a + b) (1 + w) * (xe * ye) := by
      have hu1 : x * y ≤ (npow a (1 + w) * xe) * (npow b (1 + w) * ye) :=
        le_trans (mul_le_mul_of_nonneg_right hxu hy_nn)
                 (mul_le_mul_of_nonneg_left hyu hxa'_nn)
      rwa [fe_mul4 (npow a (1 + w)) xe (npow b (1 + w)) ye, ← npow_add (1 + w) a b] at hu1
    have hp1 : p ≤ (x * y) * (1 + w) := by
      rw [hpeq]; exact mul_le_mul_of_nonneg_left hd_up hxy_nn
    have eU : (npow (a + b) (1 + w) * (xe * ye)) * (1 + w)
        = npow (a + b + 1) (1 + w) * (xe * ye) := by
      rw [npow_succ]; exact fe_rearr (npow (a + b) (1 + w)) (xe * ye) (1 + w)
    exact le_trans hp1 (le_trans (mul_le_mul_of_nonneg_right hu2 h1w'_nn) (le_of_eq eU))

/-- **Sum** composition (common exponent `a`): exponent `a + 1` (no compounding). -/
theorem renc_add {w x y p xe ye : Real} {a : Nat}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hxe : 0 ≤ xe) (hye : 0 ≤ ye)
    (hx : Renc a w x xe) (hy : Renc a w y ye)
    (hp : RoundsW w p (x + y)) :
    Renc (a + 1) w p (xe + ye) := by
  obtain ⟨hxl, hxu⟩ := hx; obtain ⟨hyl, hyu⟩ := hy
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  have h1w_nn  : 0 ≤ 1 - w := sub_nonneg_of_le hw1
  have h1w'_nn : 0 ≤ 1 + w := le_trans (le_of_lt one_pos) (le_add_of_nonneg_right hw0)
  have hx_nn : 0 ≤ x := le_trans (mul_nonneg (npow_nonneg h1w_nn a) hxe) hxl
  have hy_nn : 0 ≤ y := le_trans (mul_nonneg (npow_nonneg h1w_nn a) hye) hyl
  have hxy_nn : 0 ≤ x + y := add_nonneg_ea hx_nn hy_nn
  have hd_lo : 1 - w ≤ 1 + δ := by
    have h := add_le_add_left hδl 1; rwa [show (1 : Real) + (-w) = 1 - w from by mach_ring] at h
  have hd_up : 1 + δ ≤ 1 + w := add_le_add_left hδu 1
  have ep : (1 + δ) * (x + y) = p := by rw [hpeq]; exact fe_comm (x + y) δ
  constructor
  · have hs : npow a (1 - w) * (xe + ye) ≤ x + y := by
      have h := add_le_add_both hxl hyl
      rwa [ea_distrib (npow a (1 - w)) xe ye] at h
    have e : npow (a + 1) (1 - w) * (xe + ye)
        = (1 - w) * (npow a (1 - w) * (xe + ye)) := by
      rw [npow_succ]; exact (ea_assoc3 (1 - w) (npow a (1 - w)) (xe + ye)).symm
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_left hs h1w_nn)
            (le_trans (mul_le_mul_of_nonneg_right hd_lo hxy_nn) (le_of_eq ep))
  · have hs : x + y ≤ npow a (1 + w) * (xe + ye) := by
      have h := add_le_add_both hxu hyu
      rwa [ea_distrib (npow a (1 + w)) xe ye] at h
    have hp1 : p ≤ (x + y) * (1 + w) := by
      rw [hpeq]; exact mul_le_mul_of_nonneg_left hd_up hxy_nn
    have eU : (npow a (1 + w) * (xe + ye)) * (1 + w)
        = npow (a + 1) (1 + w) * (xe + ye) := by
      rw [npow_succ]; exact fe_rearr (npow a (1 + w)) (xe + ye) (1 + w)
    exact le_trans hp1 (le_trans (mul_le_mul_of_nonneg_right hs h1w'_nn) (le_of_eq eU))

/-- **The forward error.** A two-sided enclosure at exponent `d` gives the
relative forward-error bound `|v − ve| ≤ ((1+w)^d − 1)·ve` — the true
`*_fwd_error` shape (FPModel), assembled compositionally. -/
theorem renc_fwd {w v ve : Real} {d : Nat}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hve : 0 ≤ ve) (h : Renc d w v ve) :
    abs (v - ve) ≤ (npow d (1 + w) - 1) * ve := by
  obtain ⟨hl, hu⟩ := h
  apply abs_le_of
  · rw [← fe_sub (npow d (1 + w)) ve]; exact sub_le_sub_right hu ve
  · rw [fe_negsub v ve]
    have h2 : ve - v ≤ (1 - npow d (1 - w)) * ve := by
      rw [← fe_sub2 (npow d (1 - w)) ve]; exact sub_le_sub_left hl ve
    refine le_trans h2 (mul_le_mul_of_nonneg_right (fe_lower (two_le_pow_sum hw0 hw1 d)) hve)

theorem npow_one (x : Real) : npow 1 x = x := by
  rw [npow_succ, show npow 0 x = 1 from rfl]; exact mul_one_ax x

/-- One rounding of a **nonneg** exact value gives a `Renc 1` enclosure. The
right "leaf" for a squared/nonneg term (whose inputs may be negative — only the
term itself is nonneg), avoiding the sign restriction of `renc_mul`. -/
theorem renc_round {w p e : Real} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (he : 0 ≤ e)
    (hp : RoundsW w p e) : Renc 1 w p e := by
  obtain ⟨δ, hδl, hδu, hpeq⟩ := hp
  have hd_lo : 1 - w ≤ 1 + δ := by
    have h := add_le_add_left hδl 1; rwa [show (1 : Real) + (-w) = 1 - w from by mach_ring] at h
  have hd_up : 1 + δ ≤ 1 + w := add_le_add_left hδu 1
  refine ⟨?_, ?_⟩
  · rw [npow_one, hpeq, mul_comm (1 - w) e]; exact mul_le_mul_of_nonneg_left hd_lo he
  · rw [npow_one, hpeq, mul_comm (1 + w) e]; exact mul_le_mul_of_nonneg_left hd_up he

/-- **Worked composition** — `length_sq2` as a TRUE forward error, folding the
two-sided rules `renc_round → renc_add → renc_fwd`. Matches FPModel's
`length_sq2_fwd_error` `|s − exact| ≤ ((1+w)² − 1)·exact`, now assembled from the
operator algebra — the genuine forward-error result that
`ErrorAlgebra.length_sq2_compose` (magnitude only) did NOT prove. Each `x*x` is a
nonneg rounded term (`renc_round`), so the inputs `x,y` may be any sign. -/
theorem length_sq2_fwd_compose {w x y px py s : Real}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hpy : RoundsW w py (y * y))
    (hs : RoundsW w s (px + py)) :
    abs (s - (x * x + y * y)) ≤ (npow 2 (1 + w) - 1) * (x * x + y * y) :=
  renc_fwd hw0 hw1 (add_nonneg_ea (mul_self_nonneg x) (mul_self_nonneg y))
    (renc_add hw0 hw1 (mul_self_nonneg x) (mul_self_nonneg y)
      (renc_round hw0 hw1 (mul_self_nonneg x) hpx)
      (renc_round hw0 hw1 (mul_self_nonneg y) hpy) hs)

end MachLib.Real
