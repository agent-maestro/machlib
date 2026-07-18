import MachLib.SinTaylorRemainder
import MachLib.CosTaylorRemainder
import MachLib.TanLipschitz
import MachLib.NatCastArith

/-!
# `tan` Taylor-remainder bound — COMPLETE, `sorryAx`-free, after a real tooling wall got fixed

`eml_tan.v` computes the 4-term Maclaurin truncation `tan(x) ≈ x + x³/3 + 2x⁵/15 + 17x⁷/315`.
Unlike `sin/cos/sinh/cosh` (whose derivatives cycle back to themselves after a few steps,
making the remainder chain bottom out cleanly), `tan' = sec² = 1+tan²` means every derivative of
`tan` is a HIGHER-DEGREE polynomial in `tan` itself — the chain never closes. Differentiating by
hand (`T := tan y`, `S := 1+T² = sec² y`, so `T' = S`):

`g0=T`, `g1=1+T²`, `g2=2T+2T³`, `g3=2+8T²+6T⁴`, `g4=16T+40T³+24T⁵`,
`g5=16+136T²+240T⁴+120T⁶`, `g6=272T+1232T³+1680T⁵+720T⁷`,
`g7=272+3968T²+12096T⁴+13440T⁶+5040T⁸`, `g8=7936T+56320T³+129024T⁵+120960T⁷+40320T⁹` — each
obtained from the last via `(⋯)' = (⋯)·T' = (⋯)(1+T²)`, confirmed against the known Maclaurin
coefficients of `tan` (`g_{2k-1}(0)/(2k-1)!` reproduces `1, 1/3, 2/15, 17/315`). This needed
**8 MVT levels** (`Rtan0..Rtan7`, vs sin's 6, named with the `Rtan` prefix to avoid colliding with
`SinTaylorRemainder`'s own `R0..R5`) — genuinely harder math than sin/sinh, now fully closed.

**THE MAIN RESULT — `Rtan0_bound`**:
`|tan(x) − (x + x³/3 + (2/15)x⁵ + (17/315)x⁷)| ≤ 354560 · Mtan(x)^9 · x^8` for `x ∈ [0,1]`,
where `Mtan(x) := 1 + tan(x)`. `sorryAx`-free, standard axiom footprint (no new axioms — just the
pre-existing `pi`/`pythagorean`/`rolle_ct`/`tan_def`/`sin_pos_of_pos_lt_pi_div_two` this whole
arc already rests on). Full project `lake build` (376 files) green.

**Why this was blockable at all, and how it got unblocked** (kept for the historical record —
see [[project_natcast_arith_infrastructure]] and [[feedback_machlib_mach_ring_numeral_scale_wall]]
in the agent's memory for the full empirical writeup). The chain needs coefficients in the
thousands (3968, 12096, 13440, 5040, `g8`'s 40320/129024). Represented the OLD way (flat sums of
`1+1+1+...`, the `sevenhundredtwenty := six*onetwenty` pattern `sin`/`cos` used), `mach_ring` hits
`maximum recursion depth`/kernel deep-recursion trying to verify even one sum-of-products identity
at this scale — not a `maxRecDepth` budget problem, and not specific to collecting like terms
either. **The fix**: `MachLib.Decimal` already had `natCast_add`/`natCast_mul` (proven by induction
on `natCast_succ` for the decimal-literal evaluator, not by ring-normalizing a flat sum) — routing
every large coefficient through `natCast N` (a literal `Nat`, Lean 4's kernel handles these fast
regardless of size) instead of a flat sum sidesteps the wall entirely (`MachLib.NatCastArith`).
Fraction coefficients (`tan`'s own `1/3, 2/15, 17/315`, and intermediate fractions like `170/15`,
`102/45` that appear mid-derivation before reducing) needed two further general helpers built here
— `natCast_frac_to_nat` (fraction → whole number) and `natCast_frac_eq` (fraction → a *different*
reduced fraction, via cross-multiplication) — both proven once, reused throughout the chain.

**Method notes for the chain itself**: `Mtan(x) := 1+tan(x)` plays the same role `sinh(x)` played
for `sinh`/`cosh` — a single growing, `≥1` quantity that bounds both `tan(t)` and `t` itself, so
every level's `_bound` proof (`RtanK_bound`) is a simple propagation from `Rtan(K+1)_bound`
(`Base1_mono .. Base7_mono`), exactly mirroring `SinhTaylorRemainder`. The one place needing real
multi-term triangle-inequality work is `g8_bound` (`Rtan7`'s own derivative) — every other level's
bound is a one-line reuse of the previous level's.
-/

namespace MachLib.Real

/-! ## `tan` monotonicity on `[0, π/2)` — not yet in `MachLib`, derived via MVT (same technique as
`sinh_mono`/`cosh_mono`), needed to bound `tan(t) ≤ tan(x)` for `t ≤ x` throughout the chain. -/

theorem tan_mono {a b : Real} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb : b < pi / (1 + 1)) :
    tan a ≤ tan b := by
  have hbound : ∀ c : Real, a ≤ c → c ≤ b → abs c < pi / (1 + 1) := by
    intro c hac hcb
    rw [abs_of_nonneg (le_trans ha0 hac)]
    exact lt_of_le_of_lt hcb hb
  rcases lt_total a b with h | h | h
  · obtain ⟨c, f', hac, hcb, hdc, hval⟩ :=
      mean_value_theorem_ct tan a b h
        (fun c hac' hcb' => ⟨1 / (cos c * cos c), HasDerivAt_tan (hbound c hac' hcb')⟩)
    rw [HasDerivAt_unique tan f' (1 / (cos c * cos c)) c hdc
      (HasDerivAt_tan (hbound c (le_of_lt hac) (le_of_lt hcb)))] at hval
    refine le_of_sub_nonneg (hval ▸ mul_nonneg ?_ (le_of_lt (sub_pos_of_lt h)))
    exact one_div_nonneg_of_pos
      (mul_pos (cos_pos_of_abs_lt_pi_div_two (hbound c (le_of_lt hac) (le_of_lt hcb)))
        (cos_pos_of_abs_lt_pi_div_two (hbound c (le_of_lt hac) (le_of_lt hcb))))
  · exact le_of_eq (congrArg tan h)
  · exact absurd (lt_of_lt_of_le h hab) (lt_irrefl_ax b)

theorem tan_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) : 0 ≤ tan x := by
  have := tan_mono (le_refl 0) hx0 hx; rwa [tan_zero] at this

/-- `1 < π/2`, from `pi_gt_three : 3 < pi`. Certified domain `x ≤ 1` stays inside `tan`'s
differentiable range. -/
theorem one_lt_pi_div_two : (1 : Real) < pi / (1 + 1) := by
  have hval : (1 + 1 + 1 : Real) * (1 / (1 + 1)) = 1 + 1 / (1 + 1) := by
    rw [show (1 + 1 + 1 : Real) = (1 + 1) + 1 from by mach_ring,
      show ((1 + 1 : Real) + 1) * (1 / (1 + 1)) = (1 + 1) * (1 / (1 + 1)) + 1 * (1 / (1 + 1))
        from by mach_ring,
      mul_inv (1 + 1) my_two_ne_zero, one_mul_thm]
  have hge : (1 : Real) ≤ (1 + 1 + 1) * (1 / (1 + 1)) := by
    rw [hval]
    have := le_add_of_nonneg_right (one_div_nonneg_of_pos my_two_pos) (a := (1 : Real))
    exact this
  have hlt : (1 + 1 + 1 : Real) * (1 / (1 + 1)) < pi * (1 / (1 + 1)) :=
    mul_lt_mul_of_pos_right pi_gt_three (one_div_pos_of_pos my_two_pos)
  rw [div_def pi (1 + 1) my_two_ne_zero]
  exact lt_of_le_of_lt hge hlt

/-! ## Shared chain infrastructure

`abs_mvt_step` (`SinTaylorRemainder`) demands `∀c, HasDerivAt f (g c) c` UNCONDITIONALLY — fine for
`sin/cos/sinh/cosh` (defined everywhere) but `HasDerivAt_tan` only holds where `abs c < π/2`. This
domain-restricted variant is `abs_mvt_step`'s proof verbatim with that one hypothesis threaded
through. `Mtan(x) := 1 + tan(x)` plays the role `sinh(x)` played for `sinh`/`cosh`: a SINGLE growing
quantity (`Mtan(t) ≤ Mtan(x)` for `t≤x`, from `tan_mono`) that's also `≥ 1` for `x≥0` — which lets
BOTH `tan(t)` and `t` itself (on the certified `[0,1]` domain) be bounded by it, and lets any lower
power of it be "bumped" up to a fixed higher power via `le_mul_self_of_ge_one`. This collapses the
whole 8-level chain's bound-propagation to the exact same shape `SinhTaylorRemainder` used. -/

theorem abs_mvt_step_bounded (f g : Real → Real) (x B R : Real) (hx0 : 0 ≤ x) (hxR : x < R)
    (hB : 0 ≤ B) (hderiv : ∀ c : Real, 0 ≤ c → c < R → HasDerivAt f (g c) c) (hf0 : f 0 = 0)
    (hgB : ∀ t : Real, 0 ≤ t → t ≤ x → abs (g t) ≤ B) : abs (f x) ≤ B * x := by
  rcases (le_iff_lt_or_eq 0 x).mp hx0 with hlt | heq
  · obtain ⟨c, f', hac, hcb, hd, hval⟩ :=
      mean_value_theorem_ct f 0 x hlt
        (fun c hac hcb => ⟨g c, hderiv c hac (lt_of_le_of_lt hcb hxR)⟩)
    rw [HasDerivAt_unique f f' (g c) c hd (hderiv c (le_of_lt hac) (lt_trans_ax hcb hxR))] at hval
    rw [hf0, sub_zero, sub_zero] at hval
    have hstep : abs (f x) = abs (g c) * x := by rw [hval, abs_mul, abs_of_nonneg hx0]
    rw [hstep]
    have h1 : abs (g c) ≤ B := hgB c (le_of_lt hac) (le_of_lt hcb)
    exact mul_le_mul_of_nonneg_right h1 hx0
  · have hx0' : x = 0 := heq.symm
    rw [hx0', show f 0 = 0 from hf0, abs_zero, mul_zero]
    exact le_refl 0

/-- `b ≤ b * a` whenever `a ≥ 1`, `b ≥ 0` — the one generic fact needed to "bump" a lower power of
`Mtan` up to a fixed higher one (`Mtan(x)^k ≤ Mtan(x)^k * Mtan(x) = Mtan(x)^{k+1}`). -/
theorem le_mul_self_of_ge_one {a b : Real} (ha : 1 ≤ a) (hb0 : 0 ≤ b) : b ≤ b * a := by
  have h := mul_le_mul_of_nonneg_left ha hb0
  rwa [mul_one_ax] at h

/-- `Mtan(x) := 1 + tan(x)` — the single growing quantity for the whole chain. -/
noncomputable def Mtan (x : Real) : Real := 1 + tan x

theorem Mtan_ge_one {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) : 1 ≤ Mtan x := by
  unfold Mtan
  have := tan_nonneg hx0 hx
  exact le_add_of_nonneg_right this

theorem Mtan_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    Mtan t ≤ Mtan x := by
  unfold Mtan
  exact add_le_add_both (le_refl 1) (tan_mono ht0 htx hx)

/-- `tan(t) ≤ Mtan(t)`, trivially (`1 + tan t ≥ tan t` since `1 ≥ 0`). -/
theorem T_le_Mtan (t : Real) : tan t ≤ Mtan t := by
  unfold Mtan
  have h : tan t + 0 ≤ tan t + 1 := add_le_add_both (le_refl (tan t)) (le_of_lt zero_lt_one_ax)
  rwa [add_zero, add_comm (tan t) 1] at h

/-- `t ≤ Mtan(t)` on the certified domain `t ≤ 1` (since `1 ≤ Mtan(t)` always, for `t ≥ 0`). -/
theorem y_le_Mtan {t : Real} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htR : t < pi / (1 + 1)) :
    t ≤ Mtan t := le_trans ht1 (Mtan_ge_one ht0 htR)

theorem Mtan_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) : 0 ≤ Mtan x :=
  le_trans (le_of_lt zero_lt_one_ax) (Mtan_ge_one hx0 hx)

/-! ## `g8` — `tan`'s 8th derivative, `Rtan7`'s own derivative — the ONE place needing multi-term
triangle-inequality decomposition. Every level from `Rtan7` down to `R0` just propagates a bound
already in `C * Mtan(x)^n` form (exactly like `SinhTaylorRemainder`), so this is the only spot
that needs to bound several different powers of `tan` at once. -/

noncomputable def g8 (y : Real) : Real :=
  natCast 7936 * tan y + natCast 56320 * (tan y * tan y * tan y)
    + natCast 129024 * (tan y * tan y * tan y * tan y * tan y)
    + natCast 120960 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y)
    + natCast 40320
      * (tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y)

/-- `|g8(t)| ≤ 354560 · Mtan(x)^9` for `t ∈ [0,x]`, `x < π/2` — bounds every power of `tan(t)`
appearing in `g8` (odd powers 1..9) by the SAME `Mtan(x)^9` via `tan(t) ≤ Mtan(x)` (monotonicity)
then a degree bump (`Mtan(x) ≥ 1`), then combines the five coefficients via `natCast_add`. -/
theorem g8_bound (t x : Real) (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    abs (g8 t) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) := by
  have hx0 : 0 ≤ x := le_trans ht0 htx
  have hTnn : 0 ≤ tan t := tan_nonneg ht0 (lt_of_le_of_lt htx hx)
  have hMnn : 0 ≤ Mtan x := Mtan_nonneg hx0 hx
  have hMge1 : 1 ≤ Mtan x := Mtan_ge_one hx0 hx
  have hTle : tan t ≤ Mtan x := le_trans (T_le_Mtan t) (Mtan_mono ht0 htx hx)
  -- tan(t)^k ≤ Mtan(x)^k and nonnegativity of each side, k=2..9 (left-associated products).
  have Tnn2 : 0 ≤ tan t * tan t := mul_nonneg hTnn hTnn
  have Mnn2 : 0 ≤ Mtan x * Mtan x := mul_nonneg hMnn hMnn
  have d2 : tan t * tan t ≤ Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right hTle hTnn) (mul_le_mul_of_nonneg_left hTle hMnn)
  have Tnn3 : 0 ≤ tan t * tan t * tan t := mul_nonneg Tnn2 hTnn
  have Mnn3 : 0 ≤ Mtan x * Mtan x * Mtan x := mul_nonneg Mnn2 hMnn
  have d3 : tan t * tan t * tan t ≤ Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d2 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn2)
  have Tnn4 : 0 ≤ tan t * tan t * tan t * tan t := mul_nonneg Tnn3 hTnn
  have Mnn4 : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x := mul_nonneg Mnn3 hMnn
  have d4 : tan t * tan t * tan t * tan t ≤ Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d3 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn3)
  have Tnn5 : 0 ≤ tan t * tan t * tan t * tan t * tan t := mul_nonneg Tnn4 hTnn
  have Mnn5 : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := mul_nonneg Mnn4 hMnn
  have d5 : tan t * tan t * tan t * tan t * tan t ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d4 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn4)
  have Tnn6 : 0 ≤ tan t * tan t * tan t * tan t * tan t * tan t := mul_nonneg Tnn5 hTnn
  have Mnn6 : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := mul_nonneg Mnn5 hMnn
  have d6 : tan t * tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d5 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn5)
  have Tnn7 : 0 ≤ tan t * tan t * tan t * tan t * tan t * tan t * tan t := mul_nonneg Tnn6 hTnn
  have Mnn7 : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    mul_nonneg Mnn6 hMnn
  have d7 : tan t * tan t * tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d6 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn6)
  have Tnn8 : 0 ≤ tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t :=
    mul_nonneg Tnn7 hTnn
  have Mnn8 : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    mul_nonneg Mnn7 hMnn
  have d8 : tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d7 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn7)
  have Tnn9 : 0 ≤ tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t :=
    mul_nonneg Tnn8 hTnn
  have d9 : tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right d8 hTnn) (mul_le_mul_of_nonneg_left hTle Mnn8)
  -- Bump chain: Mtan(x)^k ≤ Mtan(x)^{k+1} for k=1..8 (Mtan(x) ≥ 1).
  have b1 : Mtan x ≤ Mtan x * Mtan x := le_mul_self_of_ge_one hMge1 hMnn
  have b2 : Mtan x * Mtan x ≤ Mtan x * Mtan x * Mtan x := le_mul_self_of_ge_one hMge1 Mnn2
  have b3 : Mtan x * Mtan x * Mtan x ≤ Mtan x * Mtan x * Mtan x * Mtan x :=
    le_mul_self_of_ge_one hMge1 Mnn3
  have b4 : Mtan x * Mtan x * Mtan x * Mtan x ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_mul_self_of_ge_one hMge1 Mnn4
  have b5 : Mtan x * Mtan x * Mtan x * Mtan x * Mtan x
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := le_mul_self_of_ge_one hMge1 Mnn5
  have b6 : Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_mul_self_of_ge_one hMge1 Mnn6
  have b7 : Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_mul_self_of_ge_one hMge1 Mnn7
  have b8 : Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_mul_self_of_ge_one hMge1 Mnn8
  -- Every needed power of tan(t), bumped up to Mtan(x)^9.
  have T1_le9 : tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans hTle (le_trans b1 (le_trans b2 (le_trans b3 (le_trans b4
      (le_trans b5 (le_trans b6 (le_trans b7 b8)))))))
  have T3_le9 : tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans d3 (le_trans b3 (le_trans b4 (le_trans b5 (le_trans b6 (le_trans b7 b8)))))
  have T5_le9 : tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans d5 (le_trans b5 (le_trans b6 (le_trans b7 b8)))
  have T7_le9 : tan t * tan t * tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans d7 (le_trans b7 b8)
  have T9_le9 : tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := d9
  -- Combine: |g8(t)| ≤ (triangle ineq, 5 terms) ≤ sum-of-coefficients * Mtan(x)^9.
  have hnn7936 : (0 : Real) ≤ natCast 7936 := natCast_nonneg 7936
  have hnn56320 : (0 : Real) ≤ natCast 56320 := natCast_nonneg 56320
  have hnn129024 : (0 : Real) ≤ natCast 129024 := natCast_nonneg 129024
  have hnn120960 : (0 : Real) ≤ natCast 120960 := natCast_nonneg 120960
  have hnn40320 : (0 : Real) ≤ natCast 40320 := natCast_nonneg 40320
  have e1 : abs (natCast 7936 * tan t) ≤ natCast 7936
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) := by
    rw [abs_of_nonneg (mul_nonneg hnn7936 hTnn)]
    exact mul_le_mul_of_nonneg_left T1_le9 hnn7936
  have e2 : abs (natCast 56320 * (tan t * tan t * tan t)) ≤ natCast 56320
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) := by
    rw [abs_of_nonneg (mul_nonneg hnn56320 Tnn3)]
    exact mul_le_mul_of_nonneg_left T3_le9 hnn56320
  have e3 : abs (natCast 129024 * (tan t * tan t * tan t * tan t * tan t)) ≤ natCast 129024
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) := by
    rw [abs_of_nonneg (mul_nonneg hnn129024 Tnn5)]
    exact mul_le_mul_of_nonneg_left T5_le9 hnn129024
  have e4 : abs (natCast 120960
      * (tan t * tan t * tan t * tan t * tan t * tan t * tan t)) ≤ natCast 120960
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) := by
    rw [abs_of_nonneg (mul_nonneg hnn120960 Tnn7)]
    exact mul_le_mul_of_nonneg_left T7_le9 hnn120960
  have e5 : abs (natCast 40320
      * (tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t * tan t)) ≤ natCast 40320
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) := by
    rw [abs_of_nonneg (mul_nonneg hnn40320 Tnn9)]
    exact mul_le_mul_of_nonneg_left T9_le9 hnn40320
  unfold g8
  rw [show natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      = natCast 7936 * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        + natCast 56320 * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        + natCast 129024 * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        + natCast 120960 * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        + natCast 40320 * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      from by
        have hcoef : natCast 354560 = ((((natCast 7936 + natCast 56320) + natCast 129024)
            + natCast 120960) + natCast 40320) := by
          rw [← natCast_add, ← natCast_add, ← natCast_add, ← natCast_add]
        rw [hcoef]; mach_ring]
  refine le_trans (abs_add _ _) (add_le_add_both ?_ e5)
  refine le_trans (abs_add _ _) (add_le_add_both ?_ e4)
  refine le_trans (abs_add _ _) (add_le_add_both ?_ e3)
  exact le_trans (abs_add _ _) (add_le_add_both e1 e2)

/-! ## `sec² = 1+tan²`, so `tan`'s derivative can be written in terms of `tan` itself (not `cos`) —
not yet in `MachLib`, needed for every `_deriv` proof in the `R0..Rtan7` chain. -/

theorem sec_sq_eq_one_add_tan_sq {c : Real} (hc : abs c < pi / (1 + 1)) :
    1 / (cos c * cos c) = 1 + tan c * tan c := by
  have hcpos : 0 < cos c := cos_pos_of_abs_lt_pi_div_two hc
  have hcne : cos c ≠ 0 := ne_of_gt hcpos
  have hccne : cos c * cos c ≠ 0 := mul_ne_zero hcne hcne
  have htan : tan c = sin c / cos c := tan_def c hcne
  have key : (1 + tan c * tan c) * (cos c * cos c) = 1 := by
    rw [htan, div_def (sin c) (cos c) hcne]
    rw [show (1 + sin c * (1 / cos c) * (sin c * (1 / cos c))) * (cos c * cos c)
        = cos c * cos c + sin c * sin c * ((1 / cos c) * (1 / cos c) * (cos c * cos c))
        from by mach_mpoly [cos c, sin c, (1 / cos c : Real)]]
    rw [show (1 / cos c : Real) * (1 / cos c) * (cos c * cos c)
        = ((1 / cos c) * cos c) * ((1 / cos c) * cos c) from by mach_ring,
      mul_comm (1 / cos c : Real) (cos c), mul_inv (cos c) hcne,
      show cos c * cos c + sin c * sin c * ((1 : Real) * 1) = sin c * sin c + cos c * cos c
        from by mach_ring]
    exact pythagorean c
  refine mul_right_cancel' hccne ?_
  rw [key, mul_comm (1 / (cos c * cos c) : Real) (cos c * cos c), mul_inv (cos c * cos c) hccne]

/-- `HasDerivAt tan (1 + tan c * tan c) c` — `HasDerivAt_tan` re-expressed via `sec_sq_eq_one_add_tan_sq`
so every derivative in the chain can be stated purely in terms of `tan`. -/
theorem HasDerivAt_tan' {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt tan (1 + tan c * tan c) c :=
  hasDerivAt_congr_val (HasDerivAt_tan hc) (sec_sq_eq_one_add_tan_sq hc)

/-! ## Derivative combinators for powers of `tan` — domain-restricted analogues of
`SinTaylorRemainder`'s `hD_y2..hD_y6`, built the same way (product rule, chained on already-
established lower powers), just differentiating `tan y` instead of the bare variable `y`. -/

theorem hDtan_2 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y)
      ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) c :=
  HasDerivAt_mul tan tan (1 + tan c * tan c) (1 + tan c * tan c) c
    (HasDerivAt_tan' hc) (HasDerivAt_tan' hc)

theorem hDtan_3 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y * tan y)
      (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
        + (tan c * tan c) * (1 + tan c * tan c)) c :=
  HasDerivAt_mul (fun y => tan y * tan y) tan
    ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) (1 + tan c * tan c) c
    (hDtan_2 hc) (HasDerivAt_tan' hc)

theorem hDtan_4raw {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => (tan y * tan y) * (tan y * tan y))
      (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
        + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))) c :=
  HasDerivAt_mul (fun y => tan y * tan y) (fun y => tan y * tan y)
    ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))
    ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) c (hDtan_2 hc) (hDtan_2 hc)

theorem hDtan_4 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y * tan y * tan y)
      (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
        + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))) c :=
  HasDerivAt_of_eq (fun y => (tan y * tan y) * (tan y * tan y))
    (fun y => tan y * tan y * tan y * tan y) _ c (fun y => by mach_ring) (hDtan_4raw hc)

theorem hDtan_5raw {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => (tan y * tan y) * (tan y * tan y * tan y))
      (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c * tan c)
        + (tan c * tan c) * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c))) c :=
  HasDerivAt_mul (fun y => tan y * tan y) (fun y => tan y * tan y * tan y)
    ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
      + (tan c * tan c) * (1 + tan c * tan c)) c (hDtan_2 hc) (hDtan_3 hc)

theorem hDtan_5 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y * tan y * tan y * tan y)
      (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c * tan c)
        + (tan c * tan c) * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c))) c :=
  HasDerivAt_of_eq (fun y => (tan y * tan y) * (tan y * tan y * tan y))
    (fun y => tan y * tan y * tan y * tan y * tan y) _ c (fun y => by mach_ring) (hDtan_5raw hc)

theorem hDtan_6raw {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => (tan y * tan y * tan y) * (tan y * tan y * tan y))
      ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c)
        + (tan c * tan c * tan c)
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
            + (tan c * tan c) * (1 + tan c * tan c))) c :=
  HasDerivAt_mul (fun y => tan y * tan y * tan y) (fun y => tan y * tan y * tan y)
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
      + (tan c * tan c) * (1 + tan c * tan c))
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
      + (tan c * tan c) * (1 + tan c * tan c)) c (hDtan_3 hc) (hDtan_3 hc)

theorem hDtan_6 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y * tan y * tan y * tan y * tan y)
      ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c)
        + (tan c * tan c * tan c)
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
            + (tan c * tan c) * (1 + tan c * tan c))) c :=
  HasDerivAt_of_eq (fun y => (tan y * tan y * tan y) * (tan y * tan y * tan y))
    (fun y => tan y * tan y * tan y * tan y * tan y * tan y) _ c (fun y => by mach_ring)
    (hDtan_6raw hc)

theorem hDtan_7raw {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => (tan y * tan y * tan y) * (tan y * tan y * tan y * tan y))
      ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c * tan c)
        + (tan c * tan c * tan c)
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
  HasDerivAt_mul (fun y => tan y * tan y * tan y) (fun y => tan y * tan y * tan y * tan y)
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
      + (tan c * tan c) * (1 + tan c * tan c))
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
      + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))) c
    (hDtan_3 hc) (hDtan_4 hc)

theorem hDtan_7 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y * tan y * tan y * tan y * tan y * tan y)
      ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c * tan c)
        + (tan c * tan c * tan c)
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
  HasDerivAt_of_eq (fun y => (tan y * tan y * tan y) * (tan y * tan y * tan y * tan y))
    (fun y => tan y * tan y * tan y * tan y * tan y * tan y * tan y) _ c (fun y => by mach_ring)
    (hDtan_7raw hc)

theorem hDtan_8raw {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => (tan y * tan y * tan y * tan y) * (tan y * tan y * tan y * tan y))
      ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
          + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))
          * (tan c * tan c * tan c * tan c)
        + (tan c * tan c * tan c * tan c)
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
  HasDerivAt_mul (fun y => tan y * tan y * tan y * tan y) (fun y => tan y * tan y * tan y * tan y)
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
      + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))
    (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
      + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))) c
    (hDtan_4 hc) (hDtan_4 hc)

theorem hDtan_8 {c : Real} (hc : abs c < pi / (1 + 1)) :
    HasDerivAt (fun y => tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y)
      ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
          + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))
          * (tan c * tan c * tan c * tan c)
        + (tan c * tan c * tan c * tan c)
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
  HasDerivAt_of_eq (fun y => (tan y * tan y * tan y * tan y) * (tan y * tan y * tan y * tan y))
    (fun y => tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y) _ c
    (fun y => by mach_ring) (hDtan_8raw hc)

/-! ## Small `natCast` conversions — turn the small integer coefficients that fall out of the
product rule (`1+1`, `1+1+1+1`, ...) into `natCast` form, so `natCast_mul` can combine them with
the chain's `natCast`-represented coefficients directly (matching the exact shape `mach_ring` sees,
rather than guessing at its internal normal form for repeated addition). -/

theorem natCast_one : natCast 1 = 1 := by rw [natCast_succ, natCast_zero]; exact zero_add 1
theorem natCast_two : natCast 2 = 1 + 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, natCast_add, natCast_one]
theorem natCast_four : natCast 4 = 1 + 1 + 1 + 1 := by
  rw [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, natCast_add, natCast_add, natCast_add, natCast_one]
theorem natCast_six : natCast 6 = 1 + 1 + 1 + 1 + 1 + 1 := by
  rw [show (6 : Nat) = 1 + 1 + 1 + 1 + 1 + 1 from rfl, natCast_add, natCast_add, natCast_add,
    natCast_add, natCast_add, natCast_one]
theorem natCast_eight : natCast 8 = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
  rw [show (8 : Nat) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl, natCast_add, natCast_add,
    natCast_add, natCast_add, natCast_add, natCast_add, natCast_add, natCast_one]

/-- `(1+1) * natCast n = natCast (2*n)` — combine a small product-rule coefficient with a chain
coefficient directly via `natCast_mul`. -/
theorem two_mul_natCast (n : Nat) : (1 + 1) * natCast n = natCast (2 * n) := by
  rw [natCast_mul, natCast_two]
theorem four_mul_natCast (n : Nat) : (1 + 1 + 1 + 1) * natCast n = natCast (4 * n) := by
  rw [natCast_mul, natCast_four]
theorem six_mul_natCast (n : Nat) : (1 + 1 + 1 + 1 + 1 + 1) * natCast n = natCast (6 * n) := by
  rw [natCast_mul, natCast_six]
theorem eight_mul_natCast (n : Nat) :
    (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast n = natCast (8 * n) := by
  rw [natCast_mul, natCast_eight]

theorem natCast_three : natCast 3 = 1 + 1 + 1 := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl, natCast_add, natCast_add, natCast_one]
theorem natCast_five : natCast 5 = 1 + 1 + 1 + 1 + 1 := by
  rw [show (5 : Nat) = 1 + 1 + 1 + 1 + 1 from rfl, natCast_add, natCast_add, natCast_add,
    natCast_add, natCast_one]
theorem natCast_seven : natCast 7 = 1 + 1 + 1 + 1 + 1 + 1 + 1 := by
  rw [show (7 : Nat) = 1 + 1 + 1 + 1 + 1 + 1 + 1 from rfl, natCast_add, natCast_add, natCast_add,
    natCast_add, natCast_add, natCast_add, natCast_one]

theorem three_mul_natCast (n : Nat) : (1 + 1 + 1) * natCast n = natCast (3 * n) := by
  rw [natCast_mul, natCast_three]
theorem five_mul_natCast (n : Nat) : (1 + 1 + 1 + 1 + 1) * natCast n = natCast (5 * n) := by
  rw [natCast_mul, natCast_five]
theorem seven_mul_natCast (n : Nat) :
    (1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast n = natCast (7 * n) := by
  rw [natCast_mul, natCast_seven]

/-! ## `Rtan7` — the base level (`Rtan6' = Rtan7`, `Rtan7' = g8`). `Rtan7(y) = g7(y) − 272` (the constant term of
`tan`'s 7th derivative cancels against the 7th derivative of the truncation polynomial, which is
itself the constant `272`). -/

noncomputable def Rtan7 (y : Real) : Real :=
  natCast 3968 * (tan y * tan y) + natCast 12096 * (tan y * tan y * tan y * tan y)
    + natCast 13440 * (tan y * tan y * tan y * tan y * tan y * tan y)
    + natCast 5040 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y)

theorem Rtan7_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan7 (g8 c) c := by
  have h2 : HasDerivAt (fun y => natCast 3968 * (tan y * tan y))
      (0 * (tan c * tan c)
        + natCast 3968 * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 3968) (fun y => tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 3968) c) (hDtan_2 hc)
  have h4 : HasDerivAt (fun y => natCast 12096 * (tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c)
        + natCast 12096
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 12096) (fun y => tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 12096) c) (hDtan_4 hc)
  have h6 : HasDerivAt (fun y => natCast 13440 * (tan y * tan y * tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c * tan c * tan c)
        + natCast 13440
          * ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
              + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c)
            + (tan c * tan c * tan c)
              * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
                + (tan c * tan c) * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 13440)
      (fun y => tan y * tan y * tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 13440) c) (hDtan_6 hc)
  have h8 : HasDerivAt
      (fun y => natCast 5040 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c * tan c * tan c * tan c * tan c)
        + natCast 5040
          * ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
              + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))
              * (tan c * tan c * tan c * tan c)
            + (tan c * tan c * tan c * tan c)
              * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
                + (tan c * tan c) * ((1 + tan c * tan c) * tan c
                  + tan c * (1 + tan c * tan c))))) c :=
    HasDerivAt_mul (fun _ => natCast 5040)
      (fun y => tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 5040) c) (hDtan_8 hc)
  have hfull := HasDerivAt_add (fun y => natCast 3968 * (tan y * tan y)
      + natCast 12096 * (tan y * tan y * tan y * tan y)
      + natCast 13440 * (tan y * tan y * tan y * tan y * tan y * tan y))
    (fun y => natCast 5040
      * (tan y * tan y * tan y * tan y * tan y * tan y * tan y * tan y)) _ _ c
    (HasDerivAt_add (fun y => natCast 3968 * (tan y * tan y)
      + natCast 12096 * (tan y * tan y * tan y * tan y))
      (fun y => natCast 13440 * (tan y * tan y * tan y * tan y * tan y * tan y)) _ _ c
      (HasDerivAt_add (fun y => natCast 3968 * (tan y * tan y))
        (fun y => natCast 12096 * (tan y * tan y * tan y * tan y)) _ _ c h2 h4) h6) h8
  have hT1 : natCast 7936 = (1 + 1) * natCast 3968 := (two_mul_natCast 3968).symm
  have hT3 : natCast 56320 = (1 + 1) * natCast 3968 + (1 + 1 + 1 + 1) * natCast 12096 := by
    rw [two_mul_natCast, four_mul_natCast, ← natCast_add]
  have hT5 : natCast 129024
      = (1 + 1 + 1 + 1) * natCast 12096 + (1 + 1 + 1 + 1 + 1 + 1) * natCast 13440 := by
    rw [four_mul_natCast, six_mul_natCast, ← natCast_add]
  have hT7 : natCast 120960 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 13440
      + (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 5040 := by
    rw [six_mul_natCast, eight_mul_natCast, ← natCast_add]
  have hT9 : natCast 40320 = (1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 5040 :=
    (eight_mul_natCast 5040).symm
  refine hasDerivAt_congr_val hfull ?_
  unfold g8
  rw [hT1, hT3, hT5, hT7, hT9]
  mach_ring

theorem Rtan7_zero : Rtan7 0 = 0 := by unfold Rtan7; rw [tan_zero]; mach_ring

/-- `|Rtan7(x)| ≤ 354560 · Mtan(x)^9 · x` for `x ∈ [0,1]` — the base bound of the whole chain,
combining `Rtan7_deriv` (`Rtan7' = g8`) with `g8_bound` via the domain-restricted MVT step. -/
theorem Rtan7_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan7 x) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x := by
  apply abs_mvt_step_bounded Rtan7 g8 x
    (natCast 354560 * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x))
    (pi / (1 + 1)) hx0 hx
    (mul_nonneg (natCast_nonneg 354560)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
        (mul_nonneg (Mtan_nonneg hx0 hx) (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx))
        (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx))
        (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx)))
    (fun c hc0 hcR => Rtan7_deriv (by rw [abs_of_nonneg hc0]; exact hcR))
    Rtan7_zero (fun t ht0 htx => g8_bound t x ht0 htx hx)

/-! ## `Rtan6` (`Rtan5' = Rtan6`, `Rtan6' = Rtan7`). `Rtan6(y) = g6(y) − 272y`. From here down, every `_bound` proof
is a SIMPLE propagation (mirroring `SinhTaylorRemainder` exactly) — the multi-term decomposition
work is done, concentrated entirely in `g8_bound` above. -/

noncomputable def Rtan6 (y : Real) : Real :=
  natCast 272 * tan y + natCast 1232 * (tan y * tan y * tan y)
    + natCast 1680 * (tan y * tan y * tan y * tan y * tan y)
    + natCast 720 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y) - natCast 272 * y

theorem Rtan6_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan6 (Rtan7 c) c := by
  have h1 : HasDerivAt (fun y => natCast 272 * tan y) (0 * tan c + natCast 272 * (1 + tan c * tan c)) c :=
    HasDerivAt_mul (fun _ => natCast 272) tan 0 _ c (HasDerivAt_const (natCast 272) c) (HasDerivAt_tan' hc)
  have h3 : HasDerivAt (fun y => natCast 1232 * (tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c) + natCast 1232
        * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c))) c :=
    HasDerivAt_mul (fun _ => natCast 1232) (fun y => tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 1232) c) (hDtan_3 hc)
  have h5 : HasDerivAt (fun y => natCast 1680 * (tan y * tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c * tan c) + natCast 1680
        * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c * tan c)
          + (tan c * tan c) * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
            + (tan c * tan c) * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 1680) (fun y => tan y * tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 1680) c) (hDtan_5 hc)
  have h7 : HasDerivAt
      (fun y => natCast 720 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c * tan c * tan c * tan c) + natCast 720
        * ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
              + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c * tan c)
            + (tan c * tan c * tan c)
              * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
                + (tan c * tan c) * ((1 + tan c * tan c) * tan c
                  + tan c * (1 + tan c * tan c))))) c :=
    HasDerivAt_mul (fun _ => natCast 720)
      (fun y => tan y * tan y * tan y * tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 720) c) (hDtan_7 hc)
  have hy : HasDerivAt (fun y => natCast 272 * y) (0 * c + natCast 272 * 1) c :=
    HasDerivAt_mul (fun _ => natCast 272) (fun y => y) 0 1 c (HasDerivAt_const (natCast 272) c)
      (HasDerivAt_id c)
  have hfull := HasDerivAt_add
    (fun y => natCast 272 * tan y + natCast 1232 * (tan y * tan y * tan y)
      + natCast 1680 * (tan y * tan y * tan y * tan y * tan y))
    (fun y => natCast 720 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y)) _ _ c
    (HasDerivAt_add (fun y => natCast 272 * tan y + natCast 1232 * (tan y * tan y * tan y))
      (fun y => natCast 1680 * (tan y * tan y * tan y * tan y * tan y)) _ _ c
      (HasDerivAt_add (fun y => natCast 272 * tan y)
        (fun y => natCast 1232 * (tan y * tan y * tan y)) _ _ c h1 h3) h5) h7
  have hfull2 := HasDerivAt_sub
    (fun y => natCast 272 * tan y + natCast 1232 * (tan y * tan y * tan y)
      + natCast 1680 * (tan y * tan y * tan y * tan y * tan y)
      + natCast 720 * (tan y * tan y * tan y * tan y * tan y * tan y * tan y))
    (fun y => natCast 272 * y) _ _ c hfull hy
  have hT2 : natCast 3968 = natCast 272 + (1 + 1 + 1) * natCast 1232 := by
    rw [three_mul_natCast, ← natCast_add]
  have hT4 : natCast 12096
      = (1 + 1 + 1) * natCast 1232 + (1 + 1 + 1 + 1 + 1) * natCast 1680 := by
    rw [three_mul_natCast, five_mul_natCast, ← natCast_add]
  have hT6 : natCast 13440
      = (1 + 1 + 1 + 1 + 1) * natCast 1680 + (1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 720 := by
    rw [five_mul_natCast, seven_mul_natCast, ← natCast_add]
  have hT8 : natCast 5040 = (1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 720 :=
    (seven_mul_natCast 720).symm
  refine hasDerivAt_congr_val hfull2 ?_
  unfold Rtan7
  rw [hT2, hT4, hT6, hT8]
  mach_mpoly [tan c, natCast 272, natCast 1232, natCast 1680, natCast 720]

theorem Rtan6_zero : Rtan6 0 = 0 := by unfold Rtan6; rw [tan_zero]; mach_ring

/-- `Mtan(t)^9 ≤ Mtan(x)^9` for `t ≤ x` — the ONE reusable monotonicity fact every remaining
level's `_bound` proof needs (the `354560 * Mtan(x)^9` factor is carried unchanged from `Rtan7_bound`
all the way to `R0_bound`; only the number of `* x` factors grows). -/
theorem Mtan_pow9_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := by
  have hx0 : 0 ≤ x := le_trans ht0 htx
  have hb1 : Mtan t ≤ Mtan x := Mtan_mono ht0 htx hx
  have n1 : 0 ≤ Mtan t := Mtan_nonneg ht0 (lt_of_le_of_lt htx hx)
  have n2 : 0 ≤ Mtan x := Mtan_nonneg hx0 hx
  have s2 : Mtan t * Mtan t ≤ Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right hb1 n1) (mul_le_mul_of_nonneg_left hb1 n2)
  have s2nn : 0 ≤ Mtan x * Mtan x := mul_nonneg n2 n2
  have s3 : Mtan t * Mtan t * Mtan t ≤ Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right s2 n1) (mul_le_mul_of_nonneg_left hb1 s2nn)
  have s3nn : 0 ≤ Mtan x * Mtan x * Mtan x := mul_nonneg s2nn n2
  have s4 : Mtan t * Mtan t * Mtan t * Mtan t ≤ Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right s3 n1) (mul_le_mul_of_nonneg_left hb1 s3nn)
  have s4nn : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x := mul_nonneg s3nn n2
  have s5 : Mtan t * Mtan t * Mtan t * Mtan t * Mtan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right s4 n1) (mul_le_mul_of_nonneg_left hb1 s4nn)
  have s5nn : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := mul_nonneg s4nn n2
  have s6 : Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right s5 n1) (mul_le_mul_of_nonneg_left hb1 s5nn)
  have s6nn : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x := mul_nonneg s5nn n2
  have s7 : Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right s6 n1) (mul_le_mul_of_nonneg_left hb1 s6nn)
  have s7nn : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    mul_nonneg s6nn n2
  have s8 : Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t
      ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    le_trans (mul_le_mul_of_nonneg_right s7 n1) (mul_le_mul_of_nonneg_left hb1 s7nn)
  have s8nn : 0 ≤ Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x :=
    mul_nonneg s7nn n2
  exact le_trans (mul_le_mul_of_nonneg_right s8 n1) (mul_le_mul_of_nonneg_left hb1 s8nn)

/-- `0 ≤ 354560 · Mtan(x)^9` — extracted as its own lemma to keep the `_bound` proofs below
free of multi-line `have`s inside lambdas. -/
theorem natCast354560_Mtan9_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) :=
  mul_nonneg (natCast_nonneg 354560)
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
      (mul_nonneg (Mtan_nonneg hx0 hx) (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx))
      (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx))
      (Mtan_nonneg hx0 hx)) (Mtan_nonneg hx0 hx))

/-- `|Rtan6(x)| ≤ (354560 · Mtan(x)^9 · x) · x` — direct propagation from `Rtan7_bound` via
`abs_mvt_step_bounded`. -/
theorem Rtan6_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan6 x) ≤ (natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x := by
  apply abs_mvt_step_bounded Rtan6 Rtan7 x (natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
    (pi / (1 + 1)) hx0 hx
    (mul_nonneg (natCast354560_Mtan9_nonneg hx0 hx) hx0)
    (fun c hc0 hcR => Rtan6_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan6_zero
    (fun t ht0 htx => le_trans (Rtan7_bound t ht0 (lt_of_le_of_lt htx hx))
      (le_trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Mtan_pow9_mono ht0 htx hx) (natCast_nonneg 354560)) ht0)
        (mul_le_mul_of_nonneg_left htx (natCast354560_Mtan9_nonneg hx0 hx))))

/-! ## `Rtan5` (`R4' = Rtan5`, `Rtan5' = Rtan6`). `Rtan5(y) = g5(y) − 16 − 136y²`. -/

noncomputable def Rtan5 (y : Real) : Real :=
  natCast 136 * (tan y * tan y) + natCast 240 * (tan y * tan y * tan y * tan y)
    + natCast 120 * (tan y * tan y * tan y * tan y * tan y * tan y) - natCast 136 * (y * y)

theorem Rtan5_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan5 (Rtan6 c) c := by
  have h2 : HasDerivAt (fun y => natCast 136 * (tan y * tan y))
      (0 * (tan c * tan c)
        + natCast 136 * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))) c :=
    HasDerivAt_mul (fun _ => natCast 136) (fun y => tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 136) c) (hDtan_2 hc)
  have h4 : HasDerivAt (fun y => natCast 240 * (tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c)
        + natCast 240
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 240) (fun y => tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 240) c) (hDtan_4 hc)
  have h6 : HasDerivAt (fun y => natCast 120 * (tan y * tan y * tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c * tan c * tan c)
        + natCast 120
          * ((((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
              + (tan c * tan c) * (1 + tan c * tan c)) * (tan c * tan c * tan c)
            + (tan c * tan c * tan c)
              * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
                + (tan c * tan c) * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 120)
      (fun y => tan y * tan y * tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 120) c) (hDtan_6 hc)
  have hy2 : HasDerivAt (fun y => natCast 136 * (y * y)) (0 * (c * c) + natCast 136 * (c + c)) c :=
    HasDerivAt_mul (fun _ => natCast 136) (fun y => y * y) 0 (c + c) c
      (HasDerivAt_const (natCast 136) c) (hD_y2 c)
  have hfull := HasDerivAt_add (fun y => natCast 136 * (tan y * tan y)
      + natCast 240 * (tan y * tan y * tan y * tan y))
    (fun y => natCast 120 * (tan y * tan y * tan y * tan y * tan y * tan y)) _ _ c
    (HasDerivAt_add (fun y => natCast 136 * (tan y * tan y))
      (fun y => natCast 240 * (tan y * tan y * tan y * tan y)) _ _ c h2 h4) h6
  have hfull2 := HasDerivAt_sub (fun y => natCast 136 * (tan y * tan y)
      + natCast 240 * (tan y * tan y * tan y * tan y)
      + natCast 120 * (tan y * tan y * tan y * tan y * tan y * tan y))
    (fun y => natCast 136 * (y * y)) _ _ c hfull hy2
  have hT1 : natCast 272 = (1 + 1) * natCast 136 := (two_mul_natCast 136).symm
  have hT3 : natCast 1232 = (1 + 1) * natCast 136 + (1 + 1 + 1 + 1) * natCast 240 := by
    rw [two_mul_natCast, four_mul_natCast, ← natCast_add]
  have hT5 : natCast 1680 = (1 + 1 + 1 + 1) * natCast 240 + (1 + 1 + 1 + 1 + 1 + 1) * natCast 120 := by
    rw [four_mul_natCast, six_mul_natCast, ← natCast_add]
  have hT7 : natCast 720 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 120 := (six_mul_natCast 120).symm
  refine hasDerivAt_congr_val hfull2 ?_
  unfold Rtan6
  rw [hT1, hT3, hT5, hT7]
  mach_mpoly [tan c, c, natCast 136, natCast 240, natCast 120]

theorem Rtan5_zero : Rtan5 0 = 0 := by unfold Rtan5; rw [tan_zero]; mach_ring

/-- Generic 2-step bump: `At ≤ Ax` and `t ≤ x` (all nonneg where needed) give `At*t ≤ Ax*x`. The
ONE combinator every remaining level's bound-propagation reuses, growing the number of trailing
`*x` factors by one per level. -/
theorem bump_step {At Ax t x : Real} (hAtx : At ≤ Ax) (htx : t ≤ x) (hAxnn : 0 ≤ Ax)
    (htnn : 0 ≤ t) : At * t ≤ Ax * x :=
  le_trans (mul_le_mul_of_nonneg_right hAtx htnn) (mul_le_mul_of_nonneg_left htx hAxnn)

theorem Base1_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x :=
  mul_nonneg (natCast354560_Mtan9_nonneg hx0 hx) hx0

theorem Base1_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t) * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x :=
  bump_step (mul_le_mul_of_nonneg_left (Mtan_pow9_mono ht0 htx hx) (natCast_nonneg 354560)) htx
    (natCast354560_Mtan9_nonneg (le_trans ht0 htx) hx) ht0

theorem Base2_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x * x :=
  mul_nonneg (Base1_nonneg hx0 hx) hx0

theorem Base2_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t) * t * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x * x :=
  bump_step (Base1_mono ht0 htx hx) htx (Base1_nonneg (le_trans ht0 htx) hx) ht0

/-- `|Rtan5(x)| ≤ ((354560 · Mtan(x)^9 · x) · x) · x` — direct propagation from `Rtan6_bound`. -/
theorem Rtan5_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan5 x) ≤ ((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x := by
  apply abs_mvt_step_bounded Rtan5 Rtan6 x ((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x) * x)
    (pi / (1 + 1)) hx0 hx (Base2_nonneg hx0 hx)
    (fun c hc0 hcR => Rtan5_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan5_zero
    (fun t ht0 htx => le_trans (Rtan6_bound t ht0 (lt_of_le_of_lt htx hx)) (Base2_mono ht0 htx hx))

/-! ## Fraction reduction via `natCast` denominators — needed from `Rtan4` down (`tan`'s own
Taylor coefficients `1/3, 2/15, 17/315` carry fractions through their derivatives until the
power-rule multiplier exactly cancels the denominator, same mechanism as `SinTaylorRemainder`'s
`frac_reduce`, just with `natCast`-represented denominators instead of flat sums). -/

theorem third_reduce (x : Real) : (x + x + x) * (1 / natCast 3) = x := by
  refine mul_right_cancel' (natCast_ne_zero (n := 3) (by decide)) ?_
  rw [show (x + x + x) * (1 / natCast 3) * natCast 3 = (x + x + x) * (natCast 3 * (1 / natCast 3))
      from by mach_ring, mul_inv (natCast 3) (natCast_ne_zero (n := 3) (by decide)), mul_one_ax,
    natCast_three]
  mach_ring

/-- `natCast a * (1/natCast b) = natCast c` whenever `a = c*b` (as Nats) — reduces a fraction
down to a whole number, general version of `third_reduce`'s specific pattern. -/
theorem natCast_frac_to_nat {a b c : Nat} (hb : 0 < b) (h : a = c * b) :
    natCast a * (1 / natCast b) = natCast c := by
  refine mul_right_cancel' (natCast_ne_zero hb) ?_
  rw [show natCast a * (1 / natCast b) * natCast b = natCast a * (natCast b * (1 / natCast b))
      from by mach_ring, mul_inv (natCast b) (natCast_ne_zero hb), mul_one_ax, h, natCast_mul]

/-- `natCast a * (1/natCast b) = natCast c * (1/natCast d)` whenever `a*d = c*b` (cross
multiplication) — reduces one unreduced fraction to another, e.g. `170/15 = 34/3`. -/
theorem natCast_frac_eq {a b c d : Nat} (hb : 0 < b) (hd : 0 < d) (h : a * d = c * b) :
    natCast a * (1 / natCast b) = natCast c * (1 / natCast d) := by
  refine mul_right_cancel' (mul_ne_zero (natCast_ne_zero hb) (natCast_ne_zero hd)) ?_
  rw [show natCast a * (1 / natCast b) * (natCast b * natCast d)
      = natCast a * natCast d * (natCast b * (1 / natCast b)) from by mach_ring,
    mul_inv (natCast b) (natCast_ne_zero hb), mul_one_ax,
    show natCast c * (1 / natCast d) * (natCast b * natCast d)
      = natCast c * natCast b * (natCast d * (1 / natCast d)) from by mach_ring,
    mul_inv (natCast d) (natCast_ne_zero hd), mul_one_ax, ← natCast_mul, ← natCast_mul, h]

/-! ## `Rtan4` (`Rtan3' = Rtan4`, `Rtan4' = Rtan5`). `Rtan4(y) = g4(y) − 16y − (136/3)y³`. -/

noncomputable def Rtan4 (y : Real) : Real :=
  natCast 16 * tan y + natCast 40 * (tan y * tan y * tan y)
    + natCast 24 * (tan y * tan y * tan y * tan y * tan y) - natCast 16 * y
    - natCast 136 * (y * y * y) * (1 / natCast 3)

theorem Rtan4_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan4 (Rtan5 c) c := by
  have h1 : HasDerivAt (fun y => natCast 16 * tan y) (0 * tan c + natCast 16 * (1 + tan c * tan c)) c :=
    HasDerivAt_mul (fun _ => natCast 16) tan 0 _ c (HasDerivAt_const (natCast 16) c) (HasDerivAt_tan' hc)
  have h3 : HasDerivAt (fun y => natCast 40 * (tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c) + natCast 40
        * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c))) c :=
    HasDerivAt_mul (fun _ => natCast 40) (fun y => tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 40) c) (hDtan_3 hc)
  have h5 : HasDerivAt (fun y => natCast 24 * (tan y * tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c * tan c) + natCast 24
        * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c * tan c)
          + (tan c * tan c) * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
            + (tan c * tan c) * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 24) (fun y => tan y * tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 24) c) (hDtan_5 hc)
  have hy : HasDerivAt (fun y => natCast 16 * y) (0 * c + natCast 16 * 1) c :=
    HasDerivAt_mul (fun _ => natCast 16) (fun y => y) 0 1 c (HasDerivAt_const (natCast 16) c)
      (HasDerivAt_id c)
  have hy3raw : HasDerivAt (fun y => natCast 136 * (y * y * y))
      (0 * (c * c * c) + natCast 136 * (c * c + c * c + c * c)) c :=
    HasDerivAt_mul (fun _ => natCast 136) (fun y => y * y * y) 0 _ c
      (HasDerivAt_const (natCast 136) c) (hD_y3 c)
  have hy3 : HasDerivAt (fun y => natCast 136 * (y * y * y) * (1 / natCast 3))
      ((0 * (c * c * c) + natCast 136 * (c * c + c * c + c * c)) * (1 / natCast 3)
        + (natCast 136 * (c * c * c)) * 0) c :=
    HasDerivAt_mul (fun y => natCast 136 * (y * y * y)) (fun _ => 1 / natCast 3) _ 0 c hy3raw
      (HasDerivAt_const (1 / natCast 3) c)
  have hfull := HasDerivAt_add (fun y => natCast 16 * tan y + natCast 40 * (tan y * tan y * tan y))
    (fun y => natCast 24 * (tan y * tan y * tan y * tan y * tan y)) _ _ c
    (HasDerivAt_add (fun y => natCast 16 * tan y) (fun y => natCast 40 * (tan y * tan y * tan y))
      _ _ c h1 h3) h5
  have hfull2 := HasDerivAt_sub (fun y => natCast 16 * tan y + natCast 40 * (tan y * tan y * tan y)
      + natCast 24 * (tan y * tan y * tan y * tan y * tan y))
    (fun y => natCast 16 * y) _ _ c hfull hy
  have hfull3 := HasDerivAt_sub (fun y => natCast 16 * tan y + natCast 40 * (tan y * tan y * tan y)
      + natCast 24 * (tan y * tan y * tan y * tan y * tan y) - natCast 16 * y)
    (fun y => natCast 136 * (y * y * y) * (1 / natCast 3)) _ _ c hfull2 hy3
  have hT2 : natCast 136 = natCast 16 + (1 + 1 + 1) * natCast 40 := by
    rw [three_mul_natCast, ← natCast_add]
  have hT4 : natCast 240 = (1 + 1 + 1) * natCast 40 + (1 + 1 + 1 + 1 + 1) * natCast 24 := by
    rw [three_mul_natCast, five_mul_natCast, ← natCast_add]
  have hT6 : natCast 120 = (1 + 1 + 1 + 1 + 1) * natCast 24 := (five_mul_natCast 24).symm
  refine hasDerivAt_congr_val hfull3 ?_
  rw [show (0 * (c * c * c) + natCast 136 * (c * c + c * c + c * c)) * (1 / natCast 3)
      + natCast 136 * (c * c * c) * 0 = natCast 136 * ((c * c + c * c + c * c) * (1 / natCast 3))
      from by mach_ring, third_reduce (c * c)]
  unfold Rtan5
  rw [hT2, hT4, hT6]
  mach_mpoly [tan c, c, natCast 16, natCast 40, natCast 24]

theorem Rtan4_zero : Rtan4 0 = 0 := by unfold Rtan4; rw [tan_zero]; mach_ring

theorem Base3_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      * x * x * x :=
  mul_nonneg (Base2_nonneg hx0 hx) hx0

theorem Base3_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t)
        * t * t * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        * x * x * x :=
  bump_step (Base2_mono ht0 htx hx) htx (Base2_nonneg (le_trans ht0 htx) hx) ht0

/-- `|Rtan4(x)| ≤ 354560 · Mtan(x)^9 · x · x · x · x` — direct propagation from `Rtan5_bound`. -/
theorem Rtan4_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan4 x) ≤ ((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x := by
  apply abs_mvt_step_bounded Rtan4 Rtan5 x (((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x)
    (pi / (1 + 1)) hx0 hx (Base3_nonneg hx0 hx)
    (fun c hc0 hcR => Rtan4_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan4_zero
    (fun t ht0 htx => le_trans (Rtan5_bound t ht0 (lt_of_le_of_lt htx hx)) (Base3_mono ht0 htx hx))

/-! ## `Rtan3` (`Rtan2' = Rtan3`, `Rtan3' = Rtan4`). `Rtan3(y) = g3(y) − 8y² − (34/3)y⁴`. -/

noncomputable def Rtan3 (y : Real) : Real :=
  natCast 8 * (tan y * tan y) + natCast 6 * (tan y * tan y * tan y * tan y) - natCast 8 * (y * y)
    - natCast 34 * (y * y * y * y) * (1 / natCast 3)

theorem Rtan3_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan3 (Rtan4 c) c := by
  have h2 : HasDerivAt (fun y => natCast 8 * (tan y * tan y))
      (0 * (tan c * tan c)
        + natCast 8 * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c))) c :=
    HasDerivAt_mul (fun _ => natCast 8) (fun y => tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 8) c) (hDtan_2 hc)
  have h4 : HasDerivAt (fun y => natCast 6 * (tan y * tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c * tan c)
        + natCast 6
          * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * (tan c * tan c)
            + (tan c * tan c) * ((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)))) c :=
    HasDerivAt_mul (fun _ => natCast 6) (fun y => tan y * tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 6) c) (hDtan_4 hc)
  have hy2 : HasDerivAt (fun y => natCast 8 * (y * y)) (0 * (c * c) + natCast 8 * (c + c)) c :=
    HasDerivAt_mul (fun _ => natCast 8) (fun y => y * y) 0 (c + c) c
      (HasDerivAt_const (natCast 8) c) (hD_y2 c)
  have hy4raw : HasDerivAt (fun y => natCast 34 * (y * y * y * y))
      (0 * (c * c * c * c) + natCast 34 * ((c + c) * (c * c) + (c * c) * (c + c))) c :=
    HasDerivAt_mul (fun _ => natCast 34) (fun y => y * y * y * y) 0 _ c
      (HasDerivAt_const (natCast 34) c) (hD_y4 c)
  have hy4 : HasDerivAt (fun y => natCast 34 * (y * y * y * y) * (1 / natCast 3))
      ((0 * (c * c * c * c) + natCast 34 * ((c + c) * (c * c) + (c * c) * (c + c)))
          * (1 / natCast 3) + natCast 34 * (c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 34 * (y * y * y * y)) (fun _ => 1 / natCast 3) _ 0 c hy4raw
      (HasDerivAt_const (1 / natCast 3) c)
  have hfull := HasDerivAt_add (fun y => natCast 8 * (tan y * tan y))
    (fun y => natCast 6 * (tan y * tan y * tan y * tan y)) _ _ c h2 h4
  have hfull2 := HasDerivAt_sub (fun y => natCast 8 * (tan y * tan y)
      + natCast 6 * (tan y * tan y * tan y * tan y)) (fun y => natCast 8 * (y * y)) _ _ c hfull hy2
  have hfull3 := HasDerivAt_sub (fun y => natCast 8 * (tan y * tan y)
      + natCast 6 * (tan y * tan y * tan y * tan y) - natCast 8 * (y * y))
    (fun y => natCast 34 * (y * y * y * y) * (1 / natCast 3)) _ _ c hfull2 hy4
  have hT1 : natCast 16 = (1 + 1) * natCast 8 := (two_mul_natCast 8).symm
  have hT3 : natCast 40 = (1 + 1) * natCast 8 + (1 + 1 + 1 + 1) * natCast 6 := by
    rw [two_mul_natCast, four_mul_natCast, ← natCast_add]
  have hT5 : natCast 24 = (1 + 1 + 1 + 1) * natCast 6 := (four_mul_natCast 6).symm
  refine hasDerivAt_congr_val hfull3 ?_
  rw [show (0 * (c * c * c * c) + natCast 34 * ((c + c) * (c * c) + (c * c) * (c + c)))
      * (1 / natCast 3) + natCast 34 * (c * c * c * c) * 0
      = natCast 136 * (c * c * c) * (1 / natCast 3) from by
        rw [show natCast 136 = (1 + 1 + 1 + 1) * natCast 34 from (four_mul_natCast 34).symm]
        mach_ring]
  unfold Rtan4
  rw [hT1, hT3, hT5]
  mach_mpoly [tan c, c, natCast 8, natCast 6, natCast 136]

theorem Rtan3_zero : Rtan3 0 = 0 := by unfold Rtan3; rw [tan_zero]; mach_ring

theorem Base4_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      * x * x * x * x :=
  mul_nonneg (Base3_nonneg hx0 hx) hx0

theorem Base4_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t)
        * t * t * t * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        * x * x * x * x :=
  bump_step (Base3_mono ht0 htx hx) htx (Base3_nonneg (le_trans ht0 htx) hx) ht0

/-- `|Rtan3(x)| ≤ 354560 · Mtan(x)^9 · x^5` — direct propagation from `Rtan4_bound`. -/
theorem Rtan3_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan3 x) ≤ (((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x) * x := by
  apply abs_mvt_step_bounded Rtan3 Rtan4 x ((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x) * x)
    (pi / (1 + 1)) hx0 hx (Base4_nonneg hx0 hx)
    (fun c hc0 hcR => Rtan3_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan3_zero
    (fun t ht0 htx => le_trans (Rtan4_bound t ht0 (lt_of_le_of_lt htx hx)) (Base4_mono ht0 htx hx))

/-! ## `Rtan2` (`Rtan1' = Rtan2`, `Rtan2' = Rtan3`). `Rtan2(y) = g2(y) − 2y − (8/3)y³ − (34/15)y⁵`. -/

noncomputable def Rtan2 (y : Real) : Real :=
  natCast 2 * tan y + natCast 2 * (tan y * tan y * tan y) - natCast 2 * y
    - natCast 8 * (y * y * y) * (1 / natCast 3)
    - natCast 34 * (y * y * y * y * y) * (1 / natCast 15)

theorem Rtan2_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan2 (Rtan3 c) c := by
  have h1 : HasDerivAt (fun y => natCast 2 * tan y) (0 * tan c + natCast 2 * (1 + tan c * tan c)) c :=
    HasDerivAt_mul (fun _ => natCast 2) tan 0 _ c (HasDerivAt_const (natCast 2) c) (HasDerivAt_tan' hc)
  have h3 : HasDerivAt (fun y => natCast 2 * (tan y * tan y * tan y))
      (0 * (tan c * tan c * tan c) + natCast 2
        * (((1 + tan c * tan c) * tan c + tan c * (1 + tan c * tan c)) * tan c
          + (tan c * tan c) * (1 + tan c * tan c))) c :=
    HasDerivAt_mul (fun _ => natCast 2) (fun y => tan y * tan y * tan y) 0 _ c
      (HasDerivAt_const (natCast 2) c) (hDtan_3 hc)
  have hy : HasDerivAt (fun y => natCast 2 * y) (0 * c + natCast 2 * 1) c :=
    HasDerivAt_mul (fun _ => natCast 2) (fun y => y) 0 1 c (HasDerivAt_const (natCast 2) c)
      (HasDerivAt_id c)
  have hy3raw : HasDerivAt (fun y => natCast 8 * (y * y * y))
      (0 * (c * c * c) + natCast 8 * (c * c + c * c + c * c)) c :=
    HasDerivAt_mul (fun _ => natCast 8) (fun y => y * y * y) 0 _ c
      (HasDerivAt_const (natCast 8) c) (hD_y3 c)
  have hy3raw2 : HasDerivAt (fun y => natCast 8 * (y * y * y) * (1 / natCast 3))
      ((0 * (c * c * c) + natCast 8 * (c * c + c * c + c * c)) * (1 / natCast 3)
        + natCast 8 * (c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 8 * (y * y * y)) (fun _ => 1 / natCast 3) _ 0 c hy3raw
      (HasDerivAt_const (1 / natCast 3) c)
  have hy3 : HasDerivAt (fun y => natCast 8 * (y * y * y) * (1 / natCast 3)) (natCast 8 * (c * c)) c :=
    hasDerivAt_congr_val hy3raw2
      (by
        have hred : natCast 24 * (1 / natCast 3) = natCast 8 :=
          natCast_frac_to_nat (b := 3) (by decide) (by decide : (24 : Nat) = 8 * 3)
        rw [show (0 * (c * c * c) + natCast 8 * (c * c + c * c + c * c)) * (1 / natCast 3)
              + natCast 8 * (c * c * c) * 0 = (c * c) * (natCast 24 * (1 / natCast 3)) from by
                rw [show natCast 24 = (1 + 1 + 1) * natCast 8 from (three_mul_natCast 8).symm]
                mach_ring,
            hred]
        mach_ring)
  have hy5raw : HasDerivAt (fun y => natCast 34 * (y * y * y * y * y))
      (0 * (c * c * c * c * c)
        + natCast 34 * ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c))) c :=
    HasDerivAt_mul (fun _ => natCast 34) (fun y => y * y * y * y * y) 0 _ c
      (HasDerivAt_const (natCast 34) c) (hD_y5 c)
  have hy5raw2 : HasDerivAt (fun y => natCast 34 * (y * y * y * y * y) * (1 / natCast 15))
      ((0 * (c * c * c * c * c)
          + natCast 34 * ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)))
          * (1 / natCast 15) + natCast 34 * (c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 34 * (y * y * y * y * y)) (fun _ => 1 / natCast 15) _ 0 c
      hy5raw (HasDerivAt_const (1 / natCast 15) c)
  have hy5 : HasDerivAt (fun y => natCast 34 * (y * y * y * y * y) * (1 / natCast 15))
      (natCast 34 * (c * c * c * c) * (1 / natCast 3)) c :=
    hasDerivAt_congr_val hy5raw2
      (by
        have hred : natCast 170 * (1 / natCast 15) = natCast 34 * (1 / natCast 3) :=
          natCast_frac_eq (b := 15) (d := 3) (by decide) (by decide) (by decide : 170 * 3 = 34 * 15)
        rw [show (0 * (c * c * c * c * c)
                + natCast 34 * ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)))
              * (1 / natCast 15) + natCast 34 * (c * c * c * c * c) * 0
              = (c * c * c * c) * (natCast 170 * (1 / natCast 15)) from by
                rw [show natCast 170 = (1 + 1 + 1 + 1 + 1) * natCast 34 from (five_mul_natCast 34).symm]
                mach_ring,
            hred]
        mach_ring)
  have hfull := HasDerivAt_add (fun y => natCast 2 * tan y)
    (fun y => natCast 2 * (tan y * tan y * tan y)) _ _ c h1 h3
  have hfull2 := HasDerivAt_sub (fun y => natCast 2 * tan y + natCast 2 * (tan y * tan y * tan y))
    (fun y => natCast 2 * y) _ _ c hfull hy
  have hfull3 := HasDerivAt_sub (fun y => natCast 2 * tan y + natCast 2 * (tan y * tan y * tan y)
      - natCast 2 * y) (fun y => natCast 8 * (y * y * y) * (1 / natCast 3)) _ _ c hfull2 hy3
  have hfull4 := HasDerivAt_sub (fun y => natCast 2 * tan y + natCast 2 * (tan y * tan y * tan y)
      - natCast 2 * y - natCast 8 * (y * y * y) * (1 / natCast 3))
    (fun y => natCast 34 * (y * y * y * y * y) * (1 / natCast 15)) _ _ c hfull3 hy5
  have hT2 : natCast 8 = natCast 2 + (1 + 1 + 1) * natCast 2 := by
    rw [three_mul_natCast, ← natCast_add]
  have hT4 : natCast 6 = (1 + 1 + 1) * natCast 2 := (three_mul_natCast 2).symm
  refine hasDerivAt_congr_val hfull4 ?_
  unfold Rtan3
  rw [hT2, hT4]
  mach_mpoly [tan c, c, natCast 2, natCast 8, natCast 34]

theorem Rtan2_zero : Rtan2 0 = 0 := by unfold Rtan2; rw [tan_zero]; mach_ring

theorem Base5_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      * x * x * x * x * x :=
  mul_nonneg (Base4_nonneg hx0 hx) hx0

theorem Base5_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t)
        * t * t * t * t * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        * x * x * x * x * x :=
  bump_step (Base4_mono ht0 htx hx) htx (Base4_nonneg (le_trans ht0 htx) hx) ht0

/-- `|Rtan2(x)| ≤ 354560 · Mtan(x)^9 · x^6` — direct propagation from `Rtan3_bound`. -/
theorem Rtan2_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan2 x) ≤ ((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x) * x) * x := by
  apply abs_mvt_step_bounded Rtan2 Rtan3 x (((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x) * x) * x)
    (pi / (1 + 1)) hx0 hx (Base5_nonneg hx0 hx)
    (fun c hc0 hcR => Rtan2_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan2_zero
    (fun t ht0 htx => le_trans (Rtan3_bound t ht0 (lt_of_le_of_lt htx hx)) (Base5_mono ht0 htx hx))

/-! ## `Rtan1` (`Rtan0' = Rtan1`, `Rtan1' = Rtan2`). `Rtan1(y) = g1(y) − y² − (2/3)y⁴ − (17/45)y⁶`. -/

noncomputable def Rtan1 (y : Real) : Real :=
  tan y * tan y - y * y - natCast 2 * (y * y * y * y) * (1 / natCast 3)
    - natCast 17 * (y * y * y * y * y * y) * (1 / natCast 45)

theorem Rtan1_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan1 (Rtan2 c) c := by
  have hy2 : HasDerivAt (fun y => y * y) (c + c) c := hD_y2 c
  have hy4raw : HasDerivAt (fun y => natCast 2 * (y * y * y * y))
      (0 * (c * c * c * c) + natCast 2 * ((c + c) * (c * c) + (c * c) * (c + c))) c :=
    HasDerivAt_mul (fun _ => natCast 2) (fun y => y * y * y * y) 0 _ c
      (HasDerivAt_const (natCast 2) c) (hD_y4 c)
  have hy4raw2 : HasDerivAt (fun y => natCast 2 * (y * y * y * y) * (1 / natCast 3))
      ((0 * (c * c * c * c) + natCast 2 * ((c + c) * (c * c) + (c * c) * (c + c)))
          * (1 / natCast 3) + natCast 2 * (c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 2 * (y * y * y * y)) (fun _ => 1 / natCast 3) _ 0 c hy4raw
      (HasDerivAt_const (1 / natCast 3) c)
  have hy4 : HasDerivAt (fun y => natCast 2 * (y * y * y * y) * (1 / natCast 3))
      (natCast 8 * (c * c * c) * (1 / natCast 3)) c := by
    refine hasDerivAt_congr_val hy4raw2 ?_
    rw [show natCast 8 = (1 + 1 + 1 + 1) * natCast 2 from (four_mul_natCast 2).symm]
    mach_ring
  have hy6raw : HasDerivAt (fun y => natCast 17 * (y * y * y * y * y * y))
      (0 * (c * c * c * c * c * c)
        + natCast 17 * ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c))) c :=
    HasDerivAt_mul (fun _ => natCast 17) (fun y => y * y * y * y * y * y) 0 _ c
      (HasDerivAt_const (natCast 17) c) (hD_y6 c)
  have hy6raw2 : HasDerivAt (fun y => natCast 17 * (y * y * y * y * y * y) * (1 / natCast 45))
      ((0 * (c * c * c * c * c * c)
          + natCast 17 * ((c * c + c * c + c * c) * (c * c * c) + (c * c * c) * (c * c + c * c + c * c)))
          * (1 / natCast 45) + natCast 17 * (c * c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 17 * (y * y * y * y * y * y)) (fun _ => 1 / natCast 45) _ 0 c
      hy6raw (HasDerivAt_const (1 / natCast 45) c)
  have hy6 : HasDerivAt (fun y => natCast 17 * (y * y * y * y * y * y) * (1 / natCast 45))
      (natCast 34 * (c * c * c * c * c) * (1 / natCast 15)) c :=
    hasDerivAt_congr_val hy6raw2
      (by
        have hred : natCast 102 * (1 / natCast 45) = natCast 34 * (1 / natCast 15) :=
          natCast_frac_eq (b := 45) (d := 15) (by decide) (by decide)
            (by decide : 102 * 15 = 34 * 45)
        rw [show (0 * (c * c * c * c * c * c)
                + natCast 17 * ((c * c + c * c + c * c) * (c * c * c)
                  + (c * c * c) * (c * c + c * c + c * c))) * (1 / natCast 45)
              + natCast 17 * (c * c * c * c * c * c) * 0
              = (c * c * c * c * c) * (natCast 102 * (1 / natCast 45)) from by
                rw [show natCast 102 = (1 + 1 + 1 + 1 + 1 + 1) * natCast 17
                    from (six_mul_natCast 17).symm]
                mach_ring,
            hred]
        mach_ring)
  have hfull1 := HasDerivAt_sub (fun y => tan y * tan y) (fun y => y * y) _ _ c (hDtan_2 hc) hy2
  have hfull2 := HasDerivAt_sub (fun y => tan y * tan y - y * y)
    (fun y => natCast 2 * (y * y * y * y) * (1 / natCast 3)) _ _ c hfull1 hy4
  have hfull3 := HasDerivAt_sub (fun y => tan y * tan y - y * y
      - natCast 2 * (y * y * y * y) * (1 / natCast 3))
    (fun y => natCast 17 * (y * y * y * y * y * y) * (1 / natCast 45)) _ _ c hfull2 hy6
  refine hasDerivAt_congr_val hfull3 ?_
  unfold Rtan2
  rw [natCast_two]
  mach_mpoly [tan c, c, natCast 2, natCast 8, natCast 34]

theorem Rtan1_zero : Rtan1 0 = 0 := by unfold Rtan1; rw [tan_zero]; mach_ring

theorem Base6_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      * x * x * x * x * x * x :=
  mul_nonneg (Base5_nonneg hx0 hx) hx0

theorem Base6_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t)
        * t * t * t * t * t * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        * x * x * x * x * x * x :=
  bump_step (Base5_mono ht0 htx hx) htx (Base5_nonneg (le_trans ht0 htx) hx) ht0

/-- `|Rtan1(x)| ≤ 354560 · Mtan(x)^9 · x^7` — direct propagation from `Rtan2_bound`. -/
theorem Rtan1_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan1 x) ≤ (((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x) * x) * x) * x := by
  apply abs_mvt_step_bounded Rtan1 Rtan2 x (((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x) * x) * x)
    (pi / (1 + 1)) hx0 hx (Base6_nonneg hx0 hx)
    (fun c hc0 hcR => Rtan1_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan1_zero
    (fun t ht0 htx => le_trans (Rtan2_bound t ht0 (lt_of_le_of_lt htx hx)) (Base6_mono ht0 htx hx))

/-- `y⁷ = y³·y⁴`, mirroring `hD_y5`/`hD_y6`'s construction (product of already-built lower
powers) — needed for `Rtan0`'s own `17/315·y⁷` term, one level past anything `SinTaylorRemainder`/
`CosTaylorRemainder` built. -/
theorem hD_y7raw : ∀ c : Real,
    HasDerivAt (fun y => (y * y * y) * (y * y * y * y))
      ((c * c + c * c + c * c) * (c * c * c * c)
        + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))) c := by
  intro c
  exact HasDerivAt_mul (fun y => y * y * y) (fun y => y * y * y * y) (c * c + c * c + c * c)
    ((c + c) * (c * c) + (c * c) * (c + c)) c (hD_y3 c) (hD_y4 c)

theorem hD_y7 : ∀ c : Real,
    HasDerivAt (fun y => y * y * y * y * y * y * y)
      ((c * c + c * c + c * c) * (c * c * c * c)
        + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))) c := by
  intro c
  exact HasDerivAt_of_eq (fun y => (y * y * y) * (y * y * y * y))
    (fun y => y * y * y * y * y * y * y) _ c (fun y => by mach_ring) (hD_y7raw c)

/-! ## `Rtan0` — THE TARGET. `Rtan0(y) = tan(y) − (y + y³/3 + (2/15)y⁵ + (17/315)y⁷)`, exactly
`eml_tan.v`'s claimed 4-term Maclaurin truncation, subtracted from the true `tan`. -/

noncomputable def Rtan0 (y : Real) : Real :=
  tan y - y - (y * y * y) * (1 / natCast 3) - natCast 2 * (y * y * y * y * y) * (1 / natCast 15)
    - natCast 17 * (y * y * y * y * y * y * y) * (1 / natCast 315)

theorem Rtan0_deriv {c : Real} (hc : abs c < pi / (1 + 1)) : HasDerivAt Rtan0 (Rtan1 c) c := by
  have hy1 : HasDerivAt (fun y => y) (1 : Real) c := HasDerivAt_id c
  have hy3raw : HasDerivAt (fun y => y * y * y) (c * c + c * c + c * c) c := hD_y3 c
  have hy3 : HasDerivAt (fun y => y * y * y * (1 / natCast 3)) (c * c) c := by
    refine hasDerivAt_congr_val
      (HasDerivAt_mul (fun y => y * y * y) (fun _ => 1 / natCast 3) _ 0 c hy3raw
        (HasDerivAt_const (1 / natCast 3) c)) ?_
    rw [show (c * c + c * c + c * c) * (1 / natCast 3) + (c * c * c) * 0
        = (c * c + c * c + c * c) * (1 / natCast 3) from by mach_ring, third_reduce]
  have hy5raw : HasDerivAt (fun y => natCast 2 * (y * y * y * y * y))
      (0 * (c * c * c * c * c)
        + natCast 2 * ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c))) c :=
    HasDerivAt_mul (fun _ => natCast 2) (fun y => y * y * y * y * y) 0 _ c
      (HasDerivAt_const (natCast 2) c) (hD_y5 c)
  have hy5raw2 : HasDerivAt (fun y => natCast 2 * (y * y * y * y * y) * (1 / natCast 15))
      ((0 * (c * c * c * c * c)
          + natCast 2 * ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)))
          * (1 / natCast 15) + natCast 2 * (c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 2 * (y * y * y * y * y)) (fun _ => 1 / natCast 15) _ 0 c
      hy5raw (HasDerivAt_const (1 / natCast 15) c)
  have hy5 : HasDerivAt (fun y => natCast 2 * (y * y * y * y * y) * (1 / natCast 15))
      (natCast 2 * (c * c * c * c) * (1 / natCast 3)) c := by
    refine hasDerivAt_congr_val hy5raw2 ?_
    have hred : natCast 10 * (1 / natCast 15) = natCast 2 * (1 / natCast 3) :=
      natCast_frac_eq (b := 15) (d := 3) (by decide) (by decide) (by decide : 10 * 3 = 2 * 15)
    rw [show (0 * (c * c * c * c * c)
            + natCast 2 * ((c + c) * (c * c * c) + (c * c) * (c * c + c * c + c * c)))
          * (1 / natCast 15) + natCast 2 * (c * c * c * c * c) * 0
          = (c * c * c * c) * (natCast 10 * (1 / natCast 15)) from by
            rw [show natCast 10 = (1 + 1 + 1 + 1 + 1) * natCast 2 from (five_mul_natCast 2).symm]
            mach_ring,
        hred]
    mach_ring
  have hy7raw : HasDerivAt (fun y => natCast 17 * (y * y * y * y * y * y * y))
      (0 * (c * c * c * c * c * c * c) + natCast 17
        * ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c)))) c :=
    HasDerivAt_mul (fun _ => natCast 17) (fun y => y * y * y * y * y * y * y) 0 _ c
      (HasDerivAt_const (natCast 17) c) (hD_y7 c)
  have hy7raw2 : HasDerivAt (fun y => natCast 17 * (y * y * y * y * y * y * y) * (1 / natCast 315))
      ((0 * (c * c * c * c * c * c * c) + natCast 17
          * ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))))
          * (1 / natCast 315) + natCast 17 * (c * c * c * c * c * c * c) * 0) c :=
    HasDerivAt_mul (fun y => natCast 17 * (y * y * y * y * y * y * y)) (fun _ => 1 / natCast 315)
      _ 0 c hy7raw (HasDerivAt_const (1 / natCast 315) c)
  have hy7 : HasDerivAt (fun y => natCast 17 * (y * y * y * y * y * y * y) * (1 / natCast 315))
      (natCast 17 * (c * c * c * c * c * c) * (1 / natCast 45)) c := by
    refine hasDerivAt_congr_val hy7raw2 ?_
    have hred : natCast 119 * (1 / natCast 315) = natCast 17 * (1 / natCast 45) :=
      natCast_frac_eq (b := 315) (d := 45) (by decide) (by decide)
        (by decide : 119 * 45 = 17 * 315)
    rw [show (0 * (c * c * c * c * c * c * c) + natCast 17
            * ((c * c + c * c + c * c) * (c * c * c * c) + (c * c * c) * ((c + c) * (c * c) + (c * c) * (c + c))))
          * (1 / natCast 315) + natCast 17 * (c * c * c * c * c * c * c) * 0
          = (c * c * c * c * c * c) * (natCast 119 * (1 / natCast 315)) from by
            rw [show natCast 119 = (1 + 1 + 1 + 1 + 1 + 1 + 1) * natCast 17
                from (seven_mul_natCast 17).symm]
            mach_ring,
        hred]
    mach_ring
  have hfull1 := HasDerivAt_sub tan (fun y => y) _ _ c (HasDerivAt_tan' hc) hy1
  have hfull2 := HasDerivAt_sub (fun y => tan y - y) (fun y => y * y * y * (1 / natCast 3))
    _ _ c hfull1 hy3
  have hfull3 := HasDerivAt_sub (fun y => tan y - y - y * y * y * (1 / natCast 3))
    (fun y => natCast 2 * (y * y * y * y * y) * (1 / natCast 15)) _ _ c hfull2 hy5
  have hfull4 := HasDerivAt_sub (fun y => tan y - y - y * y * y * (1 / natCast 3)
      - natCast 2 * (y * y * y * y * y) * (1 / natCast 15))
    (fun y => natCast 17 * (y * y * y * y * y * y * y) * (1 / natCast 315)) _ _ c hfull3 hy7
  refine hasDerivAt_congr_val hfull4 ?_
  unfold Rtan1
  mach_mpoly [tan c, c, natCast 2, natCast 17]

theorem Rtan0_zero : Rtan0 0 = 0 := by unfold Rtan0; rw [tan_zero]; mach_ring

theorem Base7_nonneg {x : Real} (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    (0 : Real) ≤ natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
      * x * x * x * x * x * x * x :=
  mul_nonneg (Base6_nonneg hx0 hx) hx0

theorem Base7_mono {t x : Real} (ht0 : 0 ≤ t) (htx : t ≤ x) (hx : x < pi / (1 + 1)) :
    natCast 354560
        * (Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t * Mtan t)
        * t * t * t * t * t * t * t
      ≤ natCast 354560
        * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x)
        * x * x * x * x * x * x * x :=
  bump_step (Base6_mono ht0 htx hx) htx (Base6_nonneg (le_trans ht0 htx) hx) ht0

/-- **THE MAIN RESULT.** `|tan(x) − (x + x³/3 + (2/15)x⁵ + (17/315)x⁷)| ≤ 354560 · Mtan(x)^9 · x^8`
for `x ∈ [0,1]` — the real-valued forward-error bound for `eml_tan.v`'s exact 4-term Maclaurin
truncation. `sorryAx`-free. -/
theorem Rtan0_bound (x : Real) (hx0 : 0 ≤ x) (hx : x < pi / (1 + 1)) :
    abs (Rtan0 x) ≤ ((((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x) * x) * x) * x) * x := by
  apply abs_mvt_step_bounded Rtan0 Rtan1 x (((((((natCast 354560
      * (Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x * Mtan x) * x)
      * x) * x * x) * x) * x) * x))
    (pi / (1 + 1)) hx0 hx (Base7_nonneg hx0 hx)
    (fun c hc0 hcR => Rtan0_deriv (by rw [abs_of_nonneg hc0]; exact hcR)) Rtan0_zero
    (fun t ht0 htx => le_trans (Rtan1_bound t ht0 (lt_of_le_of_lt htx hx)) (Base7_mono ht0 htx hx))

end MachLib.Real

