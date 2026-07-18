import MachLib.SinTaylorRemainder
import MachLib.TanLipschitz

/-!
# `tan` Taylor-remainder bound — Group B, BLOCKED by a real tooling wall, not just harder math

`eml_tan.v` computes the 4-term Maclaurin truncation `tan(x) ≈ x + x³/3 + 2x⁵/15 + 17x⁷/315`.
Unlike `sin/cos/sinh/cosh` (whose derivatives cycle back to themselves after a few steps,
making the remainder chain bottom out cleanly), `tan' = sec² = 1+tan²` means every derivative of
`tan` is a HIGHER-DEGREE polynomial in `tan` itself — the chain never closes. Differentiating by
hand (`T := tan y`, `S := 1+T² = sec² y`, so `T' = S`):

`g0=T`, `g1=1+T²`, `g2=2T+2T³`, `g3=2+8T²+6T⁴`, `g4=16T+40T³+24T⁵`,
`g5=16+136T²+240T⁴+120T⁶`, `g6=272T+1232T³+1680T⁵+720T⁷`,
`g7=272+3968T²+12096T⁴+13440T⁶+5040T⁸`, `g8=7936T+56320T³+129024T⁵+120960T⁷+40320T⁹` — each
obtained from the last via `(⋯)' = (⋯)·T' = (⋯)(1+T²)`, confirmed against the known Maclaurin
coefficients of `tan` (`g_{2k-1}(0)/(2k-1)!` reproduces `1, 1/3, 2/15, 17/315`). This needs
**8 MVT levels** (`R0..R7`, vs sin's 6) with mixed `T`-power/`y`-power terms combined via
triangle-inequality decomposition rather than a single monomial chain — genuinely harder math than
sin/sinh, but tractable in principle.

**What's actually built and verified here (sorryAx-free)**: `tan_mono`/`tan_nonneg` (MVT-derived,
mirroring `sinh_mono`/`cosh_mono` — `tan` monotonicity wasn't in `MachLib` yet) and
`one_lt_pi_div_two` (so the certified domain `x∈[0,1]` stays inside `tan`'s differentiable range,
since `1 < π/2` follows from the existing `pi_gt_three` axiom). These are genuine, reusable
additions regardless of what happens to the rest of this file.

**What's NOT done, and WHY — empirically confirmed, not just estimated as tedious.** The R0..R7
chain needs coefficients in the thousands (3968, 12096, 13440, 5040, and `g8`'s 40320, 129024,
etc.) — MachLib's reals have no native numeral literals beyond 0/1, so these must be built as
products of small flat sums (the same trick `sevenhundredtwenty := six*onetwenty` already uses at
720). Tested directly: `mach_ring` hits `maximum recursion depth`/`(kernel) deep recursion
detected` trying to verify even a SINGLE sum-of-two-such-products identity (e.g. `272+3696=3968`,
each side built the same way `sevenhundredtwenty` is) — not a timeout that a bigger
`maxRecDepth` fixes (tried `set_option maxRecDepth 4000`, still failed), and not specific to
*collecting* like terms either: a follow-up test asking `mach_ring` to merely *distribute*
`(A + B·T²)·(1+T²)` WITHOUT ever collecting the two resulting `T²`-coefficient terms into one
combined number (same A, B scale) didn't error, it hung past a 60s wall-clock timeout. A
calibration test confirmed the wall isn't about a large numeral merely *existing* in a goal —
`midsize·T = midsize·T` (trivial reflexivity, ~2000-scale factor) succeeds instantly — it's
specifically triggered once `mach_ring` has to actually *expand/normalize* an expression containing
one. Every genuine derivative-matching step in this chain needs exactly that kind of expansion, so
this isn't a matter of more time or a cleverer proof shape — the current arithmetic tactics
(`mach_ring`/`mach_mpoly`) cannot verify identities at the scale this specific certificate needs.
Reported back to the user rather than continuing to grind on a wall further effort was unlikely to
move. Fixing this for real would mean either a `norm_num`-style numeral-arithmetic tactic for
`MachLib.Real` (a separate tactic-engineering project) or finding a fundamentally different bound
that never needs coefficients past what flat-sum/small-product numerals can represent (no such
bound found yet for `tan` specifically).
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

end MachLib.Real
