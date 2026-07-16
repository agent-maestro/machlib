import MachLib.TransNodes
import MachLib.Decimal

/-!
# `log10` — algebraic link to `log`, Lipschitz bound, and forward-error node

`MachLib.Log` ships `log10` as an axiom with only an implicit exp-linking identity
(`log10_def : 0 < x → exp (log10 x * log (natCast 10)) = x`) — no direct algebraic tie to `log`
(natural log) and no Lipschitz bound, so it could not enter the certified `absErr` fold. This file
derives both, **without adding any new axioms**:

1. `log_ten_pos : 0 < log (natCast 10)` — `1 < natCast 10` (via `natCast_succ` unfolding
   `10 = 9 + 1` and `natCast_pos` on `9`), then `log_lt_log` off `log_one`.
2. `log10_eq_log_div_log_ten` — `log10 x = log x / log (natCast 10)` for `x > 0`, by chaining
   `log10_def` and `exp_log` through `exp_injective`, then `eq_div_of_mul_eq`.
3. `log10_lip_local` — `log10` is `1/(lo·log 10)`-Lipschitz on `[lo,hi]` (`lo > 0`): a straight
   rescale of `log_lip_local` (`TransNodes.lean`) by the constant `1/log(natCast 10)`, closed by
   cross-multiplying (`div_le_div_iff`) rather than by splitting the reciprocal of a product.
4. `absenc_log10_local` — the forward-error node, identical shape to `absenc_log_local`
   (`TransNodes.lean`), via `absenc_lip_local` + `log10_lip_local`.

`sorryAx`-free; 0 new axioms — everything here is a theorem derived from the `log10_def`/`log10_zero`
axioms already in `MachLib.Log`.
-/

namespace MachLib.Real

/-! ## `log (natCast 10) > 0` -/

/-- `1 < natCast 10`. Bookkeeping only: `10 = 9 + 1` (`natCast_succ`, where `9 + 1` reduces to `10`
on `Nat`), `0 < natCast 9` (`natCast_pos`), then `add_lt_add_left` + `add_comm` land `1 < natCast 9 + 1`.
-/
theorem one_lt_natCast_ten : (1 : Real) < natCast 10 := by
  have h9 : 0 < natCast 9 := natCast_pos (by decide)
  have h10 : natCast 10 = natCast 9 + 1 := natCast_succ 9
  have hstep : (1 : Real) < natCast 9 + 1 := by
    have h := add_lt_add_left h9 1
    rw [add_zero, add_comm 1 (natCast 9)] at h
    exact h
  rw [h10]; exact hstep

/-- **`log (natCast 10) > 0`.** From `one_lt_natCast_ten` and `log`'s strict monotonicity
(`log_lt_log`) off `log_one`. -/
theorem log_ten_pos : 0 < log (natCast 10) := by
  have h := log_lt_log zero_lt_one_ax one_lt_natCast_ten
  rwa [log_one] at h

/-! ## `log10 = log / log 10` -/

/-- **`log10`'s algebraic link to `log`.** Derived (not axiomatised) from `log10_def` + `exp_log`
via `exp_injective`, then `eq_div_of_mul_eq` using `log_ten_pos`. -/
theorem log10_eq_log_div_log_ten {x : Real} (hx : 0 < x) :
    log10 x = log x / log (natCast 10) := by
  have h1 : exp (log10 x * log (natCast 10)) = exp (log x) := by
    rw [log10_def x hx, exp_log hx]
  exact eq_div_of_mul_eq (ne_of_gt log_ten_pos) (exp_injective h1)

/-! ## Lipschitz bound -/

/-- **`log10` is `1/(lo·log 10)`-Lipschitz on `[lo,hi]`** (`lo > 0`) — the straight rescale of
`log_lip_local` by the constant `1/log(natCast 10)`. Closed by rewriting both sides as fractions over
`log(natCast 10)` / `lo·log(natCast 10)` and cross-multiplying (`div_le_div_iff`), rather than by
splitting `1/(lo·L)` into `(1/lo)·(1/L)` (no general reciprocal-of-product lemma was needed). -/
theorem log10_lip_local (lo hi : Real) (hlo : 0 < lo) :
    ∀ p q : Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
      abs (log10 p - log10 q) ≤ (1 / (lo * log (natCast 10))) * abs (p - q) := by
  intro p q hlp hph hlq hqh
  have hp0 : 0 < p := lt_of_lt_of_le hlo hlp
  have hq0 : 0 < q := lt_of_lt_of_le hlo hlq
  have hL : 0 < log (natCast 10) := log_ten_pos
  have hloL : 0 < lo * log (natCast 10) := mul_pos hlo hL
  have heq : log10 p - log10 q = (log p - log q) / log (natCast 10) := by
    rw [log10_eq_log_div_log_ten hp0, log10_eq_log_div_log_ten hq0,
        div_sub_div_same (ne_of_gt hL)]
  rw [heq, abs_div_pos hL,
      show (1 / (lo * log (natCast 10))) * abs (p - q)
          = abs (p - q) / (lo * log (natCast 10)) from by
        rw [div_def (abs (p - q)) (lo * log (natCast 10)) (ne_of_gt hloL), mul_comm],
      div_le_div_iff hL hloL]
  have hbound : abs (log p - log q) ≤ (1 / lo) * abs (p - q) :=
    log_lip_local lo hi hlo p q hlp hph hlq hqh
  have hstep : abs (log p - log q) * (lo * log (natCast 10))
      ≤ ((1 / lo) * abs (p - q)) * (lo * log (natCast 10)) :=
    mul_le_mul_of_nonneg_right hbound (le_of_lt hloL)
  have hcollapse : ((1 / lo) * abs (p - q)) * (lo * log (natCast 10))
      = abs (p - q) * log (natCast 10) := by
    rw [show ((1 / lo) * abs (p - q)) * (lo * log (natCast 10))
          = ((1 / lo) * lo) * (abs (p - q) * log (natCast 10)) from by mach_ring,
        mul_comm (1 / lo) lo, mul_inv lo (ne_of_gt hlo), one_mul_thm]
  rwa [hcollapse] at hstep

/-! ## Forward-error node -/

/-- **The `log10` forward-error node.** Identical shape to `absenc_log_local` (`TransNodes.lean`),
via `absenc_lip_local` + `log10_lip_local`. -/
theorem absenc_log10_local {flx xe Ex flf Eround lo hi : Real} (hlo : 0 < lo)
    (hx : AbsEnc Ex flx xe)
    (hflx_lo : lo ≤ flx) (hflx_hi : flx ≤ hi) (hxe_lo : lo ≤ xe) (hxe_hi : xe ≤ hi)
    (hround : abs (flf - log10 flx) ≤ Eround) :
    AbsEnc (Eround + (1 / (lo * log (natCast 10))) * Ex) flf (log10 xe) :=
  absenc_lip_local (le_of_lt (one_div_pos_of_pos (mul_pos hlo log_ten_pos)))
    (log10_lip_local lo hi hlo) hx hflx_lo hflx_hi hxe_lo hxe_hi hround

end MachLib.Real
