import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.FPModel
import MachLib.Exp
import MachLib.Differentiation
import MachLib.Rolle
import MachLib.AbsoluteError

/-!
# `exp` is locally Lipschitz — the bound the absolute forward-error fold needs for an unbounded primitive

`TrigLipschitz`/`HyperbolicLipschitz` give the GLOBALLY-Lipschitz primitives (`sin`, `cos`, `tanh`:
`L = 1`). `exp` has unbounded derivative (`exp' = exp`), so it is not globally Lipschitz — but on any
`(−∞, hi]` its slope is bounded by `exp hi`, hence it is `exp hi`-Lipschitz there. That LOCAL bound is
exactly what `AbsoluteError.absenc_lip_local` consumes to fold a `tr1` `exp` node over an arithmetic
subtree. Derived from `mean_value_theorem_ct` + `HasDerivAt_exp` + `exp_monotone`, the same MVT route
`sin_lipschitz` uses — now with the sound closed-interval MVT (`rolle_ct`). `log` (`L = 1/lo` on
`[lo, ∞)`), `sinh`/`cosh` (`HyperbolicLipschitz` already has their bounded-domain versions) follow the
same shape.
-/

namespace MachLib.Real

/-- `|x − y| = |y − x|` (local copy — the base `abs_sub_comm` lives in `TrigLipschitz`, which this file
does not import). -/
private theorem abs_sub_comm' (x y : Real) : abs (x - y) = abs (y - x) := by
  have h : y - x = -(x - y) := by mach_ring
  rw [h, abs_neg]

/-- One-sided MVT bound: for `a < b ≤ hi`, `|exp b − exp a| ≤ exp hi · (b − a)`. The MVT slope `exp c`
(for `c ∈ (a,b)`) is `≤ exp hi` since `c < b ≤ hi` and `exp` is monotone. -/
theorem exp_lip_lt {a b hi : Real} (hab : a < b) (hbhi : b ≤ hi) :
    abs (exp b - exp a) ≤ exp hi * (b - a) := by
  obtain ⟨c, f', _, hcb, hd, heq⟩ :=
    mean_value_theorem_ct exp a b hab (fun c _ _ => ⟨exp c, HasDerivAt_exp c⟩)
  have hf' : f' = exp c := HasDerivAt_unique exp f' (exp c) c hd (HasDerivAt_exp c)
  have hba_nn : 0 ≤ b - a := sub_nonneg_of_le (le_of_lt hab)
  rw [heq, hf', abs_mul, abs_of_nonneg hba_nn, abs_of_nonneg (le_of_lt (exp_pos c))]
  exact mul_le_mul_of_nonneg_right (exp_monotone (le_trans (le_of_lt hcb) hbhi)) hba_nn

/-- **`exp` is `exp hi`-Lipschitz on `[lo, hi]`** — the local-Lipschitz hypothesis of
`absenc_lip_local`, instantiated for the canonical unbounded-derivative primitive. For any `p, q ≤ hi`,
`|exp p − exp q| ≤ exp hi · |p − q|`. -/
theorem exp_lip_local (lo hi : Real) :
    ∀ p q : Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
      abs (exp p - exp q) ≤ exp hi * abs (p - q) := by
  intro p q _ hphi _ hqhi
  rcases lt_total p q with h | h | h
  · have hpq : abs (p - q) = q - p := by
      rw [abs_sub_comm' p q]; exact abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))
    rw [abs_sub_comm' (exp p) (exp q), hpq]
    exact exp_lip_lt h hqhi
  · subst h
    rw [show exp p - exp p = (0 : Real) from by mach_ring, abs_zero]
    exact mul_nonneg (le_of_lt (exp_pos hi)) (abs_nonneg (p - p))
  · rw [show abs (p - q) = p - q from abs_of_nonneg (sub_nonneg_of_le (le_of_lt h))]
    exact exp_lip_lt h hphi

/-- **The `exp` forward-error node** — `absenc_lip_local` instantiated for `exp` (a genuinely
unbounded-derivative primitive). If the input `flx` is within `Ex` of the exact `xe`, both lie in
`[lo,hi]`, and the computed `flf` is within the primitive's rounding `Eround` of `exp flx`, then `flf` is
within `Eround + (exp hi)·Ex` of the exact `exp xe`. Concrete proof that the local-Lipschitz node is
non-vacuous on a real non-globally-Lipschitz primitive; feeds the EML `tr1` `exp` fold once wired. -/
theorem absenc_exp_local {flx xe Ex flf Eround lo hi : Real}
    (hx : AbsEnc Ex flx xe)
    (hflx_lo : lo ≤ flx) (hflx_hi : flx ≤ hi) (hxe_lo : lo ≤ xe) (hxe_hi : xe ≤ hi)
    (hround : abs (flf - exp flx) ≤ Eround) :
    AbsEnc (Eround + exp hi * Ex) flf (exp xe) :=
  absenc_lip_local (le_of_lt (exp_pos hi)) (exp_lip_local lo hi) hx
    hflx_lo hflx_hi hxe_lo hxe_hi hround

end MachLib.Real
