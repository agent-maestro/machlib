import MachLib.Basic
import MachLib.Lemmas
import MachLib.Forge
import MachLib.Ring
import MachLib.FPModel
import MachLib.ErrorAlgebra
import MachLib.ErrorAlgebraTrans
import MachLib.ForwardError

/-!
# Hybrid forward error — arithmetic ∘ transcendental, unified

The arithmetic algebra (`ForwardError`, relative two-sided `Renc`) and the
transcendental rules (`ErrorAlgebraTrans`, `exp_grow`/`sin_grow`/`cos_grow`)
speak two dialects — *relative* and *absolute* error. They unify through one
currency: the **absolute forward-error bound** `|v − ve| ≤ E`.

* the arithmetic side *produces* it — `renc_fwd : Renc d w v ve → |v − ve| ≤
  ((1+w)^d − 1)·ve`;
* the transcendental side *consumes* it — `exp_grow`/`sin_grow`/`cos_grow` take an
  argument-error bound `E` and return the output's forward error.

So `renc_fwd` is the bridge: relative enclosure → absolute `E` → transcendental.
This file proves it end-to-end on kernels that *mix* both — the Gaussian
`exp(−(x²+y²))` (the `e^{−S}` universal shape) and `sin(x²)`. Each output forward
error is a genuine `|p − f(exact)|` bound, assembled by composing the arithmetic
algebra into the transcendental rule. `sorryAx`-free.
-/

namespace MachLib.Real

/-- Negation preserves absolute error (exact sign flip). The connective tissue
when a transcendental's argument is a negated arithmetic subtree (`exp(−S)`). -/
theorem neg_err {a b E : Real} (h : abs (a - b) ≤ E) : abs ((-a) - (-b)) ≤ E := by
  apply abs_le_of
  · rw [show (-a) - (-b) = -(a - b) from by mach_ring]; exact le_trans (neg_le_abs (a - b)) h
  · rw [show -((-a) - (-b)) = a - b from by mach_ring]; exact le_trans (le_abs_self (a - b)) h

/-- **Hybrid: Gaussian `exp(−(x²+y²))`** — the `e^{−S}` shape. The arithmetic
forward error of `x²+y²` (`length_sq2_fwd_compose`, `Renc`-based) becomes the
absolute argument error `E = ((1+w)²−1)·(x²+y²)`, which `exp_grow` converts to the
output's relative factor `exp(E)·(1+w)`. End-to-end forward error for an
exp-of-arithmetic kernel — the relative→absolute→transcendental bridge in action. -/
theorem gaussian2_fwd {w x y px py s p : Real}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x)) (hpy : RoundsW w py (y * y))
    (hs : RoundsW w s (px + py))
    (hp : RoundsW w p (exp (-s))) :
    abs (p - exp (-(x * x + y * y)))
      ≤ exp (-(x * x + y * y))
          * (exp ((npow 2 (1 + w) - 1) * (x * x + y * y)) * (1 + w) - 1) := by
  have hxy : 0 ≤ x * x + y * y := add_nonneg_ea (mul_self_nonneg x) (mul_self_nonneg y)
  have hsum_err : abs (s - (x * x + y * y)) ≤ (npow 2 (1 + w) - 1) * (x * x + y * y) :=
    length_sq2_fwd_compose hw0 hw1 hpx hpy hs
  have hE : 0 ≤ (npow 2 (1 + w) - 1) * (x * x + y * y) :=
    mul_nonneg (sub_nonneg_of_le (one_le_npow (1 + w) (le_add_of_nonneg_right hw0) 2)) hxy
  exact exp_grow hw0 hw1 hE (neg_err hsum_err) hp

/-- **Hybrid: `sin(x²)`** — the bounded-Lipschitz transcendental over an
arithmetic argument. The argument forward error `E = ((1+w)−1)·x²` (one rounded
square via `renc_round`/`renc_fwd`) stays *absolute* through `sin_grow`:
`|p − sin(x²)| ≤ w + E`. -/
theorem sin_sq_fwd {w x px p : Real}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    (hpx : RoundsW w px (x * x))
    (hp : RoundsW w p (sin px)) :
    abs (p - sin (x * x)) ≤ w + (npow 1 (1 + w) - 1) * (x * x) := by
  have hxx : 0 ≤ x * x := mul_self_nonneg x
  have harg : abs (px - x * x) ≤ (npow 1 (1 + w) - 1) * (x * x) :=
    renc_fwd hw0 hw1 hxx (renc_round hw0 hw1 hxx hpx)
  exact sin_grow hw0 harg hp

end MachLib.Real
