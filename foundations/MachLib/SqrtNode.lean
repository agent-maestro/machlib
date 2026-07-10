import MachLib.TransNodes
import MachLib.OperatorBasisComplete

/-!
# The `sqrt` forward-error node — the asymmetric-domain twin of `absenc_log_local`

`TransNodes` built `log` (`1/lo`-Lipschitz on `[lo, ∞)`, `lo > 0`). `sqrt` is the other one-sided-domain
primitive control/DSP kernels reach for (RMS, magnitude, std-dev). It is `1/(2√lo)`-Lipschitz on
`[lo, ∞)` (`sqrt' = 1/(2√x)`, decreasing, so bounded by its value at the left endpoint) — the exact
analog of `log`, with constant `1/(√lo + √lo)`. `OperatorBasisComplete.sqrt_lipschitz_bound` already
proves the two-point bound; here it is wrapped into an `absenc_lip_local` node the fold can call.
`sorryAx`-free.
-/

namespace MachLib.Real

/-- **`sqrt` is `1/(√lo+√lo)`-Lipschitz on `[lo, hi]`** (`lo > 0`) — the `absenc_lip_local` hypothesis
for `sqrt`. Wraps `sqrt_lipschitz_bound`'s `|·−·|/(√lo+√lo)` into the fold's `L·|·−·|` shape. -/
theorem sqrt_lip_local (lo hi : Real) (hlo : 0 < lo) :
    ∀ p q : Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
      abs (sqrt p - sqrt q) ≤ (1 / (sqrt lo + sqrt lo)) * abs (p - q) := by
  intro p q hlp _ hlq _
  have hdne : sqrt lo + sqrt lo ≠ 0 := ne_of_gt (add_pos (sqrt_pos hlo) (sqrt_pos hlo))
  rw [show (1 / (sqrt lo + sqrt lo)) * abs (p - q) = abs (p - q) / (sqrt lo + sqrt lo)
        from by rw [div_def (abs (p - q)) (sqrt lo + sqrt lo) hdne]; exact mul_comm _ _]
  exact sqrt_lipschitz_bound hlo hlp hlq

/-- **The `sqrt` forward-error node.** Input within `Ex`, both in `[lo,hi]` (`lo > 0`) ⟹ output within
`Eround + (1/(√lo+√lo))·Ex`. -/
theorem absenc_sqrt_local {flx xe Ex flf Eround lo hi : Real} (hlo : 0 < lo)
    (hx : AbsEnc Ex flx xe)
    (hflx_lo : lo ≤ flx) (hflx_hi : flx ≤ hi) (hxe_lo : lo ≤ xe) (hxe_hi : xe ≤ hi)
    (hround : abs (flf - sqrt flx) ≤ Eround) :
    AbsEnc (Eround + (1 / (sqrt lo + sqrt lo)) * Ex) flf (sqrt xe) :=
  absenc_lip_local (le_of_lt (one_div_pos_of_pos (add_pos (sqrt_pos hlo) (sqrt_pos hlo))))
    (sqrt_lip_local lo hi hlo) hx hflx_lo hflx_hi hxe_lo hxe_hi hround

end MachLib.Real
