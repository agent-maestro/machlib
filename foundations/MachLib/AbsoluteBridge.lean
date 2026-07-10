import MachLib.FloatRealBridge
import MachLib.AbsoluteError

/-!
# The absolute forward-error fold, wired through the emitted C — a CANCELLING kernel

`FloatRealBridge` connects T1's emitted C (`evalC ∘ emitC`) to T3's *relative* forward error, but
only for cancellation-free non-negative trees (`x²+y²`, `(x·y)·z`) — `Renc` is vacuous once a
subtraction cancels. This file closes that gap with the **absolute** fold (`AbsoluteError.AbsEnc`),
on the canonical cancelling kernel: the 2×2 determinant / cross-product `x·y − z·w`.

The result is the same span as `pipeline_sqSum`/`pipeline_prod3` — EML source ─emitC─▶ C ─evalC─▶
Float ─toR─▶ Real, provably within a forward-error bound of the exact ℝ — but now VALID UNDER
CANCELLATION (`x·y ≈ z·w`, where the relative bound is unbounded and `Renc` does not apply). The
inputs may have ANY sign: `AbsEnc` carries no non-negativity hypothesis, unlike the relative fold.

Trust boundary unchanged: the `FPBridge` per-op roundings + the C compiler. `sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/-- The EML expression `x·y − z·w` — a 2×2 determinant / cross-product, the canonical CANCELLING
kernel (it loses all relative accuracy when `x·y ≈ z·w`, e.g. a near-singular Jacobian / Wronskian). -/
def detEML : EML :=
  .bin .sub (.bin .mul (.var "x") (.var "y")) (.bin .mul (.var "z") (.var "w"))

/-- **Absolute bridge capstone (this kernel).** T2's own `evalEML` for `x·y − z·w`, through `toR`, is
within the ABSOLUTE forward error `u·(2+u)·(|X·Y| + |Z·W|)` of the exact `X·Y − Z·W` — assembled from
two `br.mul` rounded products and one `br.sub`, via `absenc_sub_rounded`. No sign hypothesis; holds in
the cancelling regime `X·Y ≈ Z·W` where the relative `Renc` bound is vacuous. -/
theorem evalEML_det_abs {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env) :
    AbsEnc (u * (1 + 1 + u) * (abs (toR (env "x").toF * toR (env "y").toF)
                              + abs (toR (env "z").toF * toR (env "w").toF)))
      (toR (evalEML i1 i2 env detEML).toF)
      (toR (env "x").toF * toR (env "y").toF - toR (env "z").toF * toR (env "w").toF) := by
  have h : (evalEML i1 i2 env detEML).toF
      = ((env "x").toF * (env "y").toF) - ((env "z").toF * (env "w").toF) := rfl
  rw [h]
  exact absenc_sub_rounded (br.mul (env "x").toF (env "y").toF)
    (br.mul (env "z").toF (env "w").toF)
    (br.sub ((env "x").toF * (env "y").toF) ((env "z").toF * (env "w").toF))

/-- **End-to-end pipeline capstone (`x·y − z·w`, cancelling).** The value the *emitted C* computes —
`evalC` of `emitC`, the actual translated program — viewed through `toR`, is within the ABSOLUTE
forward-error bound of the exact `X·Y − Z·W`. Proof: rewrite the emitted-C result to the EML Float
value by `emitC_correct` (T1), then apply the absolute bridge capstone. Same span as the relative
`pipeline_*`, now across a cancellation. -/
theorem pipeline_det {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env) :
    AbsEnc (u * (1 + 1 + u) * (abs (toR (env "x").toF * toR (env "y").toF)
                              + abs (toR (env "z").toF * toR (env "w").toF)))
      (toR (evalC r1 r2 env (emitC detEML)).toF)
      (toR (env "x").toF * toR (env "y").toF - toR (env "z").toF * toR (env "w").toF) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 detEML env]
  exact evalEML_det_abs br i1 i2 env

end Certcom
