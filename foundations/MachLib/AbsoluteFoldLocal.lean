import MachLib.AbsoluteFold
import MachLib.ExpLipschitz
import MachLib.TransNodes

/-!
# A LOCAL-Lipschitz transcendental over an arithmetic subtree, through the emitted C

`pipeline_tr1_of_arith` put a GLOBALLY-Lipschitz primitive over an arithmetic tree. This is its
local-Lipschitz analog: an `exp`/`log`/`sinh`/`cosh` node over an arithmetic subtree, where the primitive
is Lipschitz only on `[lo,hi]` and BOTH the computed input `toR (evalEML e).toF` and the exact input
`exactR e` are supplied to lie in `[lo,hi]`. Composes `evalEML_absErr` (the arithmetic fold) with
`absenc_lip_local`. Concrete `exp` (`L = exp hi`) and `log` (`L = 1/lo`) instances follow from
`ExpLipschitz`/`TransNodes`.

Scope note (honest): this is ONE local transcendental layer over arithmetic — e.g. `exp(x·y − z·w)`.
FULL recursive local-Lipschitz nesting (a local primitive over a subtree that itself contains local
transcendentals) is genuinely harder: the domain condition at each node (`toR (evalEML e).toF ∈ [lo,hi]`)
depends on the accumulated absolute error `E` at that node, which is existential — so the range and the
error must be propagated together (interval arithmetic with directed rounding). That coupling is the
remaining open piece; the globally-Lipschitz nesting (`AbsoluteFoldNest`) avoids it because those
primitives need no domain. `sorryAx`-free.
-/

namespace Certcom

open MachLib.Real

/-- **Local-Lipschitz transcendental over an arithmetic subtree, through the emitted C.** A unary
primitive `t` — real semantics `f`, `L`-Lipschitz on `[lo,hi]` — applied to an arithmetic `e`, where both
the computed and exact inputs lie in `[lo,hi]`: the emitted C's value, through `toR`, is within
`Eround + L·(absErr … e)` of the exact `f (exactR … e)`. Composes `evalEML_absErr` with
`absenc_lip_local`. -/
theorem pipeline_tr1_of_arith_local {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (f : MachLib.Real → MachLib.Real) (L Eround lo hi : MachLib.Real)
    (hLnn : 0 ≤ L)
    (hLip : ∀ p q : MachLib.Real, lo ≤ p → p ≤ hi → lo ≤ q → q ≤ hi →
        abs (f p - f q) ≤ L * abs (p - q))
    (e : EML) (he : IsArith e)
    (hflx_lo : lo ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ hi)
    (hxe_lo : lo ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ hi)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - f (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + L * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (f (exactR toR env e)) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 (tr1OfEML t e) env]
  show AbsEnc (Eround + L * absErr toR env e)
      (toR (i1 t (evalEML i1 i2 env e).toF)) (f (exactR toR env e))
  exact absenc_lip_local hLnn hLip (evalEML_absErr br i1 i2 env e he)
    hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`exp` over an arithmetic subtree** (`L = exp hi`) — instance of `pipeline_tr1_of_arith_local`. -/
theorem pipeline_exp_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (lo hi Eround : MachLib.Real) (e : EML) (he : IsArith e)
    (hflx_lo : lo ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ hi)
    (hxe_lo : lo ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ hi)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - exp (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + exp hi * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (exp (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t exp (exp hi) Eround lo hi
    (le_of_lt (exp_pos hi)) (exp_lip_local lo hi) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`log` over an arithmetic subtree** (`L = 1/lo`, `lo > 0`) — instance of the local pipeline. -/
theorem pipeline_log_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (lo hi Eround : MachLib.Real) (hlo : 0 < lo) (e : EML) (he : IsArith e)
    (hflx_lo : lo ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ hi)
    (hxe_lo : lo ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ hi)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - log (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + (1 / lo) * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (log (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t log (1 / lo) Eround lo hi
    (le_of_lt (one_div_pos_of_pos hlo)) (log_lip_local lo hi hlo) e he
    hflx_lo hflx_hi hxe_lo hxe_hi hround

end Certcom
