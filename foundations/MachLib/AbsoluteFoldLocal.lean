import MachLib.AbsoluteFold
import MachLib.ExpLipschitz
import MachLib.TransNodes
import MachLib.SqrtNode
import MachLib.Log10Lipschitz
import MachLib.InverseTrigBounded
import MachLib.HyperbolicLipschitz

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

/-- **`sqrt` over an arithmetic subtree** (`L = 1/(√lo+√lo)`, `lo > 0`) — one-sided domain, the exact
analog of `log`. Instance of the local pipeline via `SqrtNode.sqrt_lip_local`. -/
theorem pipeline_sqrt_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (lo hi Eround : MachLib.Real) (hlo : 0 < lo) (e : EML) (he : IsArith e)
    (hflx_lo : lo ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ hi)
    (hxe_lo : lo ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ hi)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - sqrt (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + (1 / (sqrt lo + sqrt lo)) * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (sqrt (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t sqrt (1 / (sqrt lo + sqrt lo)) Eround lo hi
    (le_of_lt (one_div_pos_of_pos (add_pos (sqrt_pos hlo) (sqrt_pos hlo))))
    (sqrt_lip_local lo hi hlo) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`log10` over an arithmetic subtree** (`L = 1/(lo·log 10)`, `lo > 0`) — one-sided domain,
straight rescale of `log`'s. Instance of the local pipeline via `Log10Lipschitz.log10_lip_local`. -/
theorem pipeline_log10_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (lo hi Eround : MachLib.Real) (hlo : 0 < lo) (e : EML) (he : IsArith e)
    (hflx_lo : lo ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ hi)
    (hxe_lo : lo ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ hi)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - log10 (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + (1 / (lo * log (natCast 10))) * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (log10 (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t log10 (1 / (lo * log (natCast 10))) Eround lo hi
    (le_of_lt (one_div_pos_of_pos (mul_pos hlo log_ten_pos)))
    (log10_lip_local lo hi hlo) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`arcsin` over an arithmetic subtree** (`L = 1/√(1−R²)`, `R < 1`) — SYMMETRIC domain `[-R,R]`,
matching `sinh`/`cosh`'s shape rather than `log`'s. The `0 ≤ L` obligation is derived from the same
in-domain witness (`hxe_lo`/`hxe_hi`) `absenc_arcsin_local` uses, via the now-public
`sq_lt_one_of_abs_le_lt_one`. Instance of the local pipeline via `InverseTrigBounded.arcsin_lip_local`.
-/
theorem pipeline_arcsin_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (R Eround : MachLib.Real) (hR : R < 1) (e : EML) (he : IsArith e)
    (hflx_lo : -R ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ R)
    (hxe_lo : -R ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ R)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - arcsin (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + (1 / sqrt (1 - R * R)) * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (arcsin (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t arcsin (1 / sqrt (1 - R * R)) Eround (-R) R
    (le_of_lt (one_div_pos_of_pos (sqrt_pos (sub_pos_of_lt
      (sq_lt_one_of_abs_le_lt_one hR (abs_le_iff.mpr ⟨hxe_lo, hxe_hi⟩))))))
    (arcsin_lip_local R hR) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`arccos` over an arithmetic subtree** (`L = 1/√(1−R²)`, `R < 1`) — same symmetric-domain shape
as `arcsin`. Instance of the local pipeline via `InverseTrigBounded.arccos_lip_local`. -/
theorem pipeline_arccos_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (R Eround : MachLib.Real) (hR : R < 1) (e : EML) (he : IsArith e)
    (hflx_lo : -R ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ R)
    (hxe_lo : -R ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ R)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - arccos (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + (1 / sqrt (1 - R * R)) * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (arccos (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t arccos (1 / sqrt (1 - R * R)) Eround (-R) R
    (le_of_lt (one_div_pos_of_pos (sqrt_pos (sub_pos_of_lt
      (sq_lt_one_of_abs_le_lt_one hR (abs_le_iff.mpr ⟨hxe_lo, hxe_hi⟩))))))
    (arccos_lip_local R hR) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`sinh` over an arithmetic subtree** (`L = cosh R`) — SYMMETRIC domain `[-R,R]`, unconditional
(`cosh R > 0` for every `R`, no domain-sanity hypothesis needed beyond the plain range bounds).
Instance of the local pipeline via `HyperbolicLipschitz.sinh_lip_local`. -/
theorem pipeline_sinh_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (R Eround : MachLib.Real) (e : EML) (he : IsArith e)
    (hflx_lo : -R ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ R)
    (hxe_lo : -R ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ R)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - sinh (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + cosh R * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (sinh (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t sinh (cosh R) Eround (-R) R
    (le_of_lt (cosh_pos R)) (sinh_lip_local R) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

/-- **`cosh` over an arithmetic subtree** (`L = sinh R`, `R ≥ 0`) — SYMMETRIC domain `[-R,R]`. Unlike
`sinh`, needs the explicit `0 ≤ R` domain-sanity hypothesis (`sinh R ≥ 0` only for `R ≥ 0`) — the
`cosh`/`log` analog of `sinh`/`exp`'s cheaper unconditional case. Instance of the local pipeline via
`HyperbolicLipschitz.cosh_lip_local`. -/
theorem pipeline_cosh_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (R Eround : MachLib.Real) (hR0 : 0 ≤ R) (e : EML) (he : IsArith e)
    (hflx_lo : -R ≤ toR (evalEML i1 i2 env e).toF) (hflx_hi : toR (evalEML i1 i2 env e).toF ≤ R)
    (hxe_lo : -R ≤ exactR toR env e) (hxe_hi : exactR toR env e ≤ R)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - cosh (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + sinh R * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (cosh (exactR toR env e)) :=
  pipeline_tr1_of_arith_local br i1 i2 r1 r2 hrt1 hrt2 env t cosh (sinh R) Eround (-R) R
    (sinh_nonneg hR0) (cosh_lip_local R) e he hflx_lo hflx_hi hxe_lo hxe_hi hround

end Certcom
