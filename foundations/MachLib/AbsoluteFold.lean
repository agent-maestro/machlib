import MachLib.AbsoluteBridge

/-!
# The absolute forward-error fold over an ARBITRARY arithmetic EML tree

`AbsoluteBridge.pipeline_det` bounded the emitted C for one cancelling kernel (`x·y − z·w`). This
generalises it to **every** literal / variable / `+` / `−` / `×` tree: a recursive error function
`absErr` folds the `absenc_*` node bounds over the AST, and one structural induction proves the emitted
C's value stays within `absErr e` of the exact real `exactR e` — cancellations included, no sign
hypothesis. `pipeline_det` is now literally the `detEML` instance (`isArith_detEML`).

Scope is the arithmetic fragment `IsArith` (lit/var/`+`/`−`/`×`); transcendental nodes (`tr1`/`tr2`)
would fold in their primitive `RoundsW` specs (the T3 composite bricks), and `neg` needs an `FPBridge`
sign-exactness field — both are follow-on nodes, not a change to the fold. `sorryAx`-free.

`exactR`/`absErr` are `noncomputable` (they land in the axiomatised `MachLib.Real`) and use a `List EML`
mutual companion — exactly `evalEML`'s shape — so the recursion is STRUCTURAL and the node equations
reduce definitionally (a flat `.bin .add`/`.bin .sub`/… match compiles to well-founded recursion and
does not reduce).
-/

namespace Certcom

open MachLib.Real

/-- The arithmetic fragment of `EML`: literals, variables, and `+`/`−`/`×`. -/
inductive IsArith : EML → Prop
  | lit (c : Float) : IsArith (.lit c)
  | var (s : String) : IsArith (.var s)
  | add (a b : EML) : IsArith a → IsArith b → IsArith (.bin .add a b)
  | sub (a b : EML) : IsArith a → IsArith b → IsArith (.bin .sub a b)
  | mul (a b : EML) : IsArith a → IsArith b → IsArith (.bin .mul a b)
  | neg (a : EML) : IsArith a → IsArith (.neg a)

/- Exact real interpretation of an arithmetic tree: leaves through `toR`, `MachLib.Real` ops at nodes. -/
mutual
  noncomputable def exactR (toR : Float → MachLib.Real) (env : Env) : EML → MachLib.Real
    | .lit c => toR c
    | .var s => toR (env s).toF
    | .bin op a b =>
        match op with
        | .add => exactR toR env a + exactR toR env b
        | .sub => exactR toR env a - exactR toR env b
        | .mul => exactR toR env a * exactR toR env b
        | _ => 0
    | .neg a => -(exactR toR env a)
    | .elet _ _ _ => 0
    | .tr1 _ _ => 0
    | .tr2 _ _ _ => 0
    | .cond _ _ _ => 0
    | .vlit es => exactRs toR env es
    | .idx _ _ => 0
    | .vsum _ => 0
    | .dot _ _ => 0
  noncomputable def exactRs (toR : Float → MachLib.Real) (env : Env) : List EML → MachLib.Real
    | [] => 0
    | e :: es => exactR toR env e + exactRs toR env es
end

/- The accumulated ABSOLUTE forward-error bound, folded over an arithmetic tree: leaves carry `0`, each
internal node adds exactly its `absenc_*` contribution (in terms of the subtrees' exact values + errors). -/
mutual
  noncomputable def absErr (toR : Float → MachLib.Real) (env : Env) : EML → MachLib.Real
    | .lit _ => 0
    | .var _ => 0
    | .bin op a b =>
        match op with
        | .add =>
            u * ((abs (exactR toR env a) + absErr toR env a) + (abs (exactR toR env b) + absErr toR env b))
              + (absErr toR env a + absErr toR env b)
        | .sub =>
            u * ((abs (exactR toR env a) + absErr toR env a) + (abs (exactR toR env b) + absErr toR env b))
              + (absErr toR env a + absErr toR env b)
        | .mul =>
            u * ((abs (exactR toR env a) + absErr toR env a) * (abs (exactR toR env b) + absErr toR env b))
              + ((abs (exactR toR env a) + absErr toR env a) * absErr toR env b
                 + absErr toR env a * abs (exactR toR env b))
        | _ => 0
    | .neg a => absErr toR env a
    | .elet _ _ _ => 0
    | .tr1 _ _ => 0
    | .tr2 _ _ _ => 0
    | .cond _ _ _ => 0
    | .vlit es => absErrs toR env es
    | .idx _ _ => 0
    | .vsum _ => 0
    | .dot _ _ => 0
  noncomputable def absErrs (toR : Float → MachLib.Real) (env : Env) : List EML → MachLib.Real
    | [] => 0
    | e :: es => absErr toR env e + absErrs toR env es
end

/-- **General absolute forward error over an arbitrary arithmetic EML tree.** For any `IsArith e`, T2's
`evalEML` for `e`, through `toR`, is within `absErr … e` of the exact real `exactR … e`. Structural
induction over the fragment, each node discharged by its `absenc_*` lemma + the bridge's per-op
rounding; leaves are exact (`absenc_exact`), and cancellation is handled by `absenc_sub` carrying the
same bound as `absenc_add`. -/
theorem evalEML_absErr {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env) :
    ∀ e : EML, IsArith e →
      AbsEnc (absErr toR env e) (toR (evalEML i1 i2 env e).toF) (exactR toR env e) := by
  intro e he
  induction he with
  | lit c => exact absenc_exact (toR c)
  | var s => exact absenc_exact (toR (env s).toF)
  | add a b _ _ iha ihb =>
      exact absenc_add iha ihb (br.add (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)
  | sub a b _ _ iha ihb =>
      exact absenc_sub iha ihb (br.sub (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)
  | mul a b _ _ iha ihb =>
      exact absenc_mul iha ihb (br.mul (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)
  | neg a _ iha =>
      show AbsEnc (absErr toR env a) (toR (-(evalEML i1 i2 env a).toF)) (-(exactR toR env a))
      rw [br.neg (evalEML i1 i2 env a).toF]
      exact absenc_neg iha

/-- **General cancelling pipeline — arbitrary arithmetic tree, through the emitted C.** The value the
emitted C computes for any `IsArith e`, through `toR`, is within `absErr … e` of the exact real. The
whole-fragment generalisation of `pipeline_det`. -/
theorem pipeline_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (e : EML) (he : IsArith e) :
    AbsEnc (absErr toR env e) (toR (evalC r1 r2 env (emitC e)).toF) (exactR toR env e) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
  exact evalEML_absErr br i1 i2 env e he

/-- The determinant kernel `x·y − z·w` is in the arithmetic fragment: `pipeline_det` is the `detEML`
instance of the general `pipeline_arith`. -/
theorem isArith_detEML : IsArith detEML :=
  .sub _ _ (.mul _ _ (.var "x") (.var "y")) (.mul _ _ (.var "z") (.var "w"))

/-- `f(e)` — a unary primitive `t` applied to an arithmetic subtree `e`. -/
def tr1OfEML (t : Trans1) (e : EML) : EML := .tr1 t e

/-- **A transcendental over an arithmetic subtree, through the emitted C.** A unary primitive `t` — with
real semantics `f`, `L`-Lipschitz — applied to ANY arithmetic `e` (`x·y − z·w`, a cancelling difference,
etc.): the value the emitted C computes, through `toR`, is within `Eround + L·(absErr … e)` of the exact
`f (exactR … e)`. The arithmetic fold's absolute error on `e` is amplified by the primitive's Lipschitz
sensitivity `L`, plus the primitive's own rounding `Eround`. This composes `evalEML_absErr` (the whole
arithmetic fold) with `absenc_lip` (the transcendental node) across `emitC_correct` — so the absolute,
cancellation-tolerant certificate now reaches one transcendental layer over any arithmetic tree.
Instantiate `f`/`L`/`Eround` per primitive: `TrigLipschitz`/`HyperbolicLipschitz` give `L` (`= 1` for
sin/cos/tanh/arctan/abs — the GLOBALLY-Lipschitz, bounded-derivative primitives this covers), a `RoundsW`
spec gives `Eround`. Honest scope: `exp`/`log`/`sinh`/`cosh`/`tan` have unbounded derivative and are NOT
globally Lipschitz, so they need a LOCAL-Lipschitz variant (an `L` valid on a bounded domain, with a
range hypothesis on the input); and the binary `tr2` primitives (`eml = exp − log`, `pow`) are likewise
non-Lipschitz and instead DECOMPOSE into unary + arithmetic nodes (`eml` is `absenc_sub` of two `tr1`s —
exactly `absenc_sub_rounded`). Those two are the remaining follow-ons. -/
theorem pipeline_tr1_of_arith {toR : Float → MachLib.Real} (br : FPBridge toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (f : MachLib.Real → MachLib.Real) (L Eround : MachLib.Real)
    (hLnn : 0 ≤ L) (hL : ∀ p q : MachLib.Real, abs (f p - f q) ≤ L * abs (p - q))
    (e : EML) (he : IsArith e)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - f (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + L * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (f (exactR toR env e)) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 (tr1OfEML t e) env]
  show AbsEnc (Eround + L * absErr toR env e)
      (toR (i1 t (evalEML i1 i2 env e).toF)) (f (exactR toR env e))
  exact absenc_lip hLnn hL (evalEML_absErr br i1 i2 env e he) hround

/-! ## The same fold over the bridge binary64 satisfies

`FPBridge` asks more of IEEE binary64 than it gives (`FPBridgeFinite`, `FloatRealBridge.lean`). The theorems
below are the ones above over `FPBridgeFinite`, with its side conditions supplied per node by `FloatSafe`. -/

/-- The float side conditions `FPBridgeFinite` needs along one evaluation, node by node: every `+`, `−`, `×`
and negation computes a finite float, and no product's exact value is a nonzero real below `DBL_MIN` in
magnitude. A `tr1` node adds nothing of its own (its rounding fact is the primitive's axiom) and passes the
conditions to its argument; leaves need nothing. Nothing inside Lean can establish these, since `Float` is
opaque: they are what a caller checks at run time or guarantees by bounding its inputs. -/
inductive FloatSafe (toR : Float → MachLib.Real) (i1 : Trans1 → Float → Float)
    (i2 : Trans2 → Float → Float → Float) (env : Env) : EML → Prop
  | lit (c : Float) : FloatSafe toR i1 i2 env (.lit c)
  | var (s : String) : FloatSafe toR i1 i2 env (.var s)
  | add (a b : EML) : FloatSafe toR i1 i2 env a → FloatSafe toR i1 i2 env b →
      ((evalEML i1 i2 env a).toF + (evalEML i1 i2 env b).toF).isFinite = true →
      FloatSafe toR i1 i2 env (.bin .add a b)
  | sub (a b : EML) : FloatSafe toR i1 i2 env a → FloatSafe toR i1 i2 env b →
      ((evalEML i1 i2 env a).toF - (evalEML i1 i2 env b).toF).isFinite = true →
      FloatSafe toR i1 i2 env (.bin .sub a b)
  | mul (a b : EML) : FloatSafe toR i1 i2 env a → FloatSafe toR i1 i2 env b →
      ((evalEML i1 i2 env a).toF * (evalEML i1 i2 env b).toF).isFinite = true →
      (toR (evalEML i1 i2 env a).toF * toR (evalEML i1 i2 env b).toF = 0 ∨
        dblMin ≤ abs (toR (evalEML i1 i2 env a).toF * toR (evalEML i1 i2 env b).toF)) →
      FloatSafe toR i1 i2 env (.bin .mul a b)
  | neg (a : EML) : FloatSafe toR i1 i2 env a → (evalEML i1 i2 env a).toF.isFinite = true →
      FloatSafe toR i1 i2 env (.neg a)
  | tr1 (t : Trans1) (a : EML) : FloatSafe toR i1 i2 env a → FloatSafe toR i1 i2 env (.tr1 t a)

/-- At a `+` root, `FloatSafe` says the computed float is finite: that is its own condition there. -/
theorem FloatSafe.add_isFinite {toR : Float → MachLib.Real} {i1 : Trans1 → Float → Float}
    {i2 : Trans2 → Float → Float → Float} {env : Env} {a b : EML}
    (h : FloatSafe toR i1 i2 env (.bin .add a b)) :
    (evalEML i1 i2 env (.bin .add a b)).toF.isFinite = true := by
  cases h with
  | add _ _ _ _ hf => exact hf

/-- `evalEML_absErr` over `FPBridgeFinite`: the absolute forward error of an arithmetic tree, given the tree's
float side conditions. -/
theorem evalEML_absErr_finite {toR : Float → MachLib.Real} (br : FPBridgeFinite toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) (env : Env) :
    ∀ e : EML, IsArith e → FloatSafe toR i1 i2 env e →
      AbsEnc (absErr toR env e) (toR (evalEML i1 i2 env e).toF) (exactR toR env e) := by
  intro e he
  induction he with
  | lit c => intro _; exact absenc_exact (toR c)
  | var s => intro _; exact absenc_exact (toR (env s).toF)
  | add a b _ _ iha ihb =>
      intro hs
      cases hs with
      | add _ _ hsa hsb hf => exact absenc_add (iha hsa) (ihb hsb) (br.add _ _ hf)
  | sub a b _ _ iha ihb =>
      intro hs
      cases hs with
      | sub _ _ hsa hsb hf => exact absenc_sub (iha hsa) (ihb hsb) (br.sub _ _ hf)
  | mul a b _ _ iha ihb =>
      intro hs
      cases hs with
      | mul _ _ hsa hsb hf hz => exact absenc_mul (iha hsa) (ihb hsb) (br.mul _ _ hf hz)
  | neg a _ iha =>
      intro hs
      cases hs with
      | neg _ hsa hf =>
          show AbsEnc (absErr toR env a) (toR (-(evalEML i1 i2 env a).toF)) (-(exactR toR env a))
          rw [br.neg _ hf]
          exact absenc_neg (iha hsa)

/-- `pipeline_arith` over `FPBridgeFinite`, with `FloatSafe`'s side conditions. -/
theorem pipeline_arith_finite {toR : Float → MachLib.Real} (br : FPBridgeFinite toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (e : EML) (he : IsArith e) (hs : FloatSafe toR i1 i2 env e) :
    AbsEnc (absErr toR env e) (toR (evalC r1 r2 env (emitC e)).toF) (exactR toR env e) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
  exact evalEML_absErr_finite br i1 i2 env e he hs

/-- `pipeline_det` (`AbsoluteBridge.lean`) over `FPBridgeFinite`: the two products and the difference of
`x·y − z·w` must satisfy `FloatSafe`'s conditions. -/
theorem pipeline_det_finite {toR : Float → MachLib.Real} (br : FPBridgeFinite toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v) (env : Env)
    (hs : FloatSafe toR i1 i2 env detEML) :
    AbsEnc (u * (1 + 1 + u) * (abs (toR (env "x").toF * toR (env "y").toF)
                              + abs (toR (env "z").toF * toR (env "w").toF)))
      (toR (evalC r1 r2 env (emitC detEML)).toF)
      (toR (env "x").toF * toR (env "y").toF - toR (env "z").toF * toR (env "w").toF) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 detEML env]
  have h : (evalEML i1 i2 env detEML).toF
      = ((env "x").toF * (env "y").toF) - ((env "z").toF * (env "w").toF) := rfl
  rw [h]
  have hs' : FloatSafe toR i1 i2 env
      (.bin .sub (.bin .mul (.var "x") (.var "y")) (.bin .mul (.var "z") (.var "w"))) := hs
  cases hs' with
  | sub _ _ hxy hzw hd =>
      cases hxy with
      | mul _ _ _ _ hf1 hz1 =>
          cases hzw with
          | mul _ _ _ _ hf2 hz2 =>
              exact absenc_sub_rounded (br.mul _ _ hf1 hz1) (br.mul _ _ hf2 hz2) (br.sub _ _ hd)

/-- `pipeline_tr1_of_arith` over `FPBridgeFinite`, with `FloatSafe`'s side conditions. -/
theorem pipeline_tr1_of_arith_finite {toR : Float → MachLib.Real} (br : FPBridgeFinite toR)
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (env : Env) (t : Trans1) (f : MachLib.Real → MachLib.Real) (L Eround : MachLib.Real)
    (hLnn : 0 ≤ L) (hL : ∀ p q : MachLib.Real, abs (f p - f q) ≤ L * abs (p - q))
    (e : EML) (he : IsArith e) (hs : FloatSafe toR i1 i2 env e)
    (hround : abs (toR (i1 t (evalEML i1 i2 env e).toF) - f (toR (evalEML i1 i2 env e).toF)) ≤ Eround) :
    AbsEnc (Eround + L * absErr toR env e)
      (toR (evalC r1 r2 env (emitC (tr1OfEML t e))).toF) (f (exactR toR env e)) := by
  rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 (tr1OfEML t e) env]
  show AbsEnc (Eround + L * absErr toR env e)
      (toR (i1 t (evalEML i1 i2 env e).toF)) (f (exactR toR env e))
  exact absenc_lip hLnn hL (evalEML_absErr_finite br i1 i2 env e he hs) hround

end Certcom
