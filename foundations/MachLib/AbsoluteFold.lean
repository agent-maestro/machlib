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

end Certcom
