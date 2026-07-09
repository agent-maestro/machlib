/-!
# certcom Theorem A (tier T1) — translation-validated C backend, scalar+let fragment

The soundness witness (Theorem B) grounds `MachLib.Real`'s axioms in Mathlib's ℝ. Theorem A is the
*other* half of "certcom-grade": that Forge's compiler **preserves EML semantics** on the way to C.
This file starts the **T1 translation-validated backend** — a Lean model of EML's evaluation, a Lean
model of the C the backend emits, a Lean model of the emitter (`c_backend.py`), and a proof that the
two evaluations agree. T1 deliberately trusts the `mg_*` C runtime and the C compiler (they materialise
the float ops); what it *proves* is that the Python emitter is a **semantics-preserving translation**.

Value model: Lean's `Float` (IEEE-754 double) — the honest model of what the compiled C computes
(float64), matching Forge's compute backends. This is NOT the exact-real semantics (`MachLib.Real`);
the C backend rounds, so translation validation lives at the float level.

**This fragment: straight-line scalar arithmetic with `let`.** Mirrors `c_backend._emit_expr`
(`LITERAL`→literal, `VAR`→name, `BINOP a op b`→`(a op b)`, `UNARYOP -`→`(-x)`) and the `let`-binding of
`_emit_block` (`LET x = e` → a C local `double x = e;` in scope for the rest). `emitC_correct` is the
translation-validation certificate for it. Extensions (transcendentals → `mg_*` runtime calls, vectors
→ array/`vec` structs, `cond`/`while`) build on this frame. No axioms — pure `Float` computation.
-/

namespace Certcom

/-- The scalar binary operators `c_backend` emits as infix C (`+ - * /`). -/
inductive BinOp where
  | add | sub | mul | div
deriving DecidableEq, Repr

/-- Apply a `BinOp` at the float level — the shared meaning of both the EML op and the emitted C op
(the C compiler is trusted to materialise the IEEE-754 operation). -/
def BinOp.apply : BinOp → Float → Float → Float
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b

/-- EML AST — scalar straight-line fragment (`LITERAL`, `VAR`, `BINOP`, `UNARYOP -`, `LET`). -/
inductive EML where
  | lit  : Float → EML
  | var  : String → EML
  | bin  : BinOp → EML → EML → EML
  | neg  : EML → EML
  | elet : String → EML → EML → EML   -- `let x = e in body`
deriving Repr

/-- The C AST the backend emits (structurally parallel; a `clet` is a C block introducing a local
`double x = e;` scoped over `body`). Kept a SEPARATE type from `EML` so `emitC_correct` has content. -/
inductive CExpr where
  | lit  : Float → CExpr
  | var  : String → CExpr
  | bin  : BinOp → CExpr → CExpr → CExpr
  | neg  : CExpr → CExpr
  | clet : String → CExpr → CExpr → CExpr
deriving Repr

/-- Environment: chain and local variable values. -/
abbrev Env := String → Float

/-- Extend an environment (the `let`-binding update; C's local shadows the outer scope). -/
def Env.update (env : Env) (x : String) (v : Float) : Env :=
  fun s => if s = x then v else env s

/-- **EML evaluation.** The reference semantics of the fragment (float64 model). -/
def evalEML (env : Env) : EML → Float
  | .lit c      => c
  | .var x      => env x
  | .bin op a b => op.apply (evalEML env a) (evalEML env b)
  | .neg a      => -(evalEML env a)
  | .elet x e body => evalEML (env.update x (evalEML env e)) body

/-- **C evaluation.** The (trusted-runtime) semantics of the emitted C: same float ops, `clet` binds a
local before evaluating the body. -/
def evalC (env : Env) : CExpr → Float
  | .lit c      => c
  | .var x      => env x
  | .bin op a b => op.apply (evalC env a) (evalC env b)
  | .neg a      => -(evalC env a)
  | .clet x e body => evalC (env.update x (evalC env e)) body

/-- **The emitter** — the Lean model of `c_backend.py` on this fragment (structural; `let` → `clet`). -/
def emitC : EML → CExpr
  | .lit c      => .lit c
  | .var x      => .var x
  | .bin op a b => .bin op (emitC a) (emitC b)
  | .neg a      => .neg (emitC a)
  | .elet x e body => .clet x (emitC e) (emitC body)

/-- **Translation validation (T1) for the scalar+let fragment.** For every EML expression `e` and
environment `env`, the emitted C evaluates to the same float as `e`: `evalC env (emitC e) = evalEML env e`.
The emitter preserves EML semantics on this fragment. -/
theorem emitC_correct (e : EML) (env : Env) : evalC env (emitC e) = evalEML env e := by
  induction e generalizing env with
  | lit c => rfl
  | var x => rfl
  | bin op a b iha ihb => simp only [emitC, evalC, evalEML, iha, ihb]
  | neg a ih => simp only [emitC, evalC, evalEML, ih]
  | elet x e body ihe ihbody =>
    show evalC (env.update x (evalC env (emitC e))) (emitC body)
       = evalEML (env.update x (evalEML env e)) body
    rw [ihe, ihbody]

end Certcom
