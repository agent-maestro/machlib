/-!
# certcom Theorem A (tier T1) — translation-validated C backend

The soundness witness (Theorem B) grounds `MachLib.Real`'s axioms in Mathlib's ℝ. Theorem A is the
*other* half of "certcom-grade": that Forge's compiler **preserves EML semantics** on the way to C.
This file builds the **T1 translation-validated backend** — a Lean model of EML's evaluation, a Lean
model of the C the backend emits, a Lean model of the emitter (`c_backend.py`), and a proof that the
two evaluations agree. T1 deliberately trusts the `mg_*` C runtime and the C compiler (they materialise
the float ops); what it *proves* is that the Python emitter is a **semantics-preserving translation**.

Value model: Lean's `Float` (IEEE-754 double) — the honest model of what the compiled C computes
(float64), matching Forge's compute backends. This is NOT the exact-real semantics (`MachLib.Real`);
the C backend rounds, so translation validation lives at the float level.

**Fragment covered here:** straight-line scalar arithmetic (`LITERAL`, `VAR`, `BINOP`, `UNARYOP -`),
`let` (`_emit_block`), and the transcendental / operator builtins (`EXP`/`LN`/`SIN`/… → `mg_exp`/…,
`EML`/`POW` → `mg_eml`/`mg_pow`). The runtime-call correspondence is T1's explicit trust: the theorem
is parameterised by an interpretation of the transcendentals and a model of the `mg_*` runtime, with
the hypothesis that the runtime implements the interpretation (`hrt1`/`hrt2`) — exactly the boundary
T1 declares. `emitC_correct` is the translation-validation certificate. Extensions (vectors, `cond`,
`while`/`state`, per-function) build on this frame. No axioms beyond `propext`.
-/

namespace Certcom

/-- The binary operators `c_backend` emits as infix C: arithmetic (`+ - * /`), comparison
(`< <= > >= == !=`, yielding `1.0`/`0.0` as C does with int `0`/`1` in a float context), and boolean
(`&& ||`). -/
inductive BinOp where
  | add | sub | mul | div
  | lt | le | gt | ge | eq | ne
  | band | bor
deriving DecidableEq, Repr

/-- Apply a `BinOp` at the float level — the shared meaning of both the EML op and the emitted C op.
Comparisons return `1.0`/`0.0`; booleans treat nonzero as true (C's `!= 0`). -/
def BinOp.apply : BinOp → Float → Float → Float
  | .add, a, b => a + b
  | .sub, a, b => a - b
  | .mul, a, b => a * b
  | .div, a, b => a / b
  | .lt, a, b => if a < b then 1.0 else 0.0
  | .le, a, b => if a ≤ b then 1.0 else 0.0
  | .gt, a, b => if b < a then 1.0 else 0.0
  | .ge, a, b => if b ≤ a then 1.0 else 0.0
  | .eq, a, b => bif a == b then 1.0 else 0.0
  | .ne, a, b => bif a != b then 1.0 else 0.0
  | .band, a, b => bif (a != 0.0) && (b != 0.0) then 1.0 else 0.0
  | .bor, a, b => bif (a != 0.0) || (b != 0.0) then 1.0 else 0.0

/-- Unary builtins; `c_backend` routes each to a `mg_*` runtime call. -/
inductive Trans1 where
  | exp | ln | sin | cos | tan | sqrt | abs | asin | acos | atan | sinh | cosh | tanh
deriving DecidableEq, Repr

/-- The `mg_*` C runtime name for each unary builtin (verbatim from `c_backend._BUILTIN_TO_C`). -/
def Trans1.cName : Trans1 → String
  | .exp => "mg_exp" | .ln => "mg_ln" | .sin => "mg_sin" | .cos => "mg_cos" | .tan => "mg_tan"
  | .sqrt => "mg_sqrt" | .abs => "mg_abs" | .asin => "mg_asin" | .acos => "mg_acos"
  | .atan => "mg_atan" | .sinh => "mg_sinh" | .cosh => "mg_cosh" | .tanh => "mg_tanh"

/-- Binary builtins: the EML operator `eml(x,y)` and `pow(x,y)`. -/
inductive Trans2 where
  | eml | pow
deriving DecidableEq, Repr

/-- The `mg_*` C runtime name for each binary builtin. -/
def Trans2.cName : Trans2 → String
  | .eml => "mg_eml" | .pow => "mg_pow"

/-- EML AST — scalar straight-line + builtins fragment. -/
inductive EML where
  | lit  : Float → EML
  | var  : String → EML
  | bin  : BinOp → EML → EML → EML
  | neg  : EML → EML
  | elet : String → EML → EML → EML       -- `let x = e in body`
  | tr1  : Trans1 → EML → EML             -- `exp(e)`, `ln(e)`, …
  | tr2  : Trans2 → EML → EML → EML       -- `eml(a,b)`, `pow(a,b)`
  | cond : EML → EML → EML → EML          -- `if c then t else e` (`NodeKind.COND`)
deriving Repr

/-- The C AST the backend emits (a SEPARATE type from `EML` so `emitC_correct` has content).
`ucall`/`bcall` are the emitted `mg_*` runtime calls; `clet` is a C block with a local `double x = e;`. -/
inductive CExpr where
  | lit   : Float → CExpr
  | var   : String → CExpr
  | bin   : BinOp → CExpr → CExpr → CExpr
  | neg   : CExpr → CExpr
  | clet  : String → CExpr → CExpr → CExpr
  | ucall : String → CExpr → CExpr        -- `mg_f(x)`
  | bcall : String → CExpr → CExpr → CExpr -- `mg_f(x, y)`
  | tern  : CExpr → CExpr → CExpr → CExpr  -- `c ? t : e`
deriving Repr

/-- Environment: chain and local variable values. -/
abbrev Env := String → Float

/-- C's truthiness of a condition value: nonzero is true (the `mg_*`-free ternary uses `c != 0`).
Both evaluators use the SAME test, so translation preserves the branch taken. -/
def isTrue (c : Float) : Bool := c != 0.0

/-- Extend an environment (the `let`-binding update; C's local shadows the outer scope). -/
def Env.update (env : Env) (x : String) (v : Float) : Env :=
  fun s => if s = x then v else env s

/-- **EML evaluation** (reference semantics, float64 model). Parameterised by the interpretation of the
builtins (`i1`/`i2`) — their exact-float meaning, which the `mg_*` runtime is trusted to realise. -/
def evalEML (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (env : Env) : EML → Float
  | .lit c      => c
  | .var x      => env x
  | .bin op a b => op.apply (evalEML i1 i2 env a) (evalEML i1 i2 env b)
  | .neg a      => -(evalEML i1 i2 env a)
  | .elet x e body => evalEML i1 i2 (env.update x (evalEML i1 i2 env e)) body
  | .tr1 t e    => i1 t (evalEML i1 i2 env e)
  | .tr2 t a b  => i2 t (evalEML i1 i2 env a) (evalEML i1 i2 env b)
  | .cond c t e => bif isTrue (evalEML i1 i2 env c) then evalEML i1 i2 env t else evalEML i1 i2 env e

/-- **C evaluation** of the emitted code. `r1`/`r2` model the `mg_*` runtime (name → float function). -/
def evalC (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (env : Env) : CExpr → Float
  | .lit c      => c
  | .var x      => env x
  | .bin op a b => op.apply (evalC r1 r2 env a) (evalC r1 r2 env b)
  | .neg a      => -(evalC r1 r2 env a)
  | .clet x e body => evalC r1 r2 (env.update x (evalC r1 r2 env e)) body
  | .ucall f a  => r1 f (evalC r1 r2 env a)
  | .bcall f a b => r2 f (evalC r1 r2 env a) (evalC r1 r2 env b)
  | .tern c t e => bif isTrue (evalC r1 r2 env c) then evalC r1 r2 env t else evalC r1 r2 env e

/-- **The emitter** — the Lean model of `c_backend.py` on this fragment. `tr1 t → mg_*(·)`,
`tr2 t → mg_*(·,·)`, everything else structural. -/
def emitC : EML → CExpr
  | .lit c      => .lit c
  | .var x      => .var x
  | .bin op a b => .bin op (emitC a) (emitC b)
  | .neg a      => .neg (emitC a)
  | .elet x e body => .clet x (emitC e) (emitC body)
  | .tr1 t e    => .ucall t.cName (emitC e)
  | .tr2 t a b  => .bcall t.cName (emitC a) (emitC b)
  | .cond c t e => .tern (emitC c) (emitC t) (emitC e)

/-- **Translation validation (T1).** Given that the `mg_*` runtime implements the builtin
interpretations (`hrt1 : r1 (t.cName) = i1 t`, `hrt2 : r2 (t.cName) = i2 t` — T1's explicit trust
boundary), the emitted C evaluates to the same float as the EML source, for every expression and
environment. The emitter preserves EML semantics on the scalar + `let` + builtins fragment. -/
theorem emitC_correct
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (e : EML) (env : Env) :
    evalC r1 r2 env (emitC e) = evalEML i1 i2 env e := by
  induction e generalizing env with
  | lit c => rfl
  | var x => rfl
  | bin op a b iha ihb => simp only [emitC, evalC, evalEML, iha, ihb]
  | neg a ih => simp only [emitC, evalC, evalEML, ih]
  | elet x e body ihe ihbody =>
    show evalC r1 r2 (env.update x (evalC r1 r2 env (emitC e))) (emitC body)
       = evalEML i1 i2 (env.update x (evalEML i1 i2 env e)) body
    rw [ihe, ihbody]
  | tr1 t e ih =>
    show r1 t.cName (evalC r1 r2 env (emitC e)) = i1 t (evalEML i1 i2 env e)
    rw [ih, hrt1]
  | tr2 t a b iha ihb =>
    show r2 t.cName (evalC r1 r2 env (emitC a)) (evalC r1 r2 env (emitC b))
       = i2 t (evalEML i1 i2 env a) (evalEML i1 i2 env b)
    rw [iha, ihb, hrt2]
  | cond c t e ihc iht ihe =>
    show (bif isTrue (evalC r1 r2 env (emitC c)) then evalC r1 r2 env (emitC t)
            else evalC r1 r2 env (emitC e))
       = bif isTrue (evalEML i1 i2 env c) then evalEML i1 i2 env t else evalEML i1 i2 env e
    rw [ihc, iht, ihe]

/-! ## Function level — the compilation unit (`_emit_function`) -/

/-- An EML function: parameter names + a body expression (`EMLFunction` after block-flattening). -/
structure EMLFunc where
  params : List String
  body   : EML

/-- The emitted C function: the same parameters + the emitted body. -/
structure CFunc where
  params : List String
  body   : CExpr

/-- Emit a function — the Lean model of `c_backend._emit_function` at this fragment: same signature,
translated body. -/
def emitFunc (f : EMLFunc) : CFunc := ⟨f.params, emitC f.body⟩

/-- Bind an argument vector to the parameter names (positionally), over a base environment. -/
def bindArgs : List String → List Float → Env → Env
  | [],      _,       env => env
  | _ :: _,  [],      env => env
  | x :: xs, v :: vs, env => bindArgs xs vs (env.update x v)

/-- Evaluate an EML function on an argument vector. -/
def evalFuncEML (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (f : EMLFunc) (args : List Float) (base : Env) : Float :=
  evalEML i1 i2 (bindArgs f.params args base) f.body

/-- Evaluate an emitted C function on an argument vector. -/
def evalFuncC (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (g : CFunc) (args : List Float) (base : Env) : Float :=
  evalC r1 r2 (bindArgs g.params args base) g.body

/-- **Function-level translation validation (T1).** The emitted C function computes the same float as
the EML function, for every argument vector — under the same trusted-runtime hypotheses. The
compilation-unit certificate; a direct corollary of `emitC_correct` at the parameter-bound environment. -/
theorem emitFunc_correct
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (f : EMLFunc) (args : List Float) (base : Env) :
    evalFuncC r1 r2 (emitFunc f) args base = evalFuncEML i1 i2 f args base :=
  emitC_correct i1 i2 r1 r2 hrt1 hrt2 f.body (bindArgs f.params args base)

end Certcom
