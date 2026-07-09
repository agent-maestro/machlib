/-!
# certcom Theorem A (tier T1) — translation-validated C backend

The soundness witness (Theorem B) grounds `MachLib.Real`'s axioms in Mathlib's ℝ. Theorem A is the
*other* half of "certcom-grade": that Forge's compiler **preserves EML semantics** on the way to C.
This file builds the **T1 translation-validated backend** — a Lean model of EML's evaluation, a Lean
model of the C the backend emits, a Lean model of the emitter (`c_backend.py`), and a proof that the
two evaluations agree. T1 deliberately trusts the `mg_*` C runtime and the C compiler (they materialise
the float ops); what it *proves* is that the Python emitter is a **semantics-preserving translation**.

Value model: Lean's `Float` (IEEE-754 double) — the honest model of what the compiled C computes
(float64). NOT the exact-real semantics (`MachLib.Real`); the C backend rounds, so translation
validation lives at the float level.

**Fragment covered:** scalar arithmetic (`LITERAL`/`VAR`/`BINOP`/`UNARYOP -`), comparison/boolean
`BINOP`s, `let`, the transcendental/operator builtins (`EXP`/… → `mg_*`, `EML`/`POW` → `mg_eml`/`mg_pow`),
`COND` (→ ternary), the fixed-shape vector reductions on literal vectors (`INDEX`/`VSUM`/`DOT`, which
`c_backend` UNROLLS into scalar accesses/sums), and functions (`_emit_function`). The `mg_*`
correspondence is T1's explicit trust (`hrt1`/`hrt2`). `emitC_correct` / `emitFunc_correct` are the
translation-validation certificates. No axioms beyond `propext`.
-/

namespace Certcom

/-- Binary operators emitted as infix C: arithmetic (`+ - * /`), comparison (`< <= > >= == !=`, →
`1.0`/`0.0`), boolean (`&& ||`). -/
inductive BinOp where
  | add | sub | mul | div
  | lt | le | gt | ge | eq | ne
  | band | bor
deriving DecidableEq, Repr

/-- Apply a `BinOp` at the float level — shared meaning of the EML op and the emitted C op. -/
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

/-- Unary builtins; each routes to a `mg_*` runtime call. -/
inductive Trans1 where
  | exp | ln | sin | cos | tan | sqrt | abs | asin | acos | atan | sinh | cosh | tanh
deriving DecidableEq, Repr

/-- `mg_*` C runtime name of each unary builtin (verbatim from `c_backend._BUILTIN_TO_C`). -/
def Trans1.cName : Trans1 → String
  | .exp => "mg_exp" | .ln => "mg_ln" | .sin => "mg_sin" | .cos => "mg_cos" | .tan => "mg_tan"
  | .sqrt => "mg_sqrt" | .abs => "mg_abs" | .asin => "mg_asin" | .acos => "mg_acos"
  | .atan => "mg_atan" | .sinh => "mg_sinh" | .cosh => "mg_cosh" | .tanh => "mg_tanh"

/-- Binary builtins: the EML operator `eml(x,y)` and `pow(x,y)`. -/
inductive Trans2 where
  | eml | pow
deriving DecidableEq, Repr

/-- `mg_*` C runtime name of each binary builtin. -/
def Trans2.cName : Trans2 → String
  | .eml => "mg_eml" | .pow => "mg_pow"

/-- EML AST. `idx`/`vsum`/`dot` are the fixed-shape vector reductions over a literal vector
(`List EML` of scalar elements) — the shape `c_backend` unrolls. -/
inductive EML where
  | lit  : Float → EML
  | var  : String → EML
  | bin  : BinOp → EML → EML → EML
  | neg  : EML → EML
  | elet : String → EML → EML → EML
  | tr1  : Trans1 → EML → EML
  | tr2  : Trans2 → EML → EML → EML
  | cond : EML → EML → EML → EML
  | idx  : List EML → Nat → EML            -- `v[n]` on a literal vector
  | vsum : List EML → EML                  -- `sum(v)`
  | dot  : List EML → List EML → EML       -- `dot(a, b)`

/-- The C AST the backend emits (a SEPARATE type so `emitC_correct` has content). `cidx`/`csum`/`cdot`
are the UNROLLED array access / scalar sum / sum-of-products `c_backend` produces. -/
inductive CExpr where
  | lit   : Float → CExpr
  | var   : String → CExpr
  | bin   : BinOp → CExpr → CExpr → CExpr
  | neg   : CExpr → CExpr
  | clet  : String → CExpr → CExpr → CExpr
  | ucall : String → CExpr → CExpr
  | bcall : String → CExpr → CExpr → CExpr
  | tern  : CExpr → CExpr → CExpr → CExpr
  | cidx  : List CExpr → Nat → CExpr
  | csum  : List CExpr → CExpr
  | cdot  : List CExpr → List CExpr → CExpr

/-- Environment: chain and local variable values. -/
abbrev Env := String → Float

/-- Extend an environment (the `let`-binding update). -/
def Env.update (env : Env) (x : String) (v : Float) : Env :=
  fun s => if s = x then v else env s

/-- C's truthiness: nonzero is true. Both evaluators use the SAME test. -/
def isTrue (c : Float) : Bool := c != 0.0

section
variable (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)

/- **EML evaluation** (reference float64 semantics). `evalEMLs` maps it over a literal vector's
elements (mutual, to handle the `List EML` child). -/
mutual
  def evalEML (env : Env) : EML → Float
    | .lit c      => c
    | .var x      => env x
    | .bin op a b => op.apply (evalEML env a) (evalEML env b)
    | .neg a      => -(evalEML env a)
    | .elet x e body => evalEML (env.update x (evalEML env e)) body
    | .tr1 t e    => i1 t (evalEML env e)
    | .tr2 t a b  => i2 t (evalEML env a) (evalEML env b)
    | .cond c t e => bif isTrue (evalEML env c) then evalEML env t else evalEML env e
    | .idx es n   => (evalEMLs env es).getD n 0.0
    | .vsum es    => (evalEMLs env es).foldr (· + ·) 0.0
    | .dot as bs  => (List.zipWith (· * ·) (evalEMLs env as) (evalEMLs env bs)).foldr (· + ·) 0.0
  def evalEMLs (env : Env) : List EML → List Float
    | []      => []
    | e :: es => evalEML env e :: evalEMLs env es
end

end

section
variable (r1 : String → Float → Float) (r2 : String → Float → Float → Float)

/- **C evaluation** of the emitted code. `r1`/`r2` model the `mg_*` runtime. -/
mutual
  def evalC (env : Env) : CExpr → Float
    | .lit c      => c
    | .var x      => env x
    | .bin op a b => op.apply (evalC env a) (evalC env b)
    | .neg a      => -(evalC env a)
    | .clet x e body => evalC (env.update x (evalC env e)) body
    | .ucall f a  => r1 f (evalC env a)
    | .bcall f a b => r2 f (evalC env a) (evalC env b)
    | .tern c t e => bif isTrue (evalC env c) then evalC env t else evalC env e
    | .cidx cs n  => (evalCs env cs).getD n 0.0
    | .csum cs    => (evalCs env cs).foldr (· + ·) 0.0
    | .cdot as bs => (List.zipWith (· * ·) (evalCs env as) (evalCs env bs)).foldr (· + ·) 0.0
  def evalCs (env : Env) : List CExpr → List Float
    | []      => []
    | c :: cs => evalC env c :: evalCs env cs
end

end

/- **The emitter** — the Lean model of `c_backend.py`. Vector reductions unroll to `cidx`/`csum`/`cdot`. -/
mutual
  def emitC : EML → CExpr
    | .lit c      => .lit c
    | .var x      => .var x
    | .bin op a b => .bin op (emitC a) (emitC b)
    | .neg a      => .neg (emitC a)
    | .elet x e body => .clet x (emitC e) (emitC body)
    | .tr1 t e    => .ucall t.cName (emitC e)
    | .tr2 t a b  => .bcall t.cName (emitC a) (emitC b)
    | .cond c t e => .tern (emitC c) (emitC t) (emitC e)
    | .idx es n   => .cidx (emitCs es) n
    | .vsum es    => .csum (emitCs es)
    | .dot as bs  => .cdot (emitCs as) (emitCs bs)
  def emitCs : List EML → List CExpr
    | []      => []
    | e :: es => emitC e :: emitCs es
end

section
variable (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
variable (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
variable (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
variable (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
include hrt1 hrt2

/- **Translation validation (T1).** Under the trusted-runtime hypotheses, the emitted C evaluates to
the same float as the EML source, for every expression and environment. `emitC_correct_s` is the
companion over a literal vector's elements. -/
mutual
  theorem emitC_correct : ∀ (e : EML) (env : Env), evalC r1 r2 env (emitC e) = evalEML i1 i2 env e
    | .lit c, env => rfl
    | .var x, env => rfl
    | .bin op a b, env => by
        simp only [emitC, evalC, evalEML, emitC_correct a env, emitC_correct b env]
    | .neg a, env => by simp only [emitC, evalC, evalEML, emitC_correct a env]
    | .elet x e body, env => by
        show evalC r1 r2 (env.update x (evalC r1 r2 env (emitC e))) (emitC body)
           = evalEML i1 i2 (env.update x (evalEML i1 i2 env e)) body
        rw [emitC_correct e env, emitC_correct body (env.update x (evalEML i1 i2 env e))]
    | .tr1 t e, env => by
        show r1 t.cName (evalC r1 r2 env (emitC e)) = i1 t (evalEML i1 i2 env e)
        rw [emitC_correct e env, hrt1]
    | .tr2 t a b, env => by
        show r2 t.cName (evalC r1 r2 env (emitC a)) (evalC r1 r2 env (emitC b))
           = i2 t (evalEML i1 i2 env a) (evalEML i1 i2 env b)
        rw [emitC_correct a env, emitC_correct b env, hrt2]
    | .cond c t e, env => by
        show (bif isTrue (evalC r1 r2 env (emitC c)) then evalC r1 r2 env (emitC t)
                else evalC r1 r2 env (emitC e))
           = bif isTrue (evalEML i1 i2 env c) then evalEML i1 i2 env t else evalEML i1 i2 env e
        rw [emitC_correct c env, emitC_correct t env, emitC_correct e env]
    | .idx es n, env => by
        show (evalCs r1 r2 env (emitCs es)).getD n 0.0 = (evalEMLs i1 i2 env es).getD n 0.0
        rw [emitC_correct_s es env]
    | .vsum es, env => by
        show (evalCs r1 r2 env (emitCs es)).foldr (· + ·) 0.0
           = (evalEMLs i1 i2 env es).foldr (· + ·) 0.0
        rw [emitC_correct_s es env]
    | .dot as bs, env => by
        show (List.zipWith (· * ·) (evalCs r1 r2 env (emitCs as)) (evalCs r1 r2 env (emitCs bs))).foldr (· + ·) 0.0
           = (List.zipWith (· * ·) (evalEMLs i1 i2 env as) (evalEMLs i1 i2 env bs)).foldr (· + ·) 0.0
        rw [emitC_correct_s as env, emitC_correct_s bs env]
  theorem emitC_correct_s :
      ∀ (es : List EML) (env : Env), evalCs r1 r2 env (emitCs es) = evalEMLs i1 i2 env es
    | [], env => rfl
    | e :: es, env => by
        show evalC r1 r2 env (emitC e) :: evalCs r1 r2 env (emitCs es)
           = evalEML i1 i2 env e :: evalEMLs i1 i2 env es
        rw [emitC_correct e env, emitC_correct_s es env]
end

end

/-! ## Function level — the compilation unit (`_emit_function`) -/

/-- An EML function: parameter names + a body expression. -/
structure EMLFunc where
  params : List String
  body   : EML

/-- The emitted C function: same parameters + emitted body. -/
structure CFunc where
  params : List String
  body   : CExpr

/-- Emit a function — the Lean model of `c_backend._emit_function` at this fragment. -/
def emitFunc (f : EMLFunc) : CFunc := ⟨f.params, emitC f.body⟩

/-- Bind an argument vector to the parameter names positionally, over a base environment. -/
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
the EML function, for every argument vector — the compilation-unit certificate; a direct corollary of
`emitC_correct`. -/
theorem emitFunc_correct
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (f : EMLFunc) (args : List Float) (base : Env) :
    evalFuncC r1 r2 (emitFunc f) args base = evalFuncEML i1 i2 f args base :=
  emitC_correct i1 i2 r1 r2 hrt1 hrt2 f.body (bindArgs f.params args base)

end Certcom
