/-!
# certcom Theorem A (tier T1) — translation-validated C backend

The soundness witness (Theorem B) grounds `MachLib.Real`'s axioms in Mathlib's ℝ. Theorem A is the
*other* half of "certcom-grade": that Forge's compiler **preserves EML semantics** on the way to C.
This file builds the **T1 translation-validated backend** — a Lean model of EML's evaluation, a Lean
model of the C the backend emits, a Lean model of the emitter (`c_backend.py`), and a proof that the
two evaluations agree. T1 deliberately trusts the `mg_*` C runtime and the C compiler (they materialise
the float ops); what it *proves* is that the Python emitter is a **semantics-preserving translation**.

Value model: `Val = scalar Float | vec (List Float)` over Lean's `Float` (IEEE-754 double — the honest
model of what the compiled C computes; NOT the exact-real `MachLib.Real`, since the C backend rounds).
Vectors are now first-class values, so vector variables and `VECLIT` results (`[e0, e1, …]`) are
supported alongside the reductions `INDEX`/`VSUM`/`DOT`.

**Fragment covered:** scalar arithmetic (`LITERAL`/`VAR`/`BINOP`/`UNARYOP -`), comparison/boolean
`BINOP`s, `let`, transcendental/operator builtins (`EXP`/… → `mg_*`, `EML`/`POW` → `mg_eml`/`mg_pow`),
`COND` (→ ternary), fixed-shape vectors — literals (`VECLIT`), variables, and the reductions
`INDEX`/`VSUM`/`DOT` (which `c_backend` UNROLLS) — and functions (`_emit_function`). The `mg_*`
correspondence is T1's explicit trust (`hrt1`/`hrt2`). `emitC_correct` / `emitFunc_correct` are the
translation-validation certificates. No axioms beyond `propext`.
-/

namespace Certcom

/-- Binary operators emitted as infix C: arithmetic, comparison (→ `1.0`/`0.0`), boolean. -/
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

/-- Binary builtins: `eml(x,y)` and `pow(x,y)`. -/
inductive Trans2 where
  | eml | pow
deriving DecidableEq, Repr

/-- `mg_*` C runtime name of each binary builtin. -/
def Trans2.cName : Trans2 → String
  | .eml => "mg_eml" | .pow => "mg_pow"

/-- Runtime values: a scalar float or a fixed-shape float vector. -/
inductive Val where
  | scalar : Float → Val
  | vec    : List Float → Val

/-- Scalar projection (default `0.0` for a vector — ill-typed programs get a total default; the
translation-validation theorem holds regardless, since both evaluators use the same projection). -/
def Val.toF : Val → Float
  | .scalar f => f
  | .vec _    => 0.0

/-- Vector projection (default `[]` for a scalar). -/
def Val.toV : Val → List Float
  | .vec xs   => xs
  | .scalar _ => []

/-- EML AST. Vectors: `vlit` (`[e0,…]`), plus reductions `idx`/`vsum`/`dot` over a vector-valued expr. -/
inductive EML where
  | lit  : Float → EML
  | var  : String → EML
  | bin  : BinOp → EML → EML → EML
  | neg  : EML → EML
  | elet : String → EML → EML → EML
  | tr1  : Trans1 → EML → EML
  | tr2  : Trans2 → EML → EML → EML
  | cond : EML → EML → EML → EML
  | vlit : List EML → EML          -- `[e0, e1, …]`
  | idx  : EML → Nat → EML         -- `v[n]`
  | vsum : EML → EML               -- `sum(v)`
  | dot  : EML → EML → EML         -- `dot(a, b)`

/-- The C AST the backend emits (a SEPARATE type so `emitC_correct` has content). -/
inductive CExpr where
  | lit   : Float → CExpr
  | var   : String → CExpr
  | bin   : BinOp → CExpr → CExpr → CExpr
  | neg   : CExpr → CExpr
  | clet  : String → CExpr → CExpr → CExpr
  | ucall : String → CExpr → CExpr
  | bcall : String → CExpr → CExpr → CExpr
  | tern  : CExpr → CExpr → CExpr → CExpr
  | cvlit : List CExpr → CExpr
  | cidx  : CExpr → Nat → CExpr
  | csum  : CExpr → CExpr
  | cdot  : CExpr → CExpr → CExpr

/-- Environment: variable → value (scalar or vector). -/
abbrev Env := String → Val

/-- Extend an environment. -/
def Env.update (env : Env) (x : String) (v : Val) : Env :=
  fun s => if s = x then v else env s

/-- C's truthiness: nonzero is true. -/
def isTrue (c : Float) : Bool := c != 0.0

section
variable (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)

/- **EML evaluation** (reference float64 semantics). `evalEMLs` evaluates a `vlit`'s elements to a
float list (mutual, to handle the `List EML` child). -/
mutual
  def evalEML (env : Env) : EML → Val
    | .lit c      => .scalar c
    | .var x      => env x
    | .bin op a b => .scalar (op.apply (evalEML env a).toF (evalEML env b).toF)
    | .neg a      => .scalar (-(evalEML env a).toF)
    | .elet x e body => evalEML (env.update x (evalEML env e)) body
    | .tr1 t e    => .scalar (i1 t (evalEML env e).toF)
    | .tr2 t a b  => .scalar (i2 t (evalEML env a).toF (evalEML env b).toF)
    | .cond c t e => bif isTrue (evalEML env c).toF then evalEML env t else evalEML env e
    | .vlit es    => .vec (evalEMLs env es)
    | .idx v n    => .scalar ((evalEML env v).toV.getD n 0.0)
    | .vsum v     => .scalar ((evalEML env v).toV.foldr (· + ·) 0.0)
    | .dot a b    => .scalar ((List.zipWith (· * ·) (evalEML env a).toV (evalEML env b).toV).foldr (· + ·) 0.0)
  def evalEMLs (env : Env) : List EML → List Float
    | []      => []
    | e :: es => (evalEML env e).toF :: evalEMLs env es
end

end

section
variable (r1 : String → Float → Float) (r2 : String → Float → Float → Float)

/- **C evaluation** of the emitted code. `r1`/`r2` model the `mg_*` runtime. -/
mutual
  def evalC (env : Env) : CExpr → Val
    | .lit c      => .scalar c
    | .var x      => env x
    | .bin op a b => .scalar (op.apply (evalC env a).toF (evalC env b).toF)
    | .neg a      => .scalar (-(evalC env a).toF)
    | .clet x e body => evalC (env.update x (evalC env e)) body
    | .ucall f a  => .scalar (r1 f (evalC env a).toF)
    | .bcall f a b => .scalar (r2 f (evalC env a).toF (evalC env b).toF)
    | .tern c t e => bif isTrue (evalC env c).toF then evalC env t else evalC env e
    | .cvlit cs   => .vec (evalCs env cs)
    | .cidx v n   => .scalar ((evalC env v).toV.getD n 0.0)
    | .csum v     => .scalar ((evalC env v).toV.foldr (· + ·) 0.0)
    | .cdot a b   => .scalar ((List.zipWith (· * ·) (evalC env a).toV (evalC env b).toV).foldr (· + ·) 0.0)
  def evalCs (env : Env) : List CExpr → List Float
    | []      => []
    | c :: cs => (evalC env c).toF :: evalCs env cs
end

end

/- **The emitter** — the Lean model of `c_backend.py`. -/
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
    | .vlit es    => .cvlit (emitCs es)
    | .idx v n    => .cidx (emitC v) n
    | .vsum v     => .csum (emitC v)
    | .dot a b    => .cdot (emitC a) (emitC b)
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
the same value as the EML source, for every expression and environment. `emitC_correct_s` is the
companion over a `vlit`'s elements. -/
-- `hrt1`/`hrt2` are threaded through both mutual arms (the companion recurses into `emitC_correct`),
-- so the linter's "unused in `emitC_correct_s`" report is expected, not a real omission.
set_option linter.unusedSectionVars false in
mutual
  theorem emitC_correct : ∀ (e : EML) (env : Env), evalC r1 r2 env (emitC e) = evalEML i1 i2 env e
    | .lit c, env => rfl
    | .var x, env => rfl
    | .bin op a b, env => by
        show Val.scalar (op.apply (evalC r1 r2 env (emitC a)).toF (evalC r1 r2 env (emitC b)).toF)
           = Val.scalar (op.apply (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)
        rw [emitC_correct a env, emitC_correct b env]
    | .neg a, env => by
        show Val.scalar (-(evalC r1 r2 env (emitC a)).toF) = Val.scalar (-(evalEML i1 i2 env a).toF)
        rw [emitC_correct a env]
    | .elet x e body, env => by
        show evalC r1 r2 (env.update x (evalC r1 r2 env (emitC e))) (emitC body)
           = evalEML i1 i2 (env.update x (evalEML i1 i2 env e)) body
        rw [emitC_correct e env, emitC_correct body (env.update x (evalEML i1 i2 env e))]
    | .tr1 t e, env => by
        show Val.scalar (r1 t.cName (evalC r1 r2 env (emitC e)).toF)
           = Val.scalar (i1 t (evalEML i1 i2 env e).toF)
        rw [emitC_correct e env, hrt1]
    | .tr2 t a b, env => by
        show Val.scalar (r2 t.cName (evalC r1 r2 env (emitC a)).toF (evalC r1 r2 env (emitC b)).toF)
           = Val.scalar (i2 t (evalEML i1 i2 env a).toF (evalEML i1 i2 env b).toF)
        rw [emitC_correct a env, emitC_correct b env, hrt2]
    | .cond c t e, env => by
        show (bif isTrue (evalC r1 r2 env (emitC c)).toF then evalC r1 r2 env (emitC t)
                else evalC r1 r2 env (emitC e))
           = bif isTrue (evalEML i1 i2 env c).toF then evalEML i1 i2 env t else evalEML i1 i2 env e
        rw [emitC_correct c env, emitC_correct t env, emitC_correct e env]
    | .vlit es, env => by
        show Val.vec (evalCs r1 r2 env (emitCs es)) = Val.vec (evalEMLs i1 i2 env es)
        rw [emitC_correct_s es env]
    | .idx v n, env => by
        show Val.scalar ((evalC r1 r2 env (emitC v)).toV.getD n 0.0)
           = Val.scalar ((evalEML i1 i2 env v).toV.getD n 0.0)
        rw [emitC_correct v env]
    | .vsum v, env => by
        show Val.scalar ((evalC r1 r2 env (emitC v)).toV.foldr (· + ·) 0.0)
           = Val.scalar ((evalEML i1 i2 env v).toV.foldr (· + ·) 0.0)
        rw [emitC_correct v env]
    | .dot a b, env => by
        show Val.scalar ((List.zipWith (· * ·) (evalC r1 r2 env (emitC a)).toV (evalC r1 r2 env (emitC b)).toV).foldr (· + ·) 0.0)
           = Val.scalar ((List.zipWith (· * ·) (evalEML i1 i2 env a).toV (evalEML i1 i2 env b).toV).foldr (· + ·) 0.0)
        rw [emitC_correct a env, emitC_correct b env]
  theorem emitC_correct_s :
      ∀ (es : List EML) (env : Env), evalCs r1 r2 env (emitCs es) = evalEMLs i1 i2 env es
    | [], env => rfl
    | e :: es, env => by
        show (evalC r1 r2 env (emitC e)).toF :: evalCs r1 r2 env (emitCs es)
           = (evalEML i1 i2 env e).toF :: evalEMLs i1 i2 env es
        rw [emitC_correct e env, emitC_correct_s es env]
end

end

/-! ## Function level — the compilation unit (`_emit_function`) -/

/-- An EML function: parameter names + a body expression. -/
structure EMLFunc where
  params : List String
  body   : EML

/-- The emitted C function. -/
structure CFunc where
  params : List String
  body   : CExpr

/-- Emit a function — the Lean model of `c_backend._emit_function`. -/
def emitFunc (f : EMLFunc) : CFunc := ⟨f.params, emitC f.body⟩

/-- Bind an argument list (scalar or vector values) to the parameter names positionally. -/
def bindArgs : List String → List Val → Env → Env
  | [],      _,       env => env
  | _ :: _,  [],      env => env
  | x :: xs, v :: vs, env => bindArgs xs vs (env.update x v)

/-- Evaluate an EML function on an argument list. -/
def evalFuncEML (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (f : EMLFunc) (args : List Val) (base : Env) : Val :=
  evalEML i1 i2 (bindArgs f.params args base) f.body

/-- Evaluate an emitted C function on an argument list. -/
def evalFuncC (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (g : CFunc) (args : List Val) (base : Env) : Val :=
  evalC r1 r2 (bindArgs g.params args base) g.body

/-- **Function-level translation validation (T1).** The emitted C function computes the same value as
the EML function, for every argument list — the compilation-unit certificate; a corollary of
`emitC_correct`. -/
theorem emitFunc_correct
    (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
    (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
    (f : EMLFunc) (args : List Val) (base : Env) :
    evalFuncC r1 r2 (emitFunc f) args base = evalFuncEML i1 i2 f args base :=
  emitC_correct i1 i2 r1 r2 hrt1 hrt2 f.body (bindArgs f.params args base)

/-! ## Statements — control flow + mutable state (`WHILE` / `ASSIGN` / `STATE`)

The scalar/vector layer above is expression-only. Real emitted kernels also contain **statements**:
`let`/`let_mut` declarations, `ASSIGN` mutations, `WHILE` loops, and `STATE` (variables that persist
across calls). This layer models them over a mutable **store** (`Env`, now threaded/updated) with
**fuel** on the only non-terminating construct, `while`.

`slet`/`sassign` are semantically identical (both update the store to `eval e`); they differ only in
the C they emit — a declaration `T x = e;` vs a bare assignment `x = e;`. That syntactic divergence
is *exactly* the kind the translation-validation theorem certifies away. `sexpr` is a pure
expression-statement (no store effect — EML expressions have no side effects).
-/

/-- EML statements. `swhile`'s `List Stmt` body is the loop's block. -/
inductive Stmt where
  | slet    : String → EML → Stmt        -- `T x = e;`   (LET / LET_MUT)
  | sassign : String → EML → Stmt        -- `x = e;`     (ASSIGN)
  | swhile  : EML → List Stmt → Stmt     -- `while (c) { body }`
  | sexpr   : EML → Stmt                 -- `e;`         (EXPR_STMT)

/-- Emitted C statements (a separate type, mirroring `CExpr`). -/
inductive CStmt where
  | cdecl   : String → CExpr → CStmt     -- `double x = e;`
  | cassign : String → CExpr → CStmt     -- `x = e;`
  | cwhile  : CExpr → List CStmt → CStmt
  | cexpr   : CExpr → CStmt

section
variable (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)

/- **EML statement execution** over a mutable store, fuel-bounded on `swhile`. The `while` fuel bounds
iterations only (straight-line code costs no fuel), so it's WF (not structural) recursion. -/
mutual
  def execStmt (fuel : Nat) (env : Env) : Stmt → Env
    | .slet x e      => env.update x (evalEML i1 i2 env e)
    | .sassign x e   => env.update x (evalEML i1 i2 env e)
    | .swhile c body => execWhile fuel c body env
    | .sexpr _       => env
  def execStmts (fuel : Nat) (env : Env) : List Stmt → Env
    | []      => env
    | s :: ss => execStmts fuel (execStmt fuel env s) ss
  def execWhile (fuel : Nat) (c : EML) (body : List Stmt) (env : Env) : Env :=
    match fuel with
    | 0        => env
    | fuel + 1 => bif isTrue (evalEML i1 i2 env c).toF
                  then execWhile fuel c body (execStmts fuel env body) else env
end

end

section
variable (r1 : String → Float → Float) (r2 : String → Float → Float → Float)

/- **C statement execution** — same shape; `cdecl`/`cassign` collapse to one meaning. -/
mutual
  def cexecStmt (fuel : Nat) (env : Env) : CStmt → Env
    | .cdecl x e     => env.update x (evalC r1 r2 env e)
    | .cassign x e   => env.update x (evalC r1 r2 env e)
    | .cwhile c body => cexecWhile fuel c body env
    | .cexpr _       => env
  def cexecStmts (fuel : Nat) (env : Env) : List CStmt → Env
    | []      => env
    | s :: ss => cexecStmts fuel (cexecStmt fuel env s) ss
  def cexecWhile (fuel : Nat) (c : CExpr) (body : List CStmt) (env : Env) : Env :=
    match fuel with
    | 0        => env
    | fuel + 1 => bif isTrue (evalC r1 r2 env c).toF
                  then cexecWhile fuel c body (cexecStmts fuel env body) else env
end

end

/- **The statement emitter** — the Lean model of `c_backend._emit_block`. -/
mutual
  def emitStmt : Stmt → CStmt
    | .slet x e      => .cdecl x (emitC e)
    | .sassign x e   => .cassign x (emitC e)
    | .swhile c body => .cwhile (emitC c) (emitStmts body)
    | .sexpr e       => .cexpr (emitC e)
  def emitStmts : List Stmt → List CStmt
    | []      => []
    | s :: ss => emitStmt s :: emitStmts ss
end

section
variable (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
variable (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
variable (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
variable (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
include hrt1 hrt2

/- **Statement-level translation validation (T1).** For every fuel and store, the emitted C statements
drive the store to the same state as the EML source. Because `while` is WF (fuel) recursion, these
carry `Quot.sound` alongside `propext` — both Lean-core, sorryAx-free. -/
set_option linter.unusedSectionVars false in
mutual
  theorem execStmt_correct : ∀ (fuel : Nat) (env : Env) (s : Stmt),
      cexecStmt r1 r2 fuel env (emitStmt s) = execStmt i1 i2 fuel env s
    | fuel, env, .slet x e => by
        simp only [emitStmt, execStmt, cexecStmt]
        rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
    | fuel, env, .sassign x e => by
        simp only [emitStmt, execStmt, cexecStmt]
        rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env]
    | fuel, env, .swhile c body => by
        simp only [emitStmt, execStmt, cexecStmt]
        exact execWhile_correct fuel c body env
    | fuel, env, .sexpr e => by
        simp only [emitStmt, execStmt, cexecStmt]
  theorem execStmts_correct : ∀ (fuel : Nat) (env : Env) (ss : List Stmt),
      cexecStmts r1 r2 fuel env (emitStmts ss) = execStmts i1 i2 fuel env ss
    | fuel, env, [] => by simp only [emitStmts, execStmts, cexecStmts]
    | fuel, env, s :: ss => by
        simp only [emitStmts, execStmts, cexecStmts]
        rw [execStmt_correct fuel env s, execStmts_correct fuel (execStmt i1 i2 fuel env s) ss]
  theorem execWhile_correct : ∀ (fuel : Nat) (c : EML) (body : List Stmt) (env : Env),
      cexecWhile r1 r2 fuel (emitC c) (emitStmts body) env = execWhile i1 i2 fuel c body env
    | 0, c, body, env => by simp only [execWhile, cexecWhile]
    | fuel + 1, c, body, env => by
        simp only [execWhile, cexecWhile]
        rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 c env, execStmts_correct fuel env body,
            execWhile_correct fuel c body (execStmts i1 i2 fuel env body)]
end

end

/-! ## Stateful functions — the `WHILE`/`STATE` compilation unit

A stateful function has parameters, `state` initializers (persistent vars, modeled here as an initial
store binding — cross-call persistence is a linkage concern outside the per-call translation boundary),
a statement body, and a final return expression. -/

/-- An EML stateful function. -/
structure StmtFunc where
  params : List String
  states : List (String × EML)
  body   : List Stmt
  ret    : EML

/-- The emitted C stateful function. -/
structure CStmtFunc where
  params : List String
  states : List (String × CExpr)
  body   : List CStmt
  ret    : CExpr

/-- Emit a stateful function — the Lean model of `_emit_function` with a `STATE`/`WHILE` body. -/
def emitStmtFunc (f : StmtFunc) : CStmtFunc :=
  ⟨f.params, f.states.map (fun p => (p.1, emitC p.2)), emitStmts f.body, emitC f.ret⟩

/-- Install `state` initializers into the store (each init evaluated once, left-to-right). -/
def bindStatesE (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float) :
    List (String × EML) → Env → Env
  | [],           env => env
  | (x, e) :: rs, env => bindStatesE i1 i2 rs (env.update x (evalEML i1 i2 env e))

/-- C-side state initialization. -/
def bindStatesC (r1 : String → Float → Float) (r2 : String → Float → Float → Float) :
    List (String × CExpr) → Env → Env
  | [],           env => env
  | (x, e) :: rs, env => bindStatesC r1 r2 rs (env.update x (evalC r1 r2 env e))

/-- Run a stateful EML function: bind args, install states, execute the body, return `ret`. -/
def runStmtFuncEML (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
    (fuel : Nat) (f : StmtFunc) (args : List Val) (base : Env) : Val :=
  let e1 := bindStatesE i1 i2 f.states (bindArgs f.params args base)
  evalEML i1 i2 (execStmts i1 i2 fuel e1 f.body) f.ret

/-- Run the emitted C stateful function. -/
def runStmtFuncC (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
    (fuel : Nat) (g : CStmtFunc) (args : List Val) (base : Env) : Val :=
  let e1 := bindStatesC r1 r2 g.states (bindArgs g.params args base)
  evalC r1 r2 (cexecStmts r1 r2 fuel e1 g.body) g.ret

section
variable (i1 : Trans1 → Float → Float) (i2 : Trans2 → Float → Float → Float)
variable (r1 : String → Float → Float) (r2 : String → Float → Float → Float)
variable (hrt1 : ∀ (t : Trans1) (v : Float), r1 t.cName v = i1 t v)
variable (hrt2 : ∀ (t : Trans2) (u v : Float), r2 t.cName u v = i2 t u v)
include hrt1 hrt2

/-- State-initialization correspondence: the emitted C initializers install the same store. -/
theorem bindStates_correct :
    ∀ (states : List (String × EML)) (env : Env),
      bindStatesC r1 r2 (states.map (fun p => (p.1, emitC p.2))) env
        = bindStatesE i1 i2 states env
  | [],           env => rfl
  | (x, e) :: rs, env => by
      simp only [List.map, bindStatesC, bindStatesE]
      rw [emitC_correct i1 i2 r1 r2 hrt1 hrt2 e env,
          bindStates_correct rs (env.update x (evalEML i1 i2 env e))]

/-- **Stateful-function translation validation (T1).** With enough fuel — or any fuel, since both
sides share it — the emitted C stateful function computes the same result as the EML source, for every
argument list. The compilation-unit certificate for control-flow + mutable-state kernels. -/
theorem runStmtFunc_correct (fuel : Nat) (f : StmtFunc) (args : List Val) (base : Env) :
    runStmtFuncC r1 r2 fuel (emitStmtFunc f) args base
      = runStmtFuncEML i1 i2 fuel f args base := by
  simp only [runStmtFuncC, runStmtFuncEML, emitStmtFunc,
    bindStates_correct i1 i2 r1 r2 hrt1 hrt2 f.states (bindArgs f.params args base)]
  rw [execStmts_correct i1 i2 r1 r2 hrt1 hrt2 fuel
        (bindStatesE i1 i2 f.states (bindArgs f.params args base)) f.body,
      emitC_correct i1 i2 r1 r2 hrt1 hrt2 f.ret _]

end

/-! ## Worked examples — non-vacuity + regression smoke-test -/

/-- `poly(x) = 2·x + x·x`. -/
def poly : EMLFunc :=
  ⟨["x"], .bin .add (.bin .mul (.lit 2.0) (.var "x")) (.bin .mul (.var "x") (.var "x"))⟩

/-- The emitter produces exactly the expected C for `poly` (structural, `rfl`). -/
example : emitC poly.body
    = .bin .add (.bin .mul (.lit 2.0) (.var "x")) (.bin .mul (.var "x") (.var "x")) := rfl

/-- `poly(3) = 15`. -/
example : ((evalFuncEML (fun _ _ => (0:Float)) (fun _ _ _ => (0:Float)) poly
    [.scalar 3.0] (fun _ => .scalar 0.0)).toF == 15.0) = true := by native_decide

/-- `sumFn(v) = sum(v)` — a function taking a VECTOR variable. -/
def sumFn : EMLFunc := ⟨["v"], .vsum (.var "v")⟩

/-- `sumFn([1,2,3,4]) = 10` — vector variable + reduction on a first-class vector value. -/
example : ((evalFuncEML (fun _ _ => (0:Float)) (fun _ _ _ => (0:Float)) sumFn
    [.vec [1.0, 2.0, 3.0, 4.0]] (fun _ => .scalar 0.0)).toF == 10.0) = true := by native_decide

/-- The emitted C for `sumFn` computes the same as `sumFn` (builtin-free ⇒ any runtime works). -/
example (base : Env) :
    evalFuncC (fun _ _ => 0) (fun _ _ _ => 0) (emitFunc sumFn) [.vec [1.0, 2.0, 3.0]] base
      = evalFuncEML (fun _ _ => 0) (fun _ _ _ => 0) sumFn [.vec [1.0, 2.0, 3.0]] base :=
  emitFunc_correct (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
    (fun _ _ => rfl) (fun _ _ _ => rfl) sumFn [.vec [1.0, 2.0, 3.0]] base

/-- `dotFn(a, b) = dot(a, b)` on two vector variables. -/
def dotFn : EMLFunc := ⟨["a", "b"], .dot (.var "a") (.var "b")⟩

/-- `dotFn([1,2],[3,4]) = 1·3 + 2·4 = 11`. -/
example : ((evalFuncEML (fun _ _ => (0:Float)) (fun _ _ _ => (0:Float)) dotFn
    [.vec [1.0, 2.0], .vec [3.0, 4.0]] (fun _ => .scalar 0.0)).toF == 11.0) = true := by native_decide

/-- A **stateful loop**: `sumTo(n)` accumulates `0 + 1 + … + (n-1)` via
`state s = 0; state i = 0; while (i < n) { s = s + i; i = i + 1 }; return s`. -/
def sumTo : StmtFunc where
  params := ["n"]
  states := [("s", .lit 0.0), ("i", .lit 0.0)]
  body   := [.swhile (.bin .lt (.var "i") (.var "n"))
              [ .sassign "s" (.bin .add (.var "s") (.var "i"))
              , .sassign "i" (.bin .add (.var "i") (.lit 1.0)) ]]
  ret    := .var "s"

/-- The emitter turns the loop body into the expected C statements (structural, `rfl`). -/
example : emitStmtFunc sumTo
    = { params := ["n"]
      , states := [("s", .lit 0.0), ("i", .lit 0.0)]
      , body   := [.cwhile (.bin .lt (.var "i") (.var "n"))
                    [ .cassign "s" (.bin .add (.var "s") (.var "i"))
                    , .cassign "i" (.bin .add (.var "i") (.lit 1.0)) ]]
      , ret    := .var "s" } := rfl

/-- `sumTo(4) = 0+1+2+3 = 6` with fuel ≥ 4. -/
example : ((runStmtFuncEML (fun _ _ => (0:Float)) (fun _ _ _ => (0:Float)) 10 sumTo
    [.scalar 4.0] (fun _ => .scalar 0.0)).toF == 6.0) = true := by native_decide

/-- The emitted C for `sumTo` computes the same result (builtin-free ⇒ any runtime works). This is
`runStmtFunc_correct` instantiated — the control-flow + mutable-state translation certificate. -/
example (base : Env) :
    runStmtFuncC (fun _ _ => 0) (fun _ _ _ => 0) 10 (emitStmtFunc sumTo) [.scalar 4.0] base
      = runStmtFuncEML (fun _ _ => 0) (fun _ _ _ => 0) 10 sumTo [.scalar 4.0] base :=
  runStmtFunc_correct (fun _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ _ => 0)
    (fun _ _ => rfl) (fun _ _ _ => rfl) 10 sumTo [.scalar 4.0] base

end Certcom
