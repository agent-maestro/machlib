import MachLib.Ring

/-!
# MachLib.MultiPoly — multivariate polynomial AST for Pfaffian chains

This module is the **phase-1 infrastructure** for the
`derivative_rank_lt` closure refactor. See
`machlib/DERIVATIVE_RANK_LT_REFACTOR_PLAN.md` for the full plan.

The `MultiPoly n` type represents a polynomial in `(x, y_1, ..., y_n)`
where `x : Real` is the independent variable and `y_1, ..., y_n` are
the chain variables (which will eventually be tied to specific
real-valued functions via a `PfaffianChain`).

This is deliberately small. It provides:

- The inductive `MultiPoly n` AST
- `eval` (real-valued evaluation given values for x and the y_i)
- `degreeX`, `degreeY i`, `totalDegree` (formal degree counts)
- Derived constructors: `zero`, `one`, `neg`, `pow`
- Formal partial derivatives `∂/∂x`, `∂/∂y_i`
- A handful of sanity theorems for use by downstream chain machinery

Phase 2 will build `PfaffianChain` + `PfaffianFn` on top, exposing
the chain relations `y_i' = P_i(x, y_1, ..., y_i)` so the bound
proof can induct on chain length (replacing the broken
rank-on-derivative induction).

Zero Mathlib dependency. -/

namespace MachLib
namespace MultiPolyMod

open MachLib.Real

/-- AST for a polynomial in `(x, y_1, ..., y_n)` over `Real`. The
chain variables are indexed by `Fin n`. -/
inductive MultiPoly (n : Nat) : Type where
  | const : Real → MultiPoly n
  | varX  : MultiPoly n
  | varY  : Fin n → MultiPoly n
  | add   : MultiPoly n → MultiPoly n → MultiPoly n
  | sub   : MultiPoly n → MultiPoly n → MultiPoly n
  | mul   : MultiPoly n → MultiPoly n → MultiPoly n

namespace MultiPoly

/-! ## Evaluation -/

/-- Evaluate a `MultiPoly n` given a value of `x` and a vector of
chain-variable values `env : Fin n → Real`. -/
noncomputable def eval {n : Nat} :
    MultiPoly n → Real → (Fin n → Real) → Real
  | const c,  _, _    => c
  | varX,     x, _    => x
  | varY i,   _, env  => env i
  | add p q,  x, env  => eval p x env + eval q x env
  | sub p q,  x, env  => eval p x env - eval q x env
  | mul p q,  x, env  => eval p x env * eval q x env

/-! ## Derived constructors -/

/-- The zero polynomial. -/
noncomputable def zero {n : Nat} : MultiPoly n := const 0

/-- The one polynomial. -/
noncomputable def one {n : Nat} : MultiPoly n := const 1

/-- Negation: `-p = 0 - p`. -/
noncomputable def neg {n : Nat} (p : MultiPoly n) : MultiPoly n :=
  sub zero p

/-- Repeated multiplication by self: `pow p k = p * p * ... * p` (k times).
Convention: `pow p 0 = one`. -/
noncomputable def pow {n : Nat} : MultiPoly n → Nat → MultiPoly n
  | _, 0       => one
  | p, k + 1   => mul p (pow p k)

/-! ## Degree functions -/

/-- Total formal degree in all variables. Coincides with the standard
notion for polynomials: const→0, vars→1, add/sub→max, mul→sum. -/
def totalDegree {n : Nat} : MultiPoly n → Nat
  | const _   => 0
  | varX      => 1
  | varY _    => 1
  | add p q   => Nat.max (totalDegree p) (totalDegree q)
  | sub p q   => Nat.max (totalDegree p) (totalDegree q)
  | mul p q   => totalDegree p + totalDegree q

/-- Degree in `x` (treating each `varY i` as a constant of degree 0). -/
def degreeX {n : Nat} : MultiPoly n → Nat
  | const _   => 0
  | varX      => 1
  | varY _    => 0
  | add p q   => Nat.max (degreeX p) (degreeX q)
  | sub p q   => Nat.max (degreeX p) (degreeX q)
  | mul p q   => degreeX p + degreeX q

/-- Degree in chain variable `y_i` (treating `x` and other `y_j` as
constants of degree 0). -/
def degreeY {n : Nat} (i : Fin n) : MultiPoly n → Nat
  | const _   => 0
  | varX      => 0
  | varY j    => if i = j then 1 else 0
  | add p q   => Nat.max (degreeY i p) (degreeY i q)
  | sub p q   => Nat.max (degreeY i p) (degreeY i q)
  | mul p q   => degreeY i p + degreeY i q

/-! ## Formal partial derivatives

These are the **formal** symbolic derivatives — `∂/∂x` treats every
`varY i` as a constant; `∂/∂y_i` treats `x` and every `varY j` (j ≠ i)
as a constant. They are NOT the total derivative under the chain
relations (that requires chain context and lives in phase 2). -/

/-- Formal partial derivative with respect to `x`. -/
noncomputable def dX {n : Nat} : MultiPoly n → MultiPoly n
  | const _   => const 0
  | varX      => const 1
  | varY _    => const 0
  | add p q   => add (dX p) (dX q)
  | sub p q   => sub (dX p) (dX q)
  | mul p q   => add (mul (dX p) q) (mul p (dX q))

/-- Formal partial derivative with respect to `y_i`. -/
noncomputable def dY {n : Nat} (i : Fin n) : MultiPoly n → MultiPoly n
  | const _   => const 0
  | varX      => const 0
  | varY j    => if i = j then const 1 else const 0
  | add p q   => add (dY i p) (dY i q)
  | sub p q   => sub (dY i p) (dY i q)
  | mul p q   => add (mul (dY i p) q) (mul p (dY i q))

/-! ## Sanity theorems for eval -/

theorem eval_const {n : Nat} (c : Real) (x : Real) (env : Fin n → Real) :
    eval (const c) x env = c := rfl

theorem eval_varX {n : Nat} (x : Real) (env : Fin n → Real) :
    eval (varX (n := n)) x env = x := rfl

theorem eval_varY {n : Nat} (i : Fin n) (x : Real) (env : Fin n → Real) :
    eval (varY i) x env = env i := rfl

theorem eval_add {n : Nat} (p q : MultiPoly n) (x : Real)
    (env : Fin n → Real) :
    eval (add p q) x env = eval p x env + eval q x env := rfl

theorem eval_sub {n : Nat} (p q : MultiPoly n) (x : Real)
    (env : Fin n → Real) :
    eval (sub p q) x env = eval p x env - eval q x env := rfl

theorem eval_mul {n : Nat} (p q : MultiPoly n) (x : Real)
    (env : Fin n → Real) :
    eval (mul p q) x env = eval p x env * eval q x env := rfl

theorem eval_zero {n : Nat} (x : Real) (env : Fin n → Real) :
    eval (zero (n := n)) x env = 0 := rfl

theorem eval_one {n : Nat} (x : Real) (env : Fin n → Real) :
    eval (one (n := n)) x env = 1 := rfl

/-! ## Degree sanity -/

theorem degreeX_const {n : Nat} (c : Real) :
    degreeX (const c : MultiPoly n) = 0 := rfl

theorem degreeX_varX {n : Nat} : degreeX (varX (n := n)) = 1 := rfl

theorem degreeX_varY {n : Nat} (i : Fin n) :
    degreeX (varY i) = 0 := rfl

theorem degreeY_const {n : Nat} (i : Fin n) (c : Real) :
    degreeY i (const c : MultiPoly n) = 0 := rfl

theorem degreeY_varX {n : Nat} (i : Fin n) :
    degreeY i (varX (n := n)) = 0 := rfl

theorem totalDegree_const {n : Nat} (c : Real) :
    totalDegree (const c : MultiPoly n) = 0 := rfl

theorem totalDegree_varX {n : Nat} : totalDegree (varX (n := n)) = 1 := rfl

theorem totalDegree_varY {n : Nat} (i : Fin n) :
    totalDegree (varY i) = 1 := rfl

/-! ## Key formal-derivative property: dX weakly decreases degreeX

The **structural fact that fails for the current PfaffianExpr** but
holds here: polynomial degree in x is non-increasing under formal ∂/∂x.

(STRICT decrease — `degreeX (dX p) < degreeX p` when `degreeX p ≥ 1` —
holds only for *canonical-form* polynomials. The naive AST allows
phantom terms like `c * x` whose `dX` is `0*x + c*1`, where the `0*x`
term contributes a formal degree of 1 even though it evaluates to 0.
Canonical-form normalization is phase-2 work; see
`PolynomialRootCount.lean`'s `polySimplify` for the analogous
single-variable construction.) -/

/-- Helper: Nat.max is monotone in both arguments. -/
private theorem nat_max_le_max {a b c d : Nat}
    (hac : a ≤ c) (hbd : b ≤ d) : Nat.max a b ≤ Nat.max c d := by
  simp only [Nat.max_def]
  by_cases h : a ≤ b <;> by_cases h' : c ≤ d <;> simp [h, h'] <;> omega

/-- Helper: strict variant of max-monotonicity. -/
private theorem nat_max_lt_max_strict {a b c d : Nat}
    (hac : a < c) (hbd : b < d) : Nat.max a b < Nat.max c d := by
  simp only [Nat.max_def]
  by_cases h : a ≤ b <;> by_cases h' : c ≤ d <;> simp [h, h'] <;> omega

/-- ∂/∂x weakly decreases `degreeX`. -/
theorem degreeX_dX_le {n : Nat} : ∀ p : MultiPoly n,
    degreeX (dX p) ≤ degreeX p
  | const _ => by simp [dX, degreeX]
  | varX    => by simp [dX, degreeX]
  | varY _  => by simp [dX, degreeX]
  | add p q => by
      show Nat.max (degreeX (dX p)) (degreeX (dX q)) ≤
            Nat.max (degreeX p) (degreeX q)
      exact nat_max_le_max (degreeX_dX_le p) (degreeX_dX_le q)
  | sub p q => by
      show Nat.max (degreeX (dX p)) (degreeX (dX q)) ≤
            Nat.max (degreeX p) (degreeX q)
      exact nat_max_le_max (degreeX_dX_le p) (degreeX_dX_le q)
  | mul p q => by
      show Nat.max (degreeX (dX p) + degreeX q) (degreeX p + degreeX (dX q)) ≤
            degreeX p + degreeX q
      have hp := degreeX_dX_le p
      have hq := degreeX_dX_le q
      apply Nat.max_le.mpr
      refine ⟨?_, ?_⟩
      · exact Nat.add_le_add_right hp _
      · exact Nat.add_le_add_left hq _

end MultiPoly
end MultiPolyMod
end MachLib
