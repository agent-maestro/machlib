import MachLib.Ring
import MachLib.Differentiation

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

/-! ## Leading coefficient in `y_i` (Khovanskii Step 3a)

The **formal leading coefficient** when a `MultiPoly n` is viewed as a
polynomial in the chain variable `y_i`. The result is a `MultiPoly n`
that — inductively — does not contain `varY i`.

For the Khovanskii termination argument, the pair
  `(degreeY i p, degreeX (leadingCoeffY i p))`
forms the lex measure that decreases under `scaledReduction`. Step 3a
ships the definition + basic correctness (degreeY i of the result is 0).
Step 3b proves the lex decrease under scaledReduction. Step 3c handles
dropLast. Step 3d combines into termination. -/

/-- Formal leading coefficient in `y_i`. Result inductively does not
contain `varY i`.

  - `const c`: leading is c (degree 0 in y_i).
  - `varX`: leading is x (degree 0 in y_i).
  - `varY j`: j = i → `const 1` (degree 1, leading 1);
              j ≠ i → `varY j` (degree 0, leading is itself).
  - `add p q`: degrees max; leading is from the higher, or sum if equal.
  - `sub p q`: similar; if q dominates, leading is negated.
  - `mul p q`: degrees add; leading is product of leadings. -/
noncomputable def leadingCoeffY {n : Nat} (i : Fin n) :
    MultiPoly n → MultiPoly n
  | const c   => const c
  | varX      => varX
  | varY j    => if j = i then const 1 else varY j
  | add p q   =>
      if degreeY i p > degreeY i q then leadingCoeffY i p
      else if degreeY i q > degreeY i p then leadingCoeffY i q
      else add (leadingCoeffY i p) (leadingCoeffY i q)
  | sub p q   =>
      if degreeY i p > degreeY i q then leadingCoeffY i p
      else if degreeY i q > degreeY i p then sub (const 0) (leadingCoeffY i q)
      else sub (leadingCoeffY i p) (leadingCoeffY i q)
  | mul p q   => mul (leadingCoeffY i p) (leadingCoeffY i q)

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

/-! ## leadingCoeffY correctness — degreeY of leading is 0 -/

/-- **The leading coefficient does not contain `varY i`.** Structural
induction on `p`. -/
theorem degreeY_leadingCoeffY {n : Nat} (i : Fin n) :
    ∀ p : MultiPoly n, degreeY i (leadingCoeffY i p) = 0
  | const _   => rfl
  | varX      => rfl
  | varY j    => by
    show degreeY i (if j = i then const 1 else varY j) = 0
    by_cases h : j = i
    · simp [h]; rfl
    · simp [h]
      -- Goal: degreeY i (varY j) = 0, i.e., (if i = j then 1 else 0) = 0.
      show (if i = j then 1 else 0) = 0
      have h' : i ≠ j := fun heq => h heq.symm
      simp [h']
  | add p q   => by
    show degreeY i (if degreeY i p > degreeY i q then leadingCoeffY i p
                    else if degreeY i q > degreeY i p then leadingCoeffY i q
                    else add (leadingCoeffY i p) (leadingCoeffY i q)) = 0
    by_cases h1 : degreeY i p > degreeY i q
    · simp [h1]; exact degreeY_leadingCoeffY i p
    · by_cases h2 : degreeY i q > degreeY i p
      · simp [h1, h2]; exact degreeY_leadingCoeffY i q
      · simp [h1, h2]
        show Nat.max (degreeY i (leadingCoeffY i p))
                      (degreeY i (leadingCoeffY i q)) = 0
        rw [degreeY_leadingCoeffY i p, degreeY_leadingCoeffY i q]
        rfl
  | sub p q   => by
    show degreeY i (if degreeY i p > degreeY i q then leadingCoeffY i p
                    else if degreeY i q > degreeY i p then
                      sub (const 0) (leadingCoeffY i q)
                    else sub (leadingCoeffY i p) (leadingCoeffY i q)) = 0
    by_cases h1 : degreeY i p > degreeY i q
    · simp [h1]; exact degreeY_leadingCoeffY i p
    · by_cases h2 : degreeY i q > degreeY i p
      · simp [h1, h2]
        show Nat.max (degreeY i (const 0 : MultiPoly n))
                      (degreeY i (leadingCoeffY i q)) = 0
        rw [degreeY_leadingCoeffY i q]
        rfl
      · simp [h1, h2]
        show Nat.max (degreeY i (leadingCoeffY i p))
                      (degreeY i (leadingCoeffY i q)) = 0
        rw [degreeY_leadingCoeffY i p, degreeY_leadingCoeffY i q]
        rfl
  | mul p q   => by
    show degreeY i (mul (leadingCoeffY i p) (leadingCoeffY i q)) = 0
    show degreeY i (leadingCoeffY i p) + degreeY i (leadingCoeffY i q) = 0
    rw [degreeY_leadingCoeffY i p, degreeY_leadingCoeffY i q]

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

/-! ## Normalization — multiSimplify

Mirrors `PolynomialRootCount.polySimplify`'s single-variable pattern.
Eliminates phantom `0*x` and `1*x` terms so that formal degree
reflects effective degree. Crucial for proving strict degree decrease
under `dX` (which fails on the naive AST — see the discussion above). -/

/-! ## Substitution: replace `y_i` with another polynomial

Used by the constructive Khovanskii chain-step reduction (item 3 of
4 in the constructive-Khovanskii closure path) — substituting the
chain relation's polynomial for the highest chain variable
projects to a smaller chain. -/

/-- Substitute `y_i` with the polynomial `q` everywhere in `p`. -/
noncomputable def substY {n : Nat} (i : Fin n) (q : MultiPoly n) :
    MultiPoly n → MultiPoly n
  | const c => const c
  | varX => varX
  | varY j => if i = j then q else varY j
  | add p1 p2 => add (substY i q p1) (substY i q p2)
  | sub p1 p2 => sub (substY i q p1) (substY i q p2)
  | mul p1 p2 => mul (substY i q p1) (substY i q p2)

/-! ### Eval correctness for substY -/

/-- Updating one slot of an environment. Used in the eval theorem
for `substY`: substituting `q` for `y_i` semantically means evaluating
with `env i` replaced by `eval q x env`. -/
noncomputable def updateEnv {n : Nat} (env : Fin n → Real) (i : Fin n)
    (v : Real) : Fin n → Real :=
  fun j => if i = j then v else env j

/-- Eval distributes through substitution: substituting q for y_i
in p and evaluating equals evaluating p with the env's i-slot
replaced by eval q. -/
theorem eval_substY {n : Nat} (i : Fin n) (q : MultiPoly n)
    (p : MultiPoly n) (x : Real) (env : Fin n → Real) :
    eval (substY i q p) x env =
    eval p x (updateEnv env i (eval q x env)) := by
  induction p with
  | const c =>
    show c = c
    rfl
  | varX =>
    show x = x
    rfl
  | varY j =>
    -- substY i q (varY j) = if i = j then q else varY j
    -- eval (varY j) x (updateEnv env i (eval q x env))
    --   = (updateEnv env i (eval q x env)) j
    --   = if i = j then eval q x env else env j
    show eval (if i = j then q else varY j) x env
       = (updateEnv env i (eval q x env)) j
    by_cases h : i = j
    · simp [h, updateEnv]
    · simp [h, updateEnv]
      show eval (varY j) x env = env j
      rfl
  | add p1 p2 ih1 ih2 =>
    show eval (substY i q p1) x env + eval (substY i q p2) x env
       = eval p1 x (updateEnv env i (eval q x env))
       + eval p2 x (updateEnv env i (eval q x env))
    rw [ih1, ih2]
  | sub p1 p2 ih1 ih2 =>
    show eval (substY i q p1) x env - eval (substY i q p2) x env
       = eval p1 x (updateEnv env i (eval q x env))
       - eval p2 x (updateEnv env i (eval q x env))
    rw [ih1, ih2]
  | mul p1 p2 ih1 ih2 =>
    show eval (substY i q p1) x env * eval (substY i q p2) x env
       = eval p1 x (updateEnv env i (eval q x env))
       * eval p2 x (updateEnv env i (eval q x env))
    rw [ih1, ih2]

/-! ### Degree bound for substY

The Khovanskii chain-step reduction needs to bound the polynomial
degree after substituting a chain relation for a chain variable.
The bound:

  totalDegree (substY i q p) ≤ totalDegree p * (1 + totalDegree q)

Tight at p = (varY i)^k where the bound becomes k * tD(q) and the
LHS equals exactly k * tD(q). -/
theorem totalDegree_substY_le {n : Nat} (i : Fin n) (q : MultiPoly n)
    (p : MultiPoly n) :
    totalDegree (substY i q p) ≤ totalDegree p * (1 + totalDegree q) := by
  induction p with
  | const c =>
    show (0 : Nat) ≤ 0 * (1 + totalDegree q)
    simp
  | varX =>
    show (1 : Nat) ≤ 1 * (1 + totalDegree q)
    rw [Nat.one_mul]
    exact Nat.le_add_right 1 _
  | varY j =>
    show totalDegree (if i = j then q else varY j) ≤
         1 * (1 + totalDegree q)
    by_cases h : i = j
    · -- substY varY_i = q. Goal becomes totalDegree q ≤ 1 + totalDegree q.
      simp [h, Nat.one_mul]
    · -- substY varY_j (j ≠ i) = varY j. Goal: 1 ≤ 1 + totalDegree q.
      simp [h, Nat.one_mul]
      exact Nat.le_add_right 1 _
  | add p1 p2 ih1 ih2 =>
    show Nat.max (totalDegree (substY i q p1)) (totalDegree (substY i q p2)) ≤
         Nat.max (totalDegree p1) (totalDegree p2) * (1 + totalDegree q)
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · have hp1_le_max : totalDegree p1 ≤ Nat.max (totalDegree p1) (totalDegree p2) :=
        Nat.le_max_left _ _
      have hmul : totalDegree p1 * (1 + totalDegree q) ≤
             Nat.max (totalDegree p1) (totalDegree p2) * (1 + totalDegree q) :=
        Nat.mul_le_mul_right _ hp1_le_max
      exact Nat.le_trans ih1 hmul
    · have hp2_le_max : totalDegree p2 ≤ Nat.max (totalDegree p1) (totalDegree p2) :=
        Nat.le_max_right _ _
      have hmul : totalDegree p2 * (1 + totalDegree q) ≤
             Nat.max (totalDegree p1) (totalDegree p2) * (1 + totalDegree q) :=
        Nat.mul_le_mul_right _ hp2_le_max
      exact Nat.le_trans ih2 hmul
  | sub p1 p2 ih1 ih2 =>
    show Nat.max (totalDegree (substY i q p1)) (totalDegree (substY i q p2)) ≤
         Nat.max (totalDegree p1) (totalDegree p2) * (1 + totalDegree q)
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · have hp1_le_max : totalDegree p1 ≤ Nat.max (totalDegree p1) (totalDegree p2) :=
        Nat.le_max_left _ _
      have hmul : totalDegree p1 * (1 + totalDegree q) ≤
             Nat.max (totalDegree p1) (totalDegree p2) * (1 + totalDegree q) :=
        Nat.mul_le_mul_right _ hp1_le_max
      exact Nat.le_trans ih1 hmul
    · have hp2_le_max : totalDegree p2 ≤ Nat.max (totalDegree p1) (totalDegree p2) :=
        Nat.le_max_right _ _
      have hmul : totalDegree p2 * (1 + totalDegree q) ≤
             Nat.max (totalDegree p1) (totalDegree p2) * (1 + totalDegree q) :=
        Nat.mul_le_mul_right _ hp2_le_max
      exact Nat.le_trans ih2 hmul
  | mul p1 p2 ih1 ih2 =>
    show totalDegree (substY i q p1) + totalDegree (substY i q p2) ≤
         (totalDegree p1 + totalDegree p2) * (1 + totalDegree q)
    rw [Nat.add_mul]
    exact Nat.add_le_add ih1 ih2

/-! ### Drop last chain variable (chain-projection on the polynomial)

When `degreeY n p = 0` for `p : MultiPoly (n+1)` (i.e., p doesn't
depend on the last chain variable), p can be projected to
`MultiPoly n`. This is the polynomial-level chain projection used
by Item 4 (Khovanskii reduction) to reduce chain length.

The construction is structural: replace `varY ⟨n, _⟩` with `const 0`
(safe under the degreeY n = 0 hypothesis). -/
noncomputable def dropLastY {n : Nat} : MultiPoly (n + 1) → MultiPoly n
  | .const c => .const c
  | .varX => .varX
  | .varY i =>
      if h : i.val < n then .varY ⟨i.val, h⟩
      else .const 0
  | .add p q => .add (dropLastY p) (dropLastY q)
  | .sub p q => .sub (dropLastY p) (dropLastY q)
  | .mul p q => .mul (dropLastY p) (dropLastY q)

/-- **Eval correctness for `dropLastY`.** When `degreeY n p = 0`
(p doesn't depend on the last chain variable), `dropLastY p`
evaluates to the same value as p (with the env restricted to the
first n slots, ignoring whatever is in slot n).

This is the LOAD-BEARING correctness theorem for the chain-projection
step in Item 4: it says that when we drop a chain variable that
the polynomial doesn't depend on, the eval is preserved. -/
theorem eval_dropLastY {n : Nat} (p : MultiPoly (n + 1))
    (hp : degreeY ⟨n, Nat.lt_succ_self n⟩ p = 0)
    (x : Real) (env : Fin (n + 1) → Real) :
    eval (dropLastY p) x (fun i => env ⟨i.val, by omega⟩) = eval p x env := by
  induction p with
  | const c =>
    show c = c
    rfl
  | varX =>
    show x = x
    rfl
  | varY i =>
    -- dropLastY (varY i) = if i.val < n then varY ⟨i.val, _⟩ else const 0.
    -- For i.val = n: degreeY n (varY n) = 1, contradicts hp = 0.
    -- For i.val < n: eval matches.
    show eval (if h : i.val < n then varY ⟨i.val, h⟩ else const 0) x
              (fun i => env ⟨i.val, by omega⟩)
       = env i
    by_cases h : i.val < n
    · simp only [h, dite_true]
      show env ⟨i.val, by omega⟩ = env i
      have : (⟨i.val, by omega⟩ : Fin (n + 1)) = i :=
        Fin.eq_of_val_eq rfl
      rw [this]
    · -- i.val ≥ n + 1's bound means i.val = n. But then degreeY n (varY n) = 1.
      -- Contradiction with hp = 0.
      simp only [h, dite_false]
      exfalso
      have hi_eq : i.val = n := by
        have := i.isLt
        omega
      have : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) = i := by
        apply Fin.eq_of_val_eq
        show n = i.val
        omega
      rw [this] at hp
      -- hp : degreeY i (varY i) = 0. But degreeY i (varY i) = 1 by definition.
      have hone : degreeY i (varY i) = 1 := by
        show (if i = i then 1 else 0) = 1
        simp
      rw [hone] at hp
      exact absurd hp (by omega)
  | add p q ihp ihq =>
    -- degreeY n (add p q) = max (degreeY n p) (degreeY n q) = 0.
    -- So both degreeY n p = 0 and degreeY n q = 0. Apply IHs.
    have hp_q : degreeY ⟨n, Nat.lt_succ_self n⟩ p = 0
              ∧ degreeY ⟨n, Nat.lt_succ_self n⟩ q = 0 := by
      have hmax : Nat.max (degreeY ⟨n, Nat.lt_succ_self n⟩ p)
                          (degreeY ⟨n, Nat.lt_succ_self n⟩ q) = 0 := hp
      have := Nat.max_le.mp (Nat.le_of_eq hmax)
      refine ⟨?_, ?_⟩ <;> omega
    show eval (dropLastY p) x (fun i => env ⟨i.val, by omega⟩)
       + eval (dropLastY q) x (fun i => env ⟨i.val, by omega⟩)
       = eval p x env + eval q x env
    rw [ihp hp_q.1, ihq hp_q.2]
  | sub p q ihp ihq =>
    have hp_q : degreeY ⟨n, Nat.lt_succ_self n⟩ p = 0
              ∧ degreeY ⟨n, Nat.lt_succ_self n⟩ q = 0 := by
      have hmax : Nat.max (degreeY ⟨n, Nat.lt_succ_self n⟩ p)
                          (degreeY ⟨n, Nat.lt_succ_self n⟩ q) = 0 := hp
      have := Nat.max_le.mp (Nat.le_of_eq hmax)
      refine ⟨?_, ?_⟩ <;> omega
    show eval (dropLastY p) x (fun i => env ⟨i.val, by omega⟩)
       - eval (dropLastY q) x (fun i => env ⟨i.val, by omega⟩)
       = eval p x env - eval q x env
    rw [ihp hp_q.1, ihq hp_q.2]
  | mul p q ihp ihq =>
    -- degreeY n (mul p q) = degreeY n p + degreeY n q = 0.
    -- So both are 0. Apply IHs.
    have hp_q : degreeY ⟨n, Nat.lt_succ_self n⟩ p = 0
              ∧ degreeY ⟨n, Nat.lt_succ_self n⟩ q = 0 := by
      have hsum : degreeY ⟨n, Nat.lt_succ_self n⟩ p
                + degreeY ⟨n, Nat.lt_succ_self n⟩ q = 0 := hp
      refine ⟨?_, ?_⟩ <;> omega
    show eval (dropLastY p) x (fun i => env ⟨i.val, by omega⟩)
       * eval (dropLastY q) x (fun i => env ⟨i.val, by omega⟩)
       = eval p x env * eval q x env
    rw [ihp hp_q.1, ihq hp_q.2]

/-- `dropLastY` preserves totalDegree (since we only replace nodes
with degree-0 constants). -/
theorem dropLastY_totalDegree_le {n : Nat} (p : MultiPoly (n + 1)) :
    totalDegree (dropLastY p) ≤ totalDegree p := by
  induction p with
  | const c => exact Nat.le_refl _
  | varX => exact Nat.le_refl _
  | varY i =>
    show totalDegree (if h : i.val < n then varY ⟨i.val, h⟩ else const 0) ≤ 1
    by_cases h : i.val < n
    · simp [h]
      show (1 : Nat) ≤ 1
      exact Nat.le_refl _
    · simp [h]
      show (0 : Nat) ≤ 1
      exact Nat.zero_le _
  | add p q ihp ihq =>
    show Nat.max (totalDegree (dropLastY p)) (totalDegree (dropLastY q)) ≤
         Nat.max (totalDegree p) (totalDegree q)
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans ihp (Nat.le_max_left _ _)
    · exact Nat.le_trans ihq (Nat.le_max_right _ _)
  | sub p q ihp ihq =>
    show Nat.max (totalDegree (dropLastY p)) (totalDegree (dropLastY q)) ≤
         Nat.max (totalDegree p) (totalDegree q)
    apply Nat.max_le.mpr
    refine ⟨?_, ?_⟩
    · exact Nat.le_trans ihp (Nat.le_max_left _ _)
    · exact Nat.le_trans ihq (Nat.le_max_right _ _)
  | mul p q ihp ihq =>
    show totalDegree (dropLastY p) + totalDegree (dropLastY q) ≤
         totalDegree p + totalDegree q
    exact Nat.add_le_add ihp ihq

/-- **degreeY preservation under dropLastY (≤ form).** For any j : Fin n,
`degreeY j (dropLastY p) ≤ degreeY ⟨j.val, _⟩ p`. This says: dropping
the last chain variable can only DECREASE (or preserve) the degree of
any remaining variable. Used for triangularity preservation in the
constructive Khovanskii iteration. -/
theorem degreeY_dropLastY_le {n : Nat} (p : MultiPoly (n + 1))
    (j : Fin n) :
    degreeY j (dropLastY p)
      ≤ degreeY ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ p := by
  induction p with
  | const c => exact Nat.le_refl _
  | varX => exact Nat.le_refl _
  | varY i =>
    show degreeY j (if h : i.val < n then varY ⟨i.val, h⟩ else const 0)
       ≤ (if ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = i then 1 else 0)
    by_cases h : i.val < n
    · simp only [h, dite_true]
      show (if j = ⟨i.val, h⟩ then 1 else 0)
         ≤ (if ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ = i then 1 else 0)
      by_cases hjk : j.val = i.val
      · have h1 : j = ⟨i.val, h⟩ := Fin.eq_of_val_eq hjk
        have h2 : (⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ : Fin (n + 1)) = i :=
          Fin.eq_of_val_eq hjk
        rw [if_pos h1, if_pos h2]
        exact Nat.le_refl _
      · have h1 : j ≠ ⟨i.val, h⟩ := fun heq => hjk (congrArg Fin.val heq)
        rw [if_neg h1]
        exact Nat.zero_le _
    · simp only [h, dite_false]
      show (0 : Nat) ≤ _
      exact Nat.zero_le _
  | add p q ihp ihq =>
    show Nat.max (degreeY j (dropLastY p)) (degreeY j (dropLastY q))
       ≤ Nat.max (degreeY ⟨j.val, _⟩ p) (degreeY ⟨j.val, _⟩ q)
    apply Nat.max_le.mpr
    refine ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
            Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | sub p q ihp ihq =>
    show Nat.max (degreeY j (dropLastY p)) (degreeY j (dropLastY q))
       ≤ Nat.max (degreeY ⟨j.val, _⟩ p) (degreeY ⟨j.val, _⟩ q)
    apply Nat.max_le.mpr
    refine ⟨Nat.le_trans ihp (Nat.le_max_left _ _),
            Nat.le_trans ihq (Nat.le_max_right _ _)⟩
  | mul p q ihp ihq =>
    show degreeY j (dropLastY p) + degreeY j (dropLastY q)
       ≤ degreeY ⟨j.val, _⟩ p + degreeY ⟨j.val, _⟩ q
    exact Nat.add_le_add ihp ihq

/-! ### HasDerivAt correctness for dX (partial derivative in x)

For a fixed environment `env`, the function `fun y => eval p y env` is
a univariate polynomial in `y` with constants drawn from `env`. Its
derivative at `x` equals `eval (dX p) x env`.

This is the LOAD-BEARING univariate piece of the constructive
Khovanskii Item 2. The full TOTAL derivative (where y_i are themselves
functions of x via the chain) builds on this by adding the chain
contributions; that remains as future work since it requires
formalizing multi-variable HasDerivAt machinery that MachLib does not
yet have. -/
theorem multiPolyHasDerivAt_eval_dX {n : Nat} (p : MultiPoly n)
    (env : Fin n → Real) (x : Real) :
    HasDerivAt (fun y => eval p y env) (eval (dX p) x env) x := by
  induction p with
  | const c =>
    -- eval (const c) y env = c, dX (const c) = const 0, eval = 0.
    show HasDerivAt (fun _ => c) 0 x
    exact HasDerivAt_const c x
  | varX =>
    -- eval varX y env = y, dX varX = const 1, eval = 1.
    show HasDerivAt (fun y => y) 1 x
    exact HasDerivAt_id x
  | varY j =>
    -- eval (varY j) y env = env j (constant), dX = const 0, eval = 0.
    show HasDerivAt (fun _ => env j) 0 x
    exact HasDerivAt_const (env j) x
  | add p q ihp ihq =>
    -- eval (add p q) y env = eval p y env + eval q y env.
    -- dX (add p q) = add (dX p) (dX q).
    -- HasDerivAt_add applied to IH for p and q.
    show HasDerivAt (fun y => eval p y env + eval q y env)
                    (eval (dX p) x env + eval (dX q) x env) x
    exact HasDerivAt_add _ _ _ _ x ihp ihq
  | sub p q ihp ihq =>
    show HasDerivAt (fun y => eval p y env - eval q y env)
                    (eval (dX p) x env - eval (dX q) x env) x
    exact HasDerivAt_sub _ _ _ _ x ihp ihq
  | mul p q ihp ihq =>
    -- eval (mul p q) y env = eval p y env * eval q y env.
    -- dX (mul p q) = add (mul (dX p) q) (mul p (dX q)).
    -- eval = (eval (dX p) x env) * (eval q x env)
    --      + (eval p x env) * (eval (dX q) x env).
    show HasDerivAt (fun y => eval p y env * eval q y env)
                    (eval (dX p) x env * eval q x env
                     + eval p x env * eval (dX q) x env) x
    exact HasDerivAt_mul _ _ _ _ x ihp ihq

/-! ### HasDerivAt correctness for dY (partial derivative in y_i)

Symmetric to `multiPolyHasDerivAt_eval_dX`. Holds x and other y_j
constant; differentiates with respect to the i-th chain variable
treated as a univariate variable. -/
theorem multiPolyHasDerivAt_eval_dY {n : Nat} (i : Fin n) (p : MultiPoly n)
    (env : Fin n → Real) (x : Real) (yi₀ : Real) :
    HasDerivAt (fun yi => eval p x (updateEnv env i yi))
               (eval (dY i p) x (updateEnv env i yi₀))
               yi₀ := by
  induction p with
  | const c =>
    -- eval (const c) x (updateEnv env i yi) = c, dY = const 0.
    show HasDerivAt (fun _ => c) 0 yi₀
    exact HasDerivAt_const c yi₀
  | varX =>
    -- eval varX x (updateEnv env i yi) = x for all yi.
    show HasDerivAt (fun _ => x) 0 yi₀
    exact HasDerivAt_const x yi₀
  | varY j =>
    by_cases h : i = j
    · -- i = j: function is fun yi => (updateEnv env i yi) i = yi.
      -- dY i (varY i) = const 1, eval = 1.
      subst h
      -- Rewrite the function and derivative using updateEnv and dY definitions.
      have hupd : ∀ yi, (updateEnv env i yi) i = yi := by
        intro yi
        show (if i = i then yi else env i) = yi
        simp
      have hfun : (fun yi => eval (varY i) x (updateEnv env i yi))
                = (fun yi => yi) := by
        funext yi
        show (updateEnv env i yi) i = yi
        exact hupd yi
      have hdY : eval (dY i (varY i)) x (updateEnv env i yi₀) = 1 := by
        show eval (if i = i then const 1 else const 0) x (updateEnv env i yi₀) = 1
        simp only [if_true]
        rfl
      rw [hfun, hdY]
      exact HasDerivAt_id yi₀
    · -- i ≠ j: function is constant env j.
      -- dY i (varY j) = const 0, eval = 0.
      have hupd : ∀ yi, (updateEnv env i yi) j = env j := by
        intro yi
        show (if i = j then yi else env j) = env j
        simp [h]
      have hfun : (fun yi => eval (varY j) x (updateEnv env i yi))
                = (fun _ => env j) := by
        funext yi
        show (updateEnv env i yi) j = env j
        exact hupd yi
      have hdY : eval (dY i (varY j)) x (updateEnv env i yi₀) = 0 := by
        show eval (if i = j then const 1 else const 0) x (updateEnv env i yi₀) = 0
        simp [h]
        rfl
      rw [hfun, hdY]
      exact HasDerivAt_const (env j) yi₀
  | add p q ihp ihq =>
    show HasDerivAt
      (fun yi => eval p x (updateEnv env i yi) + eval q x (updateEnv env i yi))
      (eval (dY i p) x (updateEnv env i yi₀)
       + eval (dY i q) x (updateEnv env i yi₀)) yi₀
    exact HasDerivAt_add _ _ _ _ yi₀ ihp ihq
  | sub p q ihp ihq =>
    show HasDerivAt
      (fun yi => eval p x (updateEnv env i yi) - eval q x (updateEnv env i yi))
      (eval (dY i p) x (updateEnv env i yi₀)
       - eval (dY i q) x (updateEnv env i yi₀)) yi₀
    exact HasDerivAt_sub _ _ _ _ yi₀ ihp ihq
  | mul p q ihp ihq =>
    show HasDerivAt
      (fun yi => eval p x (updateEnv env i yi) * eval q x (updateEnv env i yi))
      (eval (dY i p) x (updateEnv env i yi₀) * eval q x (updateEnv env i yi₀)
       + eval p x (updateEnv env i yi₀) * eval (dY i q) x (updateEnv env i yi₀))
      yi₀
    exact HasDerivAt_mul _ _ _ _ yi₀ ihp ihq

/-! ### Chain-projection: substY eliminates y_i when q doesn't contain y_i

The Khovanskii chain-step reduction substitutes the chain relation
for the HIGHEST chain variable y_{n-1}. For a triangular chain, that
relation has `degreeY (n-1) = 0` (the highest variable's relation
doesn't depend on itself). After substitution, the resulting
polynomial has `degreeY (n-1) = 0` everywhere — i.e., y_{n-1} has
been eliminated.

This is the **load-bearing degree-projection lemma** for the chain-
length-induction step of Khovanskii's proof. -/
theorem degreeY_substY_eliminates {n : Nat} (i : Fin n) (q : MultiPoly n)
    (hq : degreeY i q = 0) (p : MultiPoly n) :
    degreeY i (substY i q p) = 0 := by
  induction p with
  | const c =>
    show degreeY i (const c) = 0
    rfl
  | varX =>
    show degreeY i (varX (n := n)) = 0
    rfl
  | varY j =>
    show degreeY i (if i = j then q else varY j) = 0
    by_cases h : i = j
    · -- i = j: result is q. degreeY i q = 0 by hypothesis.
      subst h
      simp
      exact hq
    · -- i ≠ j: result is varY j. degreeY i (varY j) = 0 since i ≠ j.
      simp [h]
      show degreeY i (varY j) = 0
      simp [degreeY, h]
  | add p1 p2 ih1 ih2 =>
    show Nat.max (degreeY i (substY i q p1)) (degreeY i (substY i q p2)) = 0
    rw [ih1, ih2]
    rfl
  | sub p1 p2 ih1 ih2 =>
    show Nat.max (degreeY i (substY i q p1)) (degreeY i (substY i q p2)) = 0
    rw [ih1, ih2]
    rfl
  | mul p1 p2 ih1 ih2 =>
    show degreeY i (substY i q p1) + degreeY i (substY i q p2) = 0
    rw [ih1, ih2]

open Classical in
/-- `true` if the polynomial is the literal `const 0`. -/
noncomputable def multiIsZeroConst {n : Nat} : MultiPoly n → Bool
  | const c => if c = 0 then true else false
  | _ => false

open Classical in
/-- `true` if the polynomial is the literal `const 1`. -/
noncomputable def multiIsOneConst {n : Nat} : MultiPoly n → Bool
  | const c => if c = 1 then true else false
  | _ => false

open Classical in
/-- Multivariate polynomial normalization. Collapses identity factors
and additive zeros (analogous to `polySimplify`). -/
noncomputable def multiSimplify {n : Nat} : MultiPoly n → MultiPoly n
  | const c => const c
  | varX    => varX
  | varY i  => varY i
  | add p q =>
    let p' := multiSimplify p
    let q' := multiSimplify q
    if multiIsZeroConst p' then q'
    else if multiIsZeroConst q' then p'
    else add p' q'
  | sub p q =>
    let p' := multiSimplify p
    let q' := multiSimplify q
    if multiIsZeroConst q' then p'
    else sub p' q'
  | mul p q =>
    let p' := multiSimplify p
    let q' := multiSimplify q
    if multiIsZeroConst p' then const 0
    else if multiIsZeroConst q' then const 0
    else if multiIsOneConst p' then q'
    else if multiIsOneConst q' then p'
    else mul p' q'

/-- `multiIsZeroConst p = true ⇒ p evaluates to 0`. -/
theorem multiIsZeroConst_eval {n : Nat} (p : MultiPoly n)
    (h : multiIsZeroConst p = true) (x : Real) (env : Fin n → Real) :
    eval p x env = 0 := by
  cases p with
  | const c =>
    unfold multiIsZeroConst at h
    by_cases hc : c = 0
    · rw [hc]; rfl
    · simp [hc] at h
  | varX => unfold multiIsZeroConst at h; simp at h
  | varY _ => unfold multiIsZeroConst at h; simp at h
  | add _ _ => unfold multiIsZeroConst at h; simp at h
  | sub _ _ => unfold multiIsZeroConst at h; simp at h
  | mul _ _ => unfold multiIsZeroConst at h; simp at h

/-- `multiIsOneConst p = true ⇒ p evaluates to 1`. -/
theorem multiIsOneConst_eval {n : Nat} (p : MultiPoly n)
    (h : multiIsOneConst p = true) (x : Real) (env : Fin n → Real) :
    eval p x env = 1 := by
  cases p with
  | const c =>
    unfold multiIsOneConst at h
    by_cases hc : c = 1
    · rw [hc]; rfl
    · simp [hc] at h
  | varX => unfold multiIsOneConst at h; simp at h
  | varY _ => unfold multiIsOneConst at h; simp at h
  | add _ _ => unfold multiIsOneConst at h; simp at h
  | sub _ _ => unfold multiIsOneConst at h; simp at h
  | mul _ _ => unfold multiIsOneConst at h; simp at h

/-- **`multiSimplify` preserves evaluation.** Analogue of `polySimplify_eval`. -/
theorem multiSimplify_eval {n : Nat} (p : MultiPoly n) (x : Real)
    (env : Fin n → Real) :
    eval (multiSimplify p) x env = eval p x env := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i => rfl
  | add p q ihp ihq =>
    unfold multiSimplify
    by_cases hp : multiIsZeroConst (multiSimplify p) = true
    · rw [if_pos hp]
      have hp_eval : eval (multiSimplify p) x env = 0 :=
        multiIsZeroConst_eval (multiSimplify p) hp x env
      show eval (multiSimplify q) x env = eval p x env + eval q x env
      rw [ihq, ← ihp, hp_eval, zero_add]
    · rw [if_neg hp]
      by_cases hq : multiIsZeroConst (multiSimplify q) = true
      · rw [if_pos hq]
        have hq_eval : eval (multiSimplify q) x env = 0 :=
          multiIsZeroConst_eval (multiSimplify q) hq x env
        show eval (multiSimplify p) x env = eval p x env + eval q x env
        rw [ihp, ← ihq, hq_eval, add_zero]
      · rw [if_neg hq]
        show eval (multiSimplify p) x env + eval (multiSimplify q) x env
           = eval p x env + eval q x env
        rw [ihp, ihq]
  | sub p q ihp ihq =>
    unfold multiSimplify
    by_cases hq : multiIsZeroConst (multiSimplify q) = true
    · rw [if_pos hq]
      have hq_eval : eval (multiSimplify q) x env = 0 :=
        multiIsZeroConst_eval (multiSimplify q) hq x env
      show eval (multiSimplify p) x env = eval p x env - eval q x env
      rw [ihp, ← ihq, hq_eval, sub_zero]
    · rw [if_neg hq]
      show eval (multiSimplify p) x env - eval (multiSimplify q) x env
         = eval p x env - eval q x env
      rw [ihp, ihq]
  | mul p q ihp ihq =>
    unfold multiSimplify
    by_cases hp : multiIsZeroConst (multiSimplify p) = true
    · rw [if_pos hp]
      have hp_eval : eval (multiSimplify p) x env = 0 :=
        multiIsZeroConst_eval (multiSimplify p) hp x env
      show eval (const 0 : MultiPoly n) x env = eval p x env * eval q x env
      show (0 : Real) = eval p x env * eval q x env
      rw [← ihp, hp_eval, zero_mul]
    · rw [if_neg hp]
      by_cases hq : multiIsZeroConst (multiSimplify q) = true
      · rw [if_pos hq]
        have hq_eval : eval (multiSimplify q) x env = 0 :=
          multiIsZeroConst_eval (multiSimplify q) hq x env
        show eval (const 0 : MultiPoly n) x env = eval p x env * eval q x env
        show (0 : Real) = eval p x env * eval q x env
        rw [← ihq, hq_eval, mul_zero]
      · rw [if_neg hq]
        by_cases hp1 : multiIsOneConst (multiSimplify p) = true
        · rw [if_pos hp1]
          have hp1_eval : eval (multiSimplify p) x env = 1 :=
            multiIsOneConst_eval (multiSimplify p) hp1 x env
          show eval (multiSimplify q) x env = eval p x env * eval q x env
          rw [ihq, ← ihp, hp1_eval, one_mul_thm]
        · rw [if_neg hp1]
          by_cases hq1 : multiIsOneConst (multiSimplify q) = true
          · rw [if_pos hq1]
            have hq1_eval : eval (multiSimplify q) x env = 1 :=
              multiIsOneConst_eval (multiSimplify q) hq1 x env
            show eval (multiSimplify p) x env = eval p x env * eval q x env
            rw [ihp, ← ihq, hq1_eval, mul_one_ax]
          · rw [if_neg hq1]
            show eval (multiSimplify p) x env * eval (multiSimplify q) x env
               = eval p x env * eval q x env
            rw [ihp, ihq]

/-! ## Chain-extension lifts

For phase 3 of the `derivative_rank_lt` refactor: when combining two
`PfaffianFn` values with chains of length `n` and `k`, we need to
lift each one's polynomial to a polynomial over the combined chain
of length `n + k`. -/

/-- Lift a `MultiPoly n` to a `MultiPoly (n + k)` by reinterpreting each
`varY i` as `varY ⟨i.val, _⟩` in the extended chain (i.e., the lift
puts the original chain variables at the BEGINNING of the new chain). -/
def liftLeft {n : Nat} (k : Nat) : MultiPoly n → MultiPoly (n + k)
  | const c   => const c
  | varX      => varX
  | varY i    => varY ⟨i.val, by
      have := i.isLt; omega⟩
  | add p q   => add (liftLeft k p) (liftLeft k q)
  | sub p q   => sub (liftLeft k p) (liftLeft k q)
  | mul p q   => mul (liftLeft k p) (liftLeft k q)

/-- Lift a `MultiPoly k` to a `MultiPoly (n + k)` by reinterpreting each
`varY j` as `varY ⟨n + j.val, _⟩` (the lift puts the original chain
variables at the END of the new chain, after `n` slots). -/
def liftRight (n : Nat) {k : Nat} : MultiPoly k → MultiPoly (n + k)
  | const c   => const c
  | varX      => varX
  | varY j    => varY ⟨n + j.val, by
      have := j.isLt; omega⟩
  | add p q   => add (liftRight n p) (liftRight n q)
  | sub p q   => sub (liftRight n p) (liftRight n q)
  | mul p q   => mul (liftRight n p) (liftRight n q)

/-- Lift preserves evaluation when the env's first `n` slots match
the original env. -/
theorem liftLeft_eval {n k : Nat} (p : MultiPoly n) (x : Real)
    (envOrig : Fin n → Real) (envExt : Fin (n + k) → Real)
    (h : ∀ i : Fin n, envExt ⟨i.val, by have := i.isLt; omega⟩ = envOrig i) :
    eval (liftLeft k p) x envExt = eval p x envOrig := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY i =>
    show envExt ⟨i.val, _⟩ = envOrig i
    exact h i
  | add p q ihp ihq =>
    show eval (liftLeft k p) x envExt + eval (liftLeft k q) x envExt
       = eval p x envOrig + eval q x envOrig
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show eval (liftLeft k p) x envExt - eval (liftLeft k q) x envExt
       = eval p x envOrig - eval q x envOrig
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show eval (liftLeft k p) x envExt * eval (liftLeft k q) x envExt
       = eval p x envOrig * eval q x envOrig
    rw [ihp, ihq]

/-- Lift preserves evaluation when the env's last `k` slots match
the original env. -/
theorem liftRight_eval (n : Nat) {k : Nat} (p : MultiPoly k) (x : Real)
    (envOrig : Fin k → Real) (envExt : Fin (n + k) → Real)
    (h : ∀ j : Fin k, envExt ⟨n + j.val, by have := j.isLt; omega⟩ = envOrig j) :
    eval (liftRight n p) x envExt = eval p x envOrig := by
  induction p with
  | const c => rfl
  | varX => rfl
  | varY j =>
    show envExt ⟨n + j.val, _⟩ = envOrig j
    exact h j
  | add p q ihp ihq =>
    show eval (liftRight n p) x envExt + eval (liftRight n q) x envExt
       = eval p x envOrig + eval q x envOrig
    rw [ihp, ihq]
  | sub p q ihp ihq =>
    show eval (liftRight n p) x envExt - eval (liftRight n q) x envExt
       = eval p x envOrig - eval q x envOrig
    rw [ihp, ihq]
  | mul p q ihp ihq =>
    show eval (liftRight n p) x envExt * eval (liftRight n q) x envExt
       = eval p x envOrig * eval q x envOrig
    rw [ihp, ihq]

end MultiPoly
end MultiPolyMod
end MachLib
