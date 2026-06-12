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

/-! ## Normalization — multiSimplify

Mirrors `PolynomialRootCount.polySimplify`'s single-variable pattern.
Eliminates phantom `0*x` and `1*x` terms so that formal degree
reflects effective degree. Crucial for proving strict degree decrease
under `dX` (which fails on the naive AST — see the discussion above). -/

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
