import MachLib.Ring

/-!
# MachLib.MultiVar — polynomials in `k` INDEPENDENT real variables (multivariate Khovanskii, Gate 2d)

The single-variable Khovanskii/Pfaffian stack (`MultiPoly n`, `pfaffianChainFn`) counts zeros of ONE
function of ONE real variable `z` — `n` there is the *chain order* (how many auxiliary functions
`fᵢ(z)`), NOT a number of variables (see `roadmap/pfaffian-general-explicit-bound-design.md §0`).

`MultiVar k` is the genuinely-multivariate object the *system* (multi-modulus) bound needs: a polynomial
in `k` **independent** real variables `x₀,…,x_{k-1}`, evaluated at an environment `env : Fin k → Real`.
No distinguished `x`/`env` split, no chain variables — every variable is a first-class independent real.

This is Rung 0 of the Gate-2d ladder (`roadmap/multivariate-khovanskii-gate2d-scoping.md`): the
structural decision "how to represent several independent variables in the axiomatic `MachLib.Real`,
Mathlib-free." **Zero Mathlib dependency**, matching the rest of `machlib`.

Layer A (this file): the type, `eval`, formal degrees (`totalDegree`, `degVar`), derived constructors,
and the eval-homomorphism + degree-arithmetic sanity lemmas the counting layer will consume.
-/

namespace MachLib
namespace MultiVarMod

open MachLib.Real

/-- AST for a polynomial in `k` independent real variables `x₀,…,x_{k-1}`, over `Real`. The variables
are indexed by `Fin k`; unlike `MultiPoly`, there is no distinguished `x` — every `var i` is an
independent real. -/
inductive MultiVar (k : Nat) : Type where
  | const : Real → MultiVar k
  | var   : Fin k → MultiVar k
  | add   : MultiVar k → MultiVar k → MultiVar k
  | sub   : MultiVar k → MultiVar k → MultiVar k
  | mul   : MultiVar k → MultiVar k → MultiVar k

namespace MultiVar

/-! ## Evaluation -/

/-- Evaluate a `MultiVar k` at an environment `env : Fin k → Real`. -/
noncomputable def eval {k : Nat} : MultiVar k → (Fin k → Real) → Real
  | const c, _   => c
  | var i,   env => env i
  | add p q, env => eval p env + eval q env
  | sub p q, env => eval p env - eval q env
  | mul p q, env => eval p env * eval q env

@[simp] theorem eval_const {k : Nat} (c : Real) (env : Fin k → Real) :
    eval (const c) env = c := rfl
@[simp] theorem eval_var {k : Nat} (i : Fin k) (env : Fin k → Real) :
    eval (var i) env = env i := rfl
@[simp] theorem eval_add {k : Nat} (p q : MultiVar k) (env : Fin k → Real) :
    eval (add p q) env = eval p env + eval q env := rfl
@[simp] theorem eval_sub {k : Nat} (p q : MultiVar k) (env : Fin k → Real) :
    eval (sub p q) env = eval p env - eval q env := rfl
@[simp] theorem eval_mul {k : Nat} (p q : MultiVar k) (env : Fin k → Real) :
    eval (mul p q) env = eval p env * eval q env := rfl

/-! ## Derived constructors -/

/-- The zero polynomial. -/
noncomputable def zero {k : Nat} : MultiVar k := const 0
/-- The one polynomial. -/
noncomputable def one {k : Nat} : MultiVar k := const 1
/-- Negation `-p = 0 - p`. -/
noncomputable def neg {k : Nat} (p : MultiVar k) : MultiVar k := sub zero p
/-- Repeated multiplication; `pow p 0 = one`. -/
noncomputable def pow {k : Nat} (p : MultiVar k) : Nat → MultiVar k
  | 0     => one
  | n + 1 => mul (pow p n) p

@[simp] theorem eval_zero {k : Nat} (env : Fin k → Real) : eval (zero : MultiVar k) env = 0 := rfl
@[simp] theorem eval_one {k : Nat} (env : Fin k → Real) : eval (one : MultiVar k) env = 1 := rfl

/-! ## Formal degrees

`totalDegree` and `degVar i` are the *formal* (syntactic) degrees — over-estimates of the true degree
(e.g. `x·0` has formal `totalDegree 1`), exactly as `MultiPoly.degreeX`/`degreeY` are. An over-estimate
is what a zero-count *upper* bound wants. `mul ↦ +`, `add`/`sub ↦ max`, matching the single-variable
convention. -/

/-- Formal total degree. -/
def totalDegree {k : Nat} : MultiVar k → Nat
  | const _ => 0
  | var _   => 1
  | add p q => Nat.max (totalDegree p) (totalDegree q)
  | sub p q => Nat.max (totalDegree p) (totalDegree q)
  | mul p q => totalDegree p + totalDegree q

/-- Formal degree in variable `i`. -/
def degVar {k : Nat} (i : Fin k) : MultiVar k → Nat
  | const _ => 0
  | var j   => if j = i then 1 else 0
  | add p q => Nat.max (degVar i p) (degVar i q)
  | sub p q => Nat.max (degVar i p) (degVar i q)
  | mul p q => degVar i p + degVar i q

/-- Each variable's degree is bounded by the total degree — the two formal degrees are consistent. -/
theorem degVar_le_totalDegree {k : Nat} (i : Fin k) :
    ∀ p : MultiVar k, degVar i p ≤ totalDegree p
  | const _ => Nat.le_refl 0
  | var j   => by
      show (if j = i then 1 else 0) ≤ 1
      by_cases h : j = i <;> simp [h]
  | add p q => by
      show Nat.max (degVar i p) (degVar i q) ≤ Nat.max (totalDegree p) (totalDegree q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (degVar_le_totalDegree i p) (Nat.le_max_left _ _),
        Nat.le_trans (degVar_le_totalDegree i q) (Nat.le_max_right _ _)⟩
  | sub p q => by
      show Nat.max (degVar i p) (degVar i q) ≤ Nat.max (totalDegree p) (totalDegree q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (degVar_le_totalDegree i p) (Nat.le_max_left _ _),
        Nat.le_trans (degVar_le_totalDegree i q) (Nat.le_max_right _ _)⟩
  | mul p q => by
      show degVar i p + degVar i q ≤ totalDegree p + totalDegree q
      exact Nat.add_le_add (degVar_le_totalDegree i p) (degVar_le_totalDegree i q)

@[simp] theorem totalDegree_mul {k : Nat} (p q : MultiVar k) :
    totalDegree (mul p q) = totalDegree p + totalDegree q := rfl
@[simp] theorem degVar_mul {k : Nat} (i : Fin k) (p q : MultiVar k) :
    degVar i (mul p q) = degVar i p + degVar i q := rfl

end MultiVar
end MultiVarMod
end MachLib
