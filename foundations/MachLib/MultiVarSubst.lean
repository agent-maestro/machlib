import MachLib.MultiVar

/-!
# Variable restriction for `MultiVar k` — the fiber / elimination primitive (Gate 2d, Rung 0.5)

`substConst i c p` substitutes the independent variable `x_i` by the constant `c`, leaving a `MultiVar k`
that no longer depends on `x_i`. It is the **restrict-to-a-fiber** operation the multivariate count is
built on: fixing `x = x₀` in a `MultiVar 2` system `{p, q}` reduces the fiber `{y : p(x₀,y)=q(x₀,y)=0}`
to a *univariate* slice, whose root count feeds `bezout_skeleton`'s fiber bound `B`. It is equally the
primitive the resultant / elimination step evaluates against.

Proven here (Mathlib-free, sorry-free): the eval identity (`substConst` = evaluation at
`Function.update env i c`), the elimination fact (`degVar i` collapses to `0`), and degree monotonicity
(substituting a constant never raises a degree). These are exactly the facts the fiber-count reduction
consumes.
-/

namespace MachLib
namespace MultiVarMod

/-- Point-update of an environment: `x_i ↦ c`, all other coordinates unchanged. Hand-rolled because the
Mathlib-free core has no `Function.update`. -/
def substEnv {k : Nat} (env : Fin k → Real) (i : Fin k) (c : Real) : Fin k → Real :=
  fun j => if j = i then c else env j

theorem substEnv_self {k : Nat} (env : Fin k → Real) (i : Fin k) (c : Real) :
    substEnv env i c i = c := if_pos rfl
theorem substEnv_ne {k : Nat} (env : Fin k → Real) {i j : Fin k} (h : j ≠ i) (c : Real) :
    substEnv env i c j = env j := if_neg h

namespace MultiVar

/-- Substitute variable `x_i` by the constant `c`. The result is a `MultiVar k` independent of `x_i`. -/
def substConst {k : Nat} (i : Fin k) (c : Real) : MultiVar k → MultiVar k
  | const a => const a
  | var j   => if j = i then const c else var j
  | add p q => add (substConst i c p) (substConst i c q)
  | sub p q => sub (substConst i c p) (substConst i c q)
  | mul p q => mul (substConst i c p) (substConst i c q)

/-- **Eval identity.** Substituting `x_i := c` is evaluation at the updated environment `substEnv`. -/
theorem eval_substConst {k : Nat} (i : Fin k) (c : Real) :
    ∀ (p : MultiVar k) (env : Fin k → Real),
      eval (substConst i c p) env = eval p (substEnv env i c)
  | const a, env => rfl
  | var j,   env => by
      show eval (if j = i then const c else var j) env = substEnv env i c j
      by_cases h : j = i
      · rw [if_pos h, h]; exact (substEnv_self env i c).symm
      · rw [if_neg h]; exact (substEnv_ne env h c).symm
  | add p q, env => by
      show eval (substConst i c p) env + eval (substConst i c q) env = _ + _
      rw [eval_substConst i c p env, eval_substConst i c q env]
  | sub p q, env => by
      show eval (substConst i c p) env - eval (substConst i c q) env = _ - _
      rw [eval_substConst i c p env, eval_substConst i c q env]
  | mul p q, env => by
      show eval (substConst i c p) env * eval (substConst i c q) env = _ * _
      rw [eval_substConst i c p env, eval_substConst i c q env]

/-- **Elimination.** After substituting `x_i := c`, the formal degree in `x_i` collapses to `0` — the
variable is genuinely gone, so a `MultiVar 2` slice at `x = x₀` is a univariate polynomial in the other
variable. -/
theorem degVar_substConst_self {k : Nat} (i : Fin k) (c : Real) :
    ∀ p : MultiVar k, degVar i (substConst i c p) = 0
  | const _ => rfl
  | var j   => by
      show degVar i (if j = i then const c else var j) = 0
      by_cases h : j = i
      · rw [if_pos h]; rfl
      · rw [if_neg h]; show (if j = i then 1 else 0) = 0; rw [if_neg h]
  | add p q => by
      show Nat.max (degVar i (substConst i c p)) (degVar i (substConst i c q)) = 0
      rw [degVar_substConst_self i c p, degVar_substConst_self i c q]
      decide
  | sub p q => by
      show Nat.max (degVar i (substConst i c p)) (degVar i (substConst i c q)) = 0
      rw [degVar_substConst_self i c p, degVar_substConst_self i c q]
      decide
  | mul p q => by
      show degVar i (substConst i c p) + degVar i (substConst i c q) = 0
      rw [degVar_substConst_self i c p, degVar_substConst_self i c q]

/-- **Degree monotonicity.** Substituting a constant never raises the degree in any variable — so the
univariate slice's degree is `≤` the original, and Bezout's fiber bound `B ≈ deg` is inherited. -/
theorem degVar_substConst_le {k : Nat} (i : Fin k) (c : Real) (j : Fin k) :
    ∀ p : MultiVar k, degVar j (substConst i c p) ≤ degVar j p
  | const _ => Nat.le_refl 0
  | var l   => by
      show degVar j (if l = i then const c else var l) ≤ degVar j (var l)
      split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
  | add p q => by
      show Nat.max (degVar j (substConst i c p)) (degVar j (substConst i c q))
          ≤ Nat.max (degVar j p) (degVar j q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (degVar_substConst_le i c j p) (Nat.le_max_left _ _),
        Nat.le_trans (degVar_substConst_le i c j q) (Nat.le_max_right _ _)⟩
  | sub p q => by
      show Nat.max (degVar j (substConst i c p)) (degVar j (substConst i c q))
          ≤ Nat.max (degVar j p) (degVar j q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (degVar_substConst_le i c j p) (Nat.le_max_left _ _),
        Nat.le_trans (degVar_substConst_le i c j q) (Nat.le_max_right _ _)⟩
  | mul p q => by
      show degVar j (substConst i c p) + degVar j (substConst i c q) ≤ degVar j p + degVar j q
      exact Nat.add_le_add (degVar_substConst_le i c j p) (degVar_substConst_le i c j q)

/-- **Total-degree monotonicity** of the restriction. -/
theorem totalDegree_substConst_le {k : Nat} (i : Fin k) (c : Real) :
    ∀ p : MultiVar k, totalDegree (substConst i c p) ≤ totalDegree p
  | const _ => Nat.le_refl 0
  | var l   => by
      show totalDegree (if l = i then const c else var l) ≤ totalDegree (var l)
      split
      · exact Nat.zero_le _
      · exact Nat.le_refl _
  | add p q => by
      show Nat.max (totalDegree (substConst i c p)) (totalDegree (substConst i c q))
          ≤ Nat.max (totalDegree p) (totalDegree q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (totalDegree_substConst_le i c p) (Nat.le_max_left _ _),
        Nat.le_trans (totalDegree_substConst_le i c q) (Nat.le_max_right _ _)⟩
  | sub p q => by
      show Nat.max (totalDegree (substConst i c p)) (totalDegree (substConst i c q))
          ≤ Nat.max (totalDegree p) (totalDegree q)
      exact Nat.max_le.mpr ⟨Nat.le_trans (totalDegree_substConst_le i c p) (Nat.le_max_left _ _),
        Nat.le_trans (totalDegree_substConst_le i c q) (Nat.le_max_right _ _)⟩
  | mul p q => by
      show totalDegree (substConst i c p) + totalDegree (substConst i c q)
          ≤ totalDegree p + totalDegree q
      exact Nat.add_le_add (totalDegree_substConst_le i c p) (totalDegree_substConst_le i c q)

end MultiVar
end MultiVarMod
end MachLib
