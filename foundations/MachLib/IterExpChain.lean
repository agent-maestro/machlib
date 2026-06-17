import MachLib.PfaffianChain

/-!
# MachLib.IterExpChain — the non-degenerate iterated-exponential chain

This module defines `IterExpChain N : PfaffianChain N`, the canonical
**non-degenerate** Pfaffian chain where

    y_0 = exp(x)
    y_1 = exp(exp(x))
    y_2 = exp(exp(exp(x)))
    ...
    y_i = exp^{i+1}(x)        (the (i+1)-fold composition of exp)

Each chain value is a **different** function, in contrast to
`MultiExpChain N` where every `y_i = exp(x)` (degenerate; collapses to
chain length 1 via `MultiPoly.collapseMultiExp`).

The chain relations are products:

    y_i' = y_0 · y_1 · ... · y_i     (by chain rule on iterated exp)

which is triangular (`y_i'` depends only on `y_0, ..., y_i`) and
coherent (the relations hold at every x via the chain rule + induction).

This is the **target chain** for the constructive Khovanskii bound
beyond the trivial single-exp case. The bound itself is a separate
workstream (requires the parameterized SingleExp auto-bound, ~150
lines of mechanical work); this file ships only the chain definition
and its triangularity + coherence proofs.

Zero Mathlib dependency. -/

namespace MachLib
namespace IterExpChainMod

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod

/-! ## The iterated-exp function -/

/-- `iterExp n x = exp(exp(...(exp x)...))` with `(n+1)`-fold composition.
So `iterExp 0 = exp`, `iterExp 1 = exp ∘ exp`, etc. -/
noncomputable def iterExp : Nat → Real → Real
  | 0,     x => Real.exp x
  | n + 1, x => Real.exp (iterExp n x)

theorem iterExp_zero (x : Real) : iterExp 0 x = Real.exp x := rfl

theorem iterExp_succ (n : Nat) (x : Real) :
    iterExp (n + 1) x = Real.exp (iterExp n x) := rfl

/-! ## The relation polynomial — product of varY 0 ... varY k -/

/-- The polynomial `varY 0 * varY 1 * ... * varY k : MultiPoly N` for
`k < N`. Its eval at `(x, env)` is `env 0 * env 1 * ... * env k`. -/
noncomputable def prodVarYUpTo {N : Nat} : (k : Nat) → k < N → MultiPoly N
  | 0,     hk => MultiPoly.varY ⟨0, hk⟩
  | n + 1, hk =>
      MultiPoly.mul (prodVarYUpTo n (Nat.lt_of_succ_lt hk))
                    (MultiPoly.varY ⟨n + 1, hk⟩)

theorem prodVarYUpTo_zero {N : Nat} (hk : 0 < N) :
    (prodVarYUpTo 0 hk : MultiPoly N) = MultiPoly.varY ⟨0, hk⟩ := rfl

theorem prodVarYUpTo_succ {N : Nat} (n : Nat) (hk : n + 1 < N) :
    (prodVarYUpTo (n + 1) hk : MultiPoly N) =
    MultiPoly.mul (prodVarYUpTo n (Nat.lt_of_succ_lt hk))
                  (MultiPoly.varY ⟨n + 1, hk⟩) := rfl

/-! ## Eval correctness of the product polynomial -/

/-- `iteratedProd env k` = `env 0 * env 1 * ... * env k`. The natural
inhabitant of `Real` corresponding to `prodVarYUpTo k`'s eval. -/
noncomputable def iteratedProd {N : Nat} (env : Fin N → Real) :
    (k : Nat) → k < N → Real
  | 0,     hk => env ⟨0, hk⟩
  | n + 1, hk => iteratedProd env n (Nat.lt_of_succ_lt hk) * env ⟨n + 1, hk⟩

theorem eval_prodVarYUpTo {N : Nat} (k : Nat) (hk : k < N) (x : Real)
    (env : Fin N → Real) :
    MultiPoly.eval (prodVarYUpTo k hk) x env = iteratedProd env k hk := by
  induction k with
  | zero => rfl
  | succ n ih =>
    show MultiPoly.eval (prodVarYUpTo n (Nat.lt_of_succ_lt hk)) x env
       * MultiPoly.eval (MultiPoly.varY ⟨n + 1, hk⟩) x env
       = iteratedProd env n (Nat.lt_of_succ_lt hk) * env ⟨n + 1, hk⟩
    rw [ih (Nat.lt_of_succ_lt hk)]
    rfl

/-! ## HasDerivAt for iterExp

The key fact: `(iterExp n)'(x) = ∏_{j ≤ n} iterExp j x`. Proved by
induction using chain rule + commutativity of multiplication. -/

/-- **The derivative identity for iterated exp**: at every `x`,
`HasDerivAt (iterExp n) (iteratedProd (iterExp · x) n hk) x`, where
the chain values are `fun i : Fin N => iterExp i.val x`. -/
theorem HasDerivAt_iterExp {N : Nat} (n : Nat) (hk : n < N) (x : Real) :
    HasDerivAt (iterExp n)
      (iteratedProd (fun i : Fin N => iterExp i.val x) n hk) x := by
  induction n with
  | zero =>
    show HasDerivAt (iterExp 0) (iterExp 0 x) x
    exact HasDerivAt_exp x
  | succ m ih =>
    have hm : m < N := Nat.lt_of_succ_lt hk
    have ih' := ih hm
    -- iterExp (m+1) = fun y => exp (iterExp m y).
    -- Chain rule: derivative = exp'(iterExp m x) · (iterExp m)'(x)
    --           = exp(iterExp m x) · iteratedProd m
    --           = iterExp (m+1) x · iteratedProd m.
    have hcomp :
        HasDerivAt (fun y => Real.exp (iterExp m y))
          (Real.exp (iterExp m x)
            * iteratedProd (fun i : Fin N => iterExp i.val x) m hm) x := by
      have hexp : HasDerivAt Real.exp (Real.exp (iterExp m x)) (iterExp m x) :=
        HasDerivAt_exp (iterExp m x)
      exact HasDerivAt_comp Real.exp (iterExp m)
              (iteratedProd (fun i : Fin N => iterExp i.val x) m hm)
              (Real.exp (iterExp m x)) x ih' hexp
    -- Rearrange: exp(iterExp m x) = iterExp (m+1) x, and reorder the product.
    show HasDerivAt (iterExp (m + 1))
          (iteratedProd (fun i : Fin N => iterExp i.val x) (m + 1) hk) x
    have hgoal :
        iteratedProd (fun i : Fin N => iterExp i.val x) (m + 1) hk
        = Real.exp (iterExp m x)
        * iteratedProd (fun i : Fin N => iterExp i.val x) m hm := by
      show iteratedProd (fun i : Fin N => iterExp i.val x) m
              (Nat.lt_of_succ_lt hk)
            * iterExp (m + 1) x
          = Real.exp (iterExp m x)
            * iteratedProd (fun i : Fin N => iterExp i.val x) m hm
      show iteratedProd (fun i : Fin N => iterExp i.val x) m hm
            * iterExp (m + 1) x
          = Real.exp (iterExp m x)
            * iteratedProd (fun i : Fin N => iterExp i.val x) m hm
      rw [iterExp_succ, MachLib.Real.mul_comm]
    rw [hgoal]
    show HasDerivAt (iterExp (m + 1))
          (Real.exp (iterExp m x)
            * iteratedProd (fun i : Fin N => iterExp i.val x) m hm) x
    -- iterExp (m+1) = fun y => exp (iterExp m y).
    have hfn : iterExp (m + 1) = fun y => Real.exp (iterExp m y) := by
      funext y; rfl
    rw [hfn]
    exact hcomp

/-! ## The iterated-exp chain -/

/-- **The iterated-exp chain** of length `N`: `evals i = iterExp i.val`,
`relations i = prodVarYUpTo i.val i.isLt`. -/
noncomputable def IterExpChain (N : Nat) : PfaffianChain N :=
  { evals     := fun i => iterExp i.val
    relations := fun i => prodVarYUpTo i.val i.isLt }

theorem IterExpChain_evals (N : Nat) (i : Fin N) :
    (IterExpChain N).evals i = iterExp i.val := rfl

theorem IterExpChain_relations (N : Nat) (i : Fin N) :
    (IterExpChain N).relations i = prodVarYUpTo i.val i.isLt := rfl

theorem IterExpChain_chainValues (N : Nat) (x : Real) (i : Fin N) :
    (IterExpChain N).chainValues x i = iterExp i.val x := rfl

/-! ## Triangularity

`prodVarYUpTo k` only references `varY ⟨0, _⟩, ..., varY ⟨k, _⟩`, so
for `j > k` the degree in `y_j` is 0. Hence `IterExpChain` is triangular
(`P_i` depends only on `y_0, ..., y_i`). -/

theorem degreeY_prodVarYUpTo_zero_of_lt {N : Nat} (k : Nat) (hk : k < N)
    (j : Fin N) (hj : j.val > k) :
    MultiPoly.degreeY j (prodVarYUpTo k hk : MultiPoly N) = 0 := by
  induction k with
  | zero =>
    show MultiPoly.degreeY j (MultiPoly.varY ⟨0, hk⟩ : MultiPoly N) = 0
    show (if j = (⟨0, hk⟩ : Fin N) then 1 else 0) = 0
    have hj_ne : j ≠ (⟨0, hk⟩ : Fin N) := by
      intro h; rw [Fin.mk.injEq] at h; omega
    simp [hj_ne]
  | succ n ih =>
    -- prodVarYUpTo (n+1) = mul (prodVarYUpTo n) (varY ⟨n+1, _⟩).
    -- degreeY j (mul a b) = degreeY j a + degreeY j b.
    -- j.val > n+1 > n, so IH gives degreeY j (prodVarYUpTo n) = 0.
    -- j.val > n+1, so j ≠ ⟨n+1, _⟩, so degreeY j (varY ⟨n+1, _⟩) = 0.
    show MultiPoly.degreeY j
           (MultiPoly.mul (prodVarYUpTo n (Nat.lt_of_succ_lt hk))
                          (MultiPoly.varY ⟨n + 1, hk⟩)) = 0
    show MultiPoly.degreeY j (prodVarYUpTo n (Nat.lt_of_succ_lt hk))
       + MultiPoly.degreeY j (MultiPoly.varY ⟨n + 1, hk⟩) = 0
    have h1 := ih (Nat.lt_of_succ_lt hk) (by omega)
    have h_ne : j ≠ (⟨n + 1, hk⟩ : Fin N) := by
      intro h; rw [Fin.mk.injEq] at h; omega
    have h2 : MultiPoly.degreeY j (MultiPoly.varY ⟨n + 1, hk⟩ : MultiPoly N) = 0 := by
      show (if j = (⟨n + 1, hk⟩ : Fin N) then 1 else 0) = 0
      simp [h_ne]
    rw [h1, h2]

theorem IterExpChain_isTriangular (N : Nat) :
    (IterExpChain N).IsTriangular := by
  intro i j hij
  show MultiPoly.degreeY j (prodVarYUpTo i.val i.isLt : MultiPoly N) = 0
  exact degreeY_prodVarYUpTo_zero_of_lt i.val i.isLt j hij

/-! ## Coherence

At every `x`, each `(iterExp i.val)' = ∏_{j ≤ i.val} iterExp j x`,
which equals `MultiPoly.eval (prodVarYUpTo i.val) x (chainValues x)`.
Combined with `HasDerivAt_iterExp`, this gives coherence. -/

theorem IterExpChain_isCoherentAt (N : Nat) (x : Real) :
    (IterExpChain N).IsCoherentAt x := by
  intro i
  show HasDerivAt (iterExp i.val)
        (MultiPoly.eval (prodVarYUpTo i.val i.isLt)
          x ((IterExpChain N).chainValues x)) x
  rw [eval_prodVarYUpTo]
  -- chainValues x = fun j => iterExp j.val x.
  have heq : (IterExpChain N).chainValues x = (fun j : Fin N => iterExp j.val x) := by
    funext j; rfl
  rw [heq]
  exact HasDerivAt_iterExp i.val i.isLt x

theorem IterExpChain_isCoherentOn (N : Nat) (a b : Real) :
    (IterExpChain N).IsCoherentOn a b := by
  intro x _ _
  exact IterExpChain_isCoherentAt N x

end IterExpChainMod
end MachLib
