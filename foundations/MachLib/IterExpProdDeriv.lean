import MachLib.IterExpChain

/-!
# Bound-free derivative of `iterExp` — `(iterExp n)' = ∏_{j≤n} iterExp j`

`HasDerivAt_iterExp` states the iterated-exponential derivative as `iteratedProd` over a `Fin N`, tying
it to a fixed chain depth `N`. For the ∀N Rolle vehicle (whose exponent sums levels across depths) that
`N`-coupling is a nuisance. This file re-derives the same fact **bound-free**: `prodExp x n` is the plain
product `iterExp 0 x · … · iterExp n x`, and `HasDerivAt (iterExp n) (prodExp x n) x` holds for *every*
`n` (chain rule + `exp`), with no depth bound. This is the analytic primitive the vehicle's `HasDerivAt`
is built from. No `sorry`.
-/

namespace MachLib.IterExpChainMod

open MachLib.Real

/-- The product `iterExp 0 x · iterExp 1 x · … · iterExp n x` — the value of `(iterExp n)'(x)`. -/
noncomputable def prodExp (x : Real) : Nat → Real
  | 0 => iterExp 0 x
  | k + 1 => prodExp x k * iterExp (k + 1) x

/-- **The bound-free derivative identity for the iterated exponential.** For every `n`,
`(iterExp n)'(x) = prodExp x n`. Base: `iterExp 0 = exp`. Step: `iterExp (n+1) = exp ∘ iterExp n`, so by
the chain rule its derivative is `exp(iterExp n x) · prodExp x n = iterExp (n+1) x · prodExp x n =
prodExp x (n+1)`. -/
theorem HasDerivAt_iterExp_prodExp (n : Nat) (x : Real) :
    HasDerivAt (iterExp n) (prodExp x n) x := by
  induction n with
  | zero =>
      show HasDerivAt (iterExp 0) (iterExp 0 x) x
      exact HasDerivAt_exp x
  | succ n ih =>
      have hcomp := HasDerivAt_comp Real.exp (iterExp n) (prodExp x n)
        (Real.exp (iterExp n x)) x ih (HasDerivAt_exp (iterExp n x))
      have hval : prodExp x (n + 1) = Real.exp (iterExp n x) * prodExp x n := by
        show prodExp x n * iterExp (n + 1) x = Real.exp (iterExp n x) * prodExp x n
        show prodExp x n * Real.exp (iterExp n x) = Real.exp (iterExp n x) * prodExp x n
        rw [mul_comm]
      show HasDerivAt (iterExp (n + 1)) (prodExp x (n + 1)) x
      rw [hval]
      exact hcomp

end MachLib.IterExpChainMod
