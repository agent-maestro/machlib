import MachLib.MultiPoly
import MachLib.Differentiation

/-!
# MachLib.PfaffianChain — chain-explicit Pfaffian functions

This module is the **phase-2 infrastructure** for the
`derivative_rank_lt` closure refactor (see
`machlib/DERIVATIVE_RANK_LT_REFACTOR_PLAN.md`).

It defines:

- `PfaffianChain n`: a sequence of `n` chain variables `y_1, ..., y_n`
  with relations `y_i' = P_i(x, y_1, ..., y_i)`, plus the actual
  real-valued functions that realize each `y_i`.
- `PfaffianFn`: a polynomial in `(x, y_1, ..., y_n)` for some chain.
  Its `eval` substitutes the chain's functions for the y's.
- `IsCoherentAt`: the proposition that the chain's `evals` actually
  satisfy their relations as derivatives at a point.
- `IsTriangular`: the classical Khovanskii constraint — `P_i` depends
  only on `(x, y_1, ..., y_i)`, not on `y_j` for `j > i`.

Phase 3 will provide a conversion from `PfaffianExpr` (in
`Pfaffian.lean`) to `PfaffianFn`, so the existing eml_pfaffian
construction lifts.

Phase 4 is the payoff: a new bound proof via chain-length induction
on `PfaffianChain.n`, replacing the broken rank-on-derivative induction
in `KhovanskiiLemma.lean`. After phase 4 lands, `derivative_rank_lt`
can be removed.

Zero Mathlib dependency. -/

namespace MachLib
namespace PfaffianChainMod

open MachLib.Real
open MachLib.MultiPolyMod

/-! ## PfaffianChain

A chain of length `n` consists of `n` real-valued functions
`y_1, ..., y_n` together with polynomial relations expressing each
derivative. The chain is **classical Khovanskii-style** when:
1. Each `relations i : MultiPoly n` is the polynomial `P_i`.
2. Each `evals i : Real → Real` is the function `y_i`.
3. The chain is *coherent*: `y_i' = P_i(x, y_1, ..., y_n)` everywhere
   the construction is valid.
4. The chain is *triangular*: `P_i` does not depend on `y_j` for `j > i`.

Conditions (3) and (4) are propositions (see `IsCoherentAt`,
`IsTriangular` below); the structure itself just bundles the data. -/
structure PfaffianChain (n : Nat) where
  evals     : Fin n → (Real → Real)
  relations : Fin n → MultiPoly n

namespace PfaffianChain

/-- The vector `(y_1(x), ..., y_n(x))` at a real point. -/
noncomputable def chainValues {n : Nat} (c : PfaffianChain n) (x : Real) :
    Fin n → Real := fun i => c.evals i x

/-- Coherence at a point: each `y_i` has the derivative its relation
specifies. -/
def IsCoherentAt {n : Nat} (c : PfaffianChain n) (x : Real) : Prop :=
  ∀ i : Fin n,
    HasDerivAt (c.evals i)
      (MultiPoly.eval (c.relations i) x (c.chainValues x)) x

/-- Triangularity: `P_i` is independent of `y_j` for `j > i`. -/
def IsTriangular {n : Nat} (c : PfaffianChain n) : Prop :=
  ∀ i j : Fin n, j.val > i.val →
    MultiPoly.degreeY j (c.relations i) = 0

/-- Coherence on an interval: coherent at every interior point. -/
def IsCoherentOn {n : Nat} (c : PfaffianChain n) (a b : Real) : Prop :=
  ∀ x : Real, a < x → x < b → IsCoherentAt c x

end PfaffianChain

/-! ## PfaffianFn — a polynomial in (x, y_1, ..., y_n) over a chain -/

/-- A **Pfaffian function** is a polynomial in `(x, y_1, ..., y_n)`
for some chain of length `n`. -/
structure PfaffianFn where
  n     : Nat
  chain : PfaffianChain n
  poly  : MultiPoly n

namespace PfaffianFn

/-- Real-valued evaluation: substitute `x` for the x-variable and
each `chain.evals i x` for the `y_i`-variable. -/
noncomputable def eval (f : PfaffianFn) (x : Real) : Real :=
  MultiPoly.eval f.poly x (f.chain.chainValues x)

/-- The chain length. Used as the induction measure in the
phase-4 bound proof. -/
def chainLength (f : PfaffianFn) : Nat := f.n

/-- The x-degree of the underlying polynomial. -/
def degreeX (f : PfaffianFn) : Nat :=
  MultiPoly.degreeX f.poly

/-- The total degree of the underlying polynomial. -/
def totalDegree (f : PfaffianFn) : Nat :=
  MultiPoly.totalDegree f.poly

/-- Normalize the underlying polynomial via `multiSimplify`. Preserves
`eval` (by `multiSimplify_eval`). -/
noncomputable def simplify (f : PfaffianFn) : PfaffianFn :=
  { n := f.n, chain := f.chain, poly := MultiPoly.multiSimplify f.poly }

/-- **Simplify preserves eval.** -/
theorem simplify_eval (f : PfaffianFn) (x : Real) :
    (simplify f).eval x = f.eval x := by
  show MultiPoly.eval (MultiPoly.multiSimplify f.poly)
        x (f.chain.chainValues x) =
       MultiPoly.eval f.poly x (f.chain.chainValues x)
  exact MultiPoly.multiSimplify_eval f.poly x (f.chain.chainValues x)

end PfaffianFn

end PfaffianChainMod
end MachLib
