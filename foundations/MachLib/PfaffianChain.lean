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

/-! ## Chain combinators (phase 3 infrastructure)

When combining two `PfaffianFn` values with chains of length `n` and
`k`, we need to lift each one's polynomial to the combined chain of
length `n + k`. -/

namespace PfaffianChain

/-- Append two chains: the result has length `n + k`. The first `n`
slots come from `c1`, the next `k` from `c2`. Relations get lifted
to the larger chain space. -/
noncomputable def append {n k : Nat} (c1 : PfaffianChain n)
    (c2 : PfaffianChain k) : PfaffianChain (n + k) :=
  { evals := fun i =>
      if h : i.val < n then c1.evals ⟨i.val, h⟩
      else c2.evals ⟨i.val - n, by have := i.isLt; omega⟩,
    relations := fun i =>
      if h : i.val < n then
        MultiPoly.liftLeft k (c1.relations ⟨i.val, h⟩)
      else
        MultiPoly.liftRight n (c2.relations ⟨i.val - n,
          by have := i.isLt; omega⟩) }

/-! ### Append correspondence lemmas (phase 3.5)

The `append` operation puts c1's chainValues in slots [0, n) and c2's
in slots [n, n+k). These lemmas express that correspondence — needed
by the `liftLeft_eval` / `liftRight_eval` hypotheses for combiners. -/

theorem append_chainValues_left {n k : Nat} (c1 : PfaffianChain n)
    (c2 : PfaffianChain k) (x : Real) (i : Fin n) :
    (c1.append c2).chainValues x ⟨i.val, by have := i.isLt; omega⟩ =
    c1.chainValues x i := by
  show (c1.append c2).evals ⟨i.val, _⟩ x = c1.evals i x
  show (if h : i.val < n then c1.evals ⟨i.val, h⟩
        else c2.evals ⟨i.val - n, _⟩) x = c1.evals i x
  have hlt : i.val < n := i.isLt
  rw [dif_pos hlt]

theorem append_chainValues_right {n k : Nat} (c1 : PfaffianChain n)
    (c2 : PfaffianChain k) (x : Real) (j : Fin k) :
    (c1.append c2).chainValues x ⟨n + j.val, by have := j.isLt; omega⟩ =
    c2.chainValues x j := by
  show (c1.append c2).evals ⟨n + j.val, _⟩ x = c2.evals j x
  show (if h : n + j.val < n then c1.evals ⟨n + j.val, h⟩
        else c2.evals ⟨n + j.val - n, _⟩) x = c2.evals j x
  have hnlt : ¬ (n + j.val < n) := by omega
  rw [dif_neg hnlt]
  -- The remaining goal is c2.evals on the shifted Fin equals c2.evals j x.
  -- Cast away the Fin difference by .val equality.
  have hval_eq : (⟨n + j.val - n, by omega⟩ : Fin k) = j := by
    apply Fin.eq_of_val_eq
    show n + j.val - n = j.val
    omega
  rw [hval_eq]

end PfaffianChain

/-! ## PfaffianFn smart constructors -/

namespace PfaffianFn

/-- The constant function `c`. Chain of length 0. -/
noncomputable def const (c : Real) : PfaffianFn :=
  { n := 0,
    chain := { evals := Fin.elim0, relations := Fin.elim0 },
    poly := MultiPoly.const c }

/-- The identity function `x`. Chain of length 0. -/
noncomputable def var : PfaffianFn :=
  { n := 0,
    chain := { evals := Fin.elim0, relations := Fin.elim0 },
    poly := MultiPoly.varX }

/-- The exponential function `exp(x)` as a PfaffianFn. Chain of
length 1: `y_1 = exp x`, relation `y_1' = y_1` (the defining
chain relation of exp). The polynomial is `varY 0`. -/
noncomputable def expFn : PfaffianFn :=
  { n := 1,
    chain := { evals := fun _ => Real.exp,
               relations := fun _ => MultiPoly.varY 0 },
    poly := MultiPoly.varY 0 }

/-! ### Eval sanity for the smart constructors -/

theorem eval_const (c : Real) (x : Real) :
    (const c).eval x = c := rfl

theorem eval_var (x : Real) : var.eval x = x := rfl

theorem eval_expFn (x : Real) : expFn.eval x = Real.exp x := rfl

/-! ### Chain-combining operations (phase 3.5)

`add`, `sub`, `mul` of two PfaffianFns: build a combined chain via
`append`, lift each polynomial to the combined chain space, and
combine via the corresponding MultiPoly op. -/

/-- Addition of Pfaffian functions: chain is `f.chain ++ g.chain`,
polynomial is `liftLeft f.poly + liftRight g.poly`. -/
noncomputable def add (f g : PfaffianFn) : PfaffianFn :=
  { n := f.n + g.n,
    chain := f.chain.append g.chain,
    poly := MultiPoly.add
              (MultiPoly.liftLeft g.n f.poly)
              (MultiPoly.liftRight f.n g.poly) }

/-- Subtraction. -/
noncomputable def sub (f g : PfaffianFn) : PfaffianFn :=
  { n := f.n + g.n,
    chain := f.chain.append g.chain,
    poly := MultiPoly.sub
              (MultiPoly.liftLeft g.n f.poly)
              (MultiPoly.liftRight f.n g.poly) }

/-- Multiplication. -/
noncomputable def mul (f g : PfaffianFn) : PfaffianFn :=
  { n := f.n + g.n,
    chain := f.chain.append g.chain,
    poly := MultiPoly.mul
              (MultiPoly.liftLeft g.n f.poly)
              (MultiPoly.liftRight f.n g.poly) }

/-! ### Eval correctness for combiners

Each combiner's eval reduces to the corresponding Real operation via
the `liftLeft_eval` / `liftRight_eval` lemmas, with the appended-chain
correspondence supplied by `append_chainValues_left/right`. -/

theorem eval_add (f g : PfaffianFn) (x : Real) :
    (f.add g).eval x = f.eval x + g.eval x := by
  show MultiPoly.eval
        (MultiPoly.add (MultiPoly.liftLeft g.n f.poly)
                        (MultiPoly.liftRight f.n g.poly))
        x ((f.chain.append g.chain).chainValues x)
    = MultiPoly.eval f.poly x (f.chain.chainValues x)
      + MultiPoly.eval g.poly x (g.chain.chainValues x)
  rw [MultiPoly.eval_add]
  congr 1
  · -- eval (liftLeft g.n f.poly) x appended = eval f.poly x f.chain.chainValues
    apply MultiPoly.liftLeft_eval
    intro i
    exact PfaffianChain.append_chainValues_left f.chain g.chain x i
  · apply MultiPoly.liftRight_eval
    intro j
    exact PfaffianChain.append_chainValues_right f.chain g.chain x j

theorem eval_sub (f g : PfaffianFn) (x : Real) :
    (f.sub g).eval x = f.eval x - g.eval x := by
  show MultiPoly.eval
        (MultiPoly.sub (MultiPoly.liftLeft g.n f.poly)
                        (MultiPoly.liftRight f.n g.poly))
        x ((f.chain.append g.chain).chainValues x)
    = MultiPoly.eval f.poly x (f.chain.chainValues x)
      - MultiPoly.eval g.poly x (g.chain.chainValues x)
  rw [MultiPoly.eval_sub]
  congr 1
  · apply MultiPoly.liftLeft_eval
    intro i
    exact PfaffianChain.append_chainValues_left f.chain g.chain x i
  · apply MultiPoly.liftRight_eval
    intro j
    exact PfaffianChain.append_chainValues_right f.chain g.chain x j

theorem eval_mul (f g : PfaffianFn) (x : Real) :
    (f.mul g).eval x = f.eval x * g.eval x := by
  show MultiPoly.eval
        (MultiPoly.mul (MultiPoly.liftLeft g.n f.poly)
                        (MultiPoly.liftRight f.n g.poly))
        x ((f.chain.append g.chain).chainValues x)
    = MultiPoly.eval f.poly x (f.chain.chainValues x)
      * MultiPoly.eval g.poly x (g.chain.chainValues x)
  rw [MultiPoly.eval_mul]
  congr 1
  · apply MultiPoly.liftLeft_eval
    intro i
    exact PfaffianChain.append_chainValues_left f.chain g.chain x i
  · apply MultiPoly.liftRight_eval
    intro j
    exact PfaffianChain.append_chainValues_right f.chain g.chain x j

end PfaffianFn

end PfaffianChainMod
end MachLib
