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

/-! ### Total derivative (constructive Khovanskii item 2, FRAMEWORK)

The total derivative of a PfaffianFn `f(x, y_1, ..., y_n)` treats it
as a function of x where y_i = y_i(x) are determined by the chain
relations:

  d/dx f = ∂f/∂x + Σ_{i=0..n-1} (∂f/∂y_i) · (chain.relations i)

The construction below assembles this polynomial. Eval correctness
(`HasDerivAt`-shaped theorem) is FUTURE WORK; it requires multi-
variable HasDerivAt machinery that MachLib does not have yet. See
`monogate-research/exploration/constructive_khovanskii_zero_bound_scoping_2026_06_13/`
for the closure path estimate.

The structural framework here is the load-bearing first step;
downstream consumers can use the polynomial-level structure even
before the HasDerivAt proof lands. -/

/-- Recursive accumulator: sum the chain-rule contribution from each
chain variable up to index `k`. Returns `dX poly + Σ_{i<k} (chain.relations i) * (dY i poly)`. -/
noncomputable def chainSumAux {n : Nat} (chain : PfaffianChain n)
    (poly : MultiPoly n) : Nat → MultiPoly n
  | 0 => MultiPoly.dX poly
  | k + 1 =>
    if h : k < n then
      MultiPoly.add
        (chainSumAux chain poly k)
        (MultiPoly.mul (chain.relations ⟨k, h⟩)
                       (MultiPoly.dY ⟨k, h⟩ poly))
    else
      chainSumAux chain poly k

/-- The total derivative as a PfaffianFn. Same chain (the y_i don't
change), updated polynomial via the chain rule. -/
noncomputable def totalDerivative (f : PfaffianFn) : PfaffianFn :=
  { n := f.n,
    chain := f.chain,
    poly := chainSumAux f.chain f.poly f.n }

/-- Trivial structural check: totalDerivative preserves chain length. -/
theorem totalDerivative_chainLength (f : PfaffianFn) :
    (totalDerivative f).chainLength = f.chainLength := rfl

/-- The base case of `chainSumAux`: at k = 0, it's just dX of the
polynomial. -/
theorem chainSumAux_zero {n : Nat} (chain : PfaffianChain n)
    (poly : MultiPoly n) :
    chainSumAux chain poly 0 = MultiPoly.dX poly := rfl

/-- For chain length 0 (no chain variables), `chainSumAux` at the
chain's index `n` is just `dX poly`. The full total derivative on
length-0 chains reduces to dX. -/
theorem chainSumAux_at_chainLength_zero (chain : PfaffianChain 0)
    (poly : MultiPoly 0) :
    chainSumAux chain poly 0 = MultiPoly.dX poly := rfl

/-- The recursive step of `chainSumAux`: adds the chain-rule
contribution for the next variable. -/
theorem chainSumAux_succ {n : Nat} (chain : PfaffianChain n)
    (poly : MultiPoly n) (k : Nat) (h : k < n) :
    chainSumAux chain poly (k + 1) =
    MultiPoly.add
      (chainSumAux chain poly k)
      (MultiPoly.mul (chain.relations ⟨k, h⟩)
                     (MultiPoly.dY ⟨k, h⟩ poly)) := by
  show (if h : k < n then _ else _) = _
  simp [h]

/-! ### Structural total derivative + HasDerivAt for arbitrary chain length

The `chainTotalDeriv` function is a STRUCTURAL recursion that computes
the total derivative of a MultiPoly with respect to x, given a chain.
Each varY i is replaced by the chain relation `chain.relations i`
(which is the derivative of the corresponding chain function), and
the operators distribute as expected.

The corresponding `multiPolyHasDerivAt_eval_with_chain` theorem
proves that this is indeed the derivative of `eval p y (chain.chainValues y)`
at x, given chain coherence. -/

/-- The structural total derivative of a MultiPoly, with each y_i
replaced by the chain relation (giving y_i'(x)). -/
noncomputable def chainTotalDeriv {n : Nat} (chain : PfaffianChain n) :
    MultiPoly n → MultiPoly n
  | .const _ => .const 0
  | .varX => .const 1
  | .varY i => chain.relations i
  | .add p q => .add (chainTotalDeriv chain p) (chainTotalDeriv chain q)
  | .sub p q => .sub (chainTotalDeriv chain p) (chainTotalDeriv chain q)
  | .mul p q => .add
      (.mul (chainTotalDeriv chain p) q)
      (.mul p (chainTotalDeriv chain q))

/-- **THE CHAIN-RULE THEOREM.** For a PfaffianChain coherent at x, the
function `fun y => eval p y (chain.chainValues y)` has HasDerivAt at x
with derivative `eval (chainTotalDeriv chain p) x (chain.chainValues x)`.

Constructive proof by structural induction on the MultiPoly AST:
  - const c: derivative is 0.
  - varX: derivative is 1.
  - varY i: derivative is chain.relations i (from chain coherence).
  - add/sub/mul: derived by HasDerivAt_add/sub/mul applied to IHs.

This is the CONSTRUCTIVE proof of the multi-variable chain rule
specialized to PfaffianFn evaluations. -/
theorem multiPolyHasDerivAt_eval_with_chain {n : Nat}
    (chain : PfaffianChain n) (p : MultiPoly n) (x : Real)
    (hcoherent : chain.IsCoherentAt x) :
    HasDerivAt (fun y => MultiPoly.eval p y (chain.chainValues y))
               (MultiPoly.eval (chainTotalDeriv chain p) x
                                (chain.chainValues x))
               x := by
  induction p with
  | const c =>
    -- F(y) = c, F'(x) = 0.
    show HasDerivAt (fun _ => c) 0 x
    exact HasDerivAt_const c x
  | varX =>
    -- F(y) = y, F'(x) = 1.
    show HasDerivAt (fun y => y) 1 x
    exact HasDerivAt_id x
  | varY i =>
    -- F(y) = chain.chainValues y i = chain.evals i y.
    -- F'(x) = chain.evals i derivative at x
    --       = eval (chain.relations i) x (chain.chainValues x) by coherence.
    show HasDerivAt (fun y => chain.chainValues y i)
                    (MultiPoly.eval (chain.relations i) x (chain.chainValues x))
                    x
    -- chain.chainValues y i = chain.evals i y by def.
    have heq : (fun y => chain.chainValues y i) = chain.evals i := by
      funext y
      rfl
    rw [heq]
    exact hcoherent i
  | add p q ihp ihq =>
    show HasDerivAt
      (fun y => MultiPoly.eval p y (chain.chainValues y)
              + MultiPoly.eval q y (chain.chainValues y))
      (MultiPoly.eval (chainTotalDeriv chain p) x (chain.chainValues x)
       + MultiPoly.eval (chainTotalDeriv chain q) x (chain.chainValues x))
      x
    exact HasDerivAt_add _ _ _ _ x ihp ihq
  | sub p q ihp ihq =>
    show HasDerivAt
      (fun y => MultiPoly.eval p y (chain.chainValues y)
              - MultiPoly.eval q y (chain.chainValues y))
      (MultiPoly.eval (chainTotalDeriv chain p) x (chain.chainValues x)
       - MultiPoly.eval (chainTotalDeriv chain q) x (chain.chainValues x))
      x
    exact HasDerivAt_sub _ _ _ _ x ihp ihq
  | mul p q ihp ihq =>
    show HasDerivAt
      (fun y => MultiPoly.eval p y (chain.chainValues y)
              * MultiPoly.eval q y (chain.chainValues y))
      (MultiPoly.eval (chainTotalDeriv chain p) x (chain.chainValues x)
       * MultiPoly.eval q x (chain.chainValues x)
       + MultiPoly.eval p x (chain.chainValues x)
       * MultiPoly.eval (chainTotalDeriv chain q) x (chain.chainValues x))
      x
    exact HasDerivAt_mul _ _ _ _ x ihp ihq

/-! ### HasDerivAt for length-0 chains (the base case of the full chain rule)

For a PfaffianFn with chain length 0, the eval is just a univariate
polynomial in x. The HasDerivAt theorem follows directly from
`multiPolyHasDerivAt_eval_dX` since there are no chain variables to
worry about.

This is the BASE CASE of the full HasDerivAt-for-PfaffianFn theorem
(needed for the constructive Khovanskii inductive step). The
inductive case (chain length n+1) requires the multi-variable chain
rule combining dX, dY, and the chain coherence — a separate ~150-200
line proof. -/

/-- **PfaffianFn HasDerivAt — general chain length.** For a PfaffianFn
whose chain is coherent at x, the eval has HasDerivAt with derivative
given by `chainTotalDeriv`. Direct application of
`multiPolyHasDerivAt_eval_with_chain`. -/
theorem PfaffianFn.hasDerivAt_eval (f : PfaffianFn) (x : Real)
    (hcoherent : f.chain.IsCoherentAt x) :
    HasDerivAt f.eval
               (MultiPoly.eval (chainTotalDeriv f.chain f.poly) x
                                (f.chain.chainValues x))
               x := by
  show HasDerivAt (fun y => MultiPoly.eval f.poly y (f.chain.chainValues y))
                  (MultiPoly.eval (chainTotalDeriv f.chain f.poly) x
                                   (f.chain.chainValues x))
                  x
  exact multiPolyHasDerivAt_eval_with_chain f.chain f.poly x hcoherent

/-- The chain-total-derivative as a PfaffianFn (same chain, updated
polynomial). This is the natural PfaffianFn-level wrapper for the
constructive total derivative. Used in the constructive Khovanskii
inductive step (Item 4) as the function whose zero count bounds f's
via Rolle. -/
noncomputable def chainTotalDerivative (f : PfaffianFn) : PfaffianFn :=
  { n := f.n,
    chain := f.chain,
    poly := chainTotalDeriv f.chain f.poly }

/-- Same chain length: the derivative preserves chain structure. -/
theorem chainTotalDerivative_chainLength (f : PfaffianFn) :
    f.chainTotalDerivative.chainLength = f.chainLength := rfl

/-- Eval of the chain-total-derivative matches the polynomial-level
chainTotalDeriv evaluation. -/
theorem chainTotalDerivative_eval (f : PfaffianFn) (x : Real) :
    f.chainTotalDerivative.eval x =
    MultiPoly.eval (chainTotalDeriv f.chain f.poly) x (f.chain.chainValues x) := rfl

/-- **The HasDerivAt theorem in PfaffianFn-natural form.** Repeats
`PfaffianFn.hasDerivAt_eval` with the PfaffianFn wrapper for the
derivative. This is the form Item 4 (Khovanskii reduction) actually
uses with `zero_count_bound_by_deriv`. -/
theorem hasDerivAt_eval_natural (f : PfaffianFn) (x : Real)
    (hcoherent : f.chain.IsCoherentAt x) :
    HasDerivAt f.eval (f.chainTotalDerivative.eval x) x := by
  show HasDerivAt f.eval
                  (MultiPoly.eval (chainTotalDeriv f.chain f.poly) x
                                   (f.chain.chainValues x)) x
  exact PfaffianFn.hasDerivAt_eval f x hcoherent

/-- For a PfaffianFn with no chain variables, the eval has HasDerivAt
matching the totalDerivative (which reduces to dX in this case). -/
theorem PfaffianFn.hasDerivAt_eval_chainLength_zero (f : PfaffianFn)
    (h0 : f.n = 0) (x : Real) :
    HasDerivAt f.eval (MultiPoly.eval (MultiPoly.dX f.poly) x
                        (f.chain.chainValues x)) x := by
  -- f.eval x = MultiPoly.eval f.poly x (f.chain.chainValues x).
  -- With f.n = 0, chainValues is trivially the empty function.
  -- HasDerivAt follows from multiPolyHasDerivAt_eval_dX with env =
  -- chainValues x.
  show HasDerivAt (fun y => MultiPoly.eval f.poly y (f.chain.chainValues y))
                  (MultiPoly.eval (MultiPoly.dX f.poly) x (f.chain.chainValues x))
                  x
  -- For chain length 0, chainValues is constant (no actual values).
  -- So `fun y => MultiPoly.eval f.poly y (f.chain.chainValues y)` equals
  -- `fun y => MultiPoly.eval f.poly y (f.chain.chainValues x)`.
  have hcv : ∀ y, f.chain.chainValues y = f.chain.chainValues x := by
    intro y
    -- chainValues : Fin n → Real with n = 0 is Fin.elim0 essentially.
    funext i
    -- i : Fin 0 is impossible, so this is vacuously true.
    exact absurd i.isLt (by simp [h0])
  have hfun : (fun y => MultiPoly.eval f.poly y (f.chain.chainValues y))
            = (fun y => MultiPoly.eval f.poly y (f.chain.chainValues x)) := by
    funext y
    rw [hcv]
  rw [hfun]
  exact MultiPoly.multiPolyHasDerivAt_eval_dX f.poly (f.chain.chainValues x) x

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
