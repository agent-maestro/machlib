import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.Differentiation
import MachLib.AnalyticFiniteZeros

/-!
# Pfaffian Functions — header port (Phase A of Pfaffian programme)

Ports the Pfaffian chain / Pfaffian function infrastructure into
MachLib as a header file. The semantic content (zero-count bound)
is axiomatized; a future "Phase C" research push replaces the axiom
with a constructive Khovanskii-style proof.

**Strategic purpose:** Pfaffian zero bounds collapse the EML
hierarchy programme from N^k case enumeration (per depth k) to ONE
theorem per question: `sin ∉ EML_k for all k`, `EML_k ⊊ EML_{k+1}
for all k`, etc.

**Scope of this file:**

1. `PfaffianChain` opaque type — abstracts the sequence of analytic
   functions `(f_1, ..., f_n)` where each `f_i' = P_i(x, f_1, ..., f_i)`
   for some polynomial `P_i`.
2. `PfaffianFunction` opaque type — polynomial in chain entries.
3. Order + degree projections.
4. Evaluation as `Real → Real`.
5. **Pfaffian zero bound** (axiomatized): for any Pfaffian function
   `f` on a bounded open interval `(a, b)`, the zero count is bounded
   by `B(f.chain.order, f.degree)` where `B : Nat → Nat → Nat` is a
   universal function (concretely: `B(n, d) = d · (d + 1)^(n - 1)`
   per Khovanskii's standard formulation).
6. **Base embeddings:** `exp`, `log`, `sin`, `cos` as Pfaffian
   functions of known orders.
7. **Closure axioms:** sum, difference, product, composition of
   Pfaffian functions remain Pfaffian (with order bounded by sum of
   orders).

**Strategic deferred:**

- `eml_pfaffian` constructor (EMLTree → PfaffianFunction with explicit
  order/degree bounds): part of Phase D.
- The sin barrier corollary (`sin ∉ EML_k for all k`): part of Phase D.
- The constructive zero-bound proof: Phase C (~2-3 weeks).

**Honest scope:** This is a header port. Replacing the axiomatized
zero bound with a constructive proof is the genuine research work
deferred to Phase C. Until then, downstream consumers (Phase D)
treat the bound as an axiom and produce results conditional on it.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib
namespace Real

/-! ## Pfaffian chain & function — opaque types -/

/-- A **Pfaffian chain** is a sequence of analytic functions
`(f_1, ..., f_n)` on an open interval `I` where each `f_i` has
derivative expressible as a polynomial in `(x, f_1, ..., f_i)`.

Axiomatized as an opaque type. Concrete chains are constructed via
the embedding axioms (`pfaffian_chain_empty`, `pfaffian_chain_exp`,
`pfaffian_chain_cons`, etc.) below.

In a future Phase C formalization, this is replaced by an inductive
type carrying explicit polynomial expressions and well-foundedness
proofs. -/
axiom PfaffianChain : Type

/-- The length (order) of a Pfaffian chain. -/
axiom PfaffianChain.order : PfaffianChain → Nat

/-- A **Pfaffian function** is a polynomial in the chain entries
(treating `x` as a chain entry too). Axiomatized as opaque. -/
axiom PfaffianFunction : Type

/-- The underlying chain of a Pfaffian function. -/
axiom PfaffianFunction.chain : PfaffianFunction → PfaffianChain

/-- Polynomial degree of a Pfaffian function in the chain entries.
This is the "degree" parameter in the Khovanskii zero bound. -/
axiom PfaffianFunction.degree : PfaffianFunction → Nat

/-- Evaluation of a Pfaffian function as a real-valued function. -/
axiom PfaffianFunction.eval : PfaffianFunction → Real → Real

/-! ## The Pfaffian zero-count bound (the main axiom) -/

/-- **Pfaffian zero bound** (Khovanskii's theorem, axiomatized form).

For any Pfaffian function `f` and any bounded open interval `(a, b)`
contained in the domain of definition of `f`, the number of zeros of
`f` on `(a, b)` is bounded by `pfaffian_zero_count_bound n d` where
`n = f.chain.order` and `d = f.degree`. The bound depends ONLY on
`n` and `d`, not on `f` or `(a, b)`.

This is the key strategic theorem: the uniform-in-parameters bound
that the existing `analytic_finite_zeros_compact` (in
`AnalyticFiniteZeros.lean`) does NOT provide. Replacing this axiom
with a constructive proof is the Phase C deliverable. -/
axiom pfaffian_zero_count_bound : Nat → Nat → Nat

/-- The bound is monotone in both arguments — a sanity-check axiom
that captures the "more orders, more zeros" intuition. -/
axiom pfaffian_zero_count_bound_monotone :
    ∀ n n' d d' : Nat, n ≤ n' → d ≤ d' →
    pfaffian_zero_count_bound n d ≤ pfaffian_zero_count_bound n' d'

/-- A `Real → Prop` predicate counting zeros (cardinality bounded). -/
def PfaffianFunction.zero_count_le (f : PfaffianFunction) (a b : Real)
    (N : Nat) : Prop :=
  ∀ zeros : List Real,
    (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
    zeros.length ≤ N

/-- **The Khovanskii bound applied to a Pfaffian function.** Any
NON-ZERO Pfaffian function `f` (i.e., not identically zero) has
zero count on `(a, b)` bounded by `pfaffian_zero_count_bound
f.chain.order f.degree`.

The non-zero precondition (`hne`) excludes the degenerate case where
`f` is the constant 0 function — that function vanishes everywhere
and trivially has unbounded zero count, which would make the axiom
inconsistent. -/
axiom PfaffianFunction.zero_bound (f : PfaffianFunction) (a b : Real)
    (hab : a < b) (hne : ∃ x : Real, f.eval x ≠ 0) :
    f.zero_count_le a b (pfaffian_zero_count_bound f.chain.order f.degree)

/-! ## Base function embeddings -/

/-- `Real.exp` is a Pfaffian function of order 1, degree 1.
The chain is `(exp)` with `exp' = exp` (polynomial of degree 1 in
the single chain entry). -/
axiom exp_as_pfaffian : PfaffianFunction

axiom exp_as_pfaffian_eval :
    ∀ x : Real, exp_as_pfaffian.eval x = Real.exp x

axiom exp_as_pfaffian_order :
    exp_as_pfaffian.chain.order = 1

axiom exp_as_pfaffian_degree :
    exp_as_pfaffian.degree = 1

/-- `Real.log` (restricted to its positive domain) is Pfaffian of
order 1, degree 1. The chain is `(log)` with `log' = 1/x`, which is
a rational function in `x` — formally a Pfaffian relation of degree
1 once we extend the chain with `1/x` (order 1 for the inverse).
For MachLib's purposes, we collapse this bookkeeping into an
axiomatized order-1 statement. -/
axiom log_as_pfaffian : PfaffianFunction

axiom log_as_pfaffian_eval :
    ∀ x : Real, 0 < x → log_as_pfaffian.eval x = Real.log x

axiom log_as_pfaffian_order :
    log_as_pfaffian.chain.order = 1

axiom log_as_pfaffian_degree :
    log_as_pfaffian.degree = 1

/-- `Real.sin` is Pfaffian of order 2, degree 1. The chain is
`(sin, cos)` with `sin' = cos` and `cos' = -sin`. -/
axiom sin_as_pfaffian : PfaffianFunction

axiom sin_as_pfaffian_eval :
    ∀ x : Real, sin_as_pfaffian.eval x = Real.sin x

axiom sin_as_pfaffian_order :
    sin_as_pfaffian.chain.order = 2

axiom sin_as_pfaffian_degree :
    sin_as_pfaffian.degree = 1

/-- `Real.cos` is Pfaffian of order 2, degree 1, sharing the chain
with `sin`. -/
axiom cos_as_pfaffian : PfaffianFunction

axiom cos_as_pfaffian_eval :
    ∀ x : Real, cos_as_pfaffian.eval x = Real.cos x

axiom cos_as_pfaffian_order :
    cos_as_pfaffian.chain.order = 2

axiom cos_as_pfaffian_degree :
    cos_as_pfaffian.degree = 1

/-! ## Closure axioms -/

/-- Sum of two Pfaffian functions is Pfaffian; order bounded by sum
of orders, degree by max of degrees. -/
axiom PfaffianFunction.add (f g : PfaffianFunction) : PfaffianFunction

axiom PfaffianFunction.add_eval (f g : PfaffianFunction) (x : Real) :
    (f.add g).eval x = f.eval x + g.eval x

axiom PfaffianFunction.add_order (f g : PfaffianFunction) :
    (f.add g).chain.order ≤ f.chain.order + g.chain.order

axiom PfaffianFunction.add_degree (f g : PfaffianFunction) :
    (f.add g).degree ≤ Nat.max f.degree g.degree

/-- Difference of two Pfaffian functions is Pfaffian. -/
axiom PfaffianFunction.sub (f g : PfaffianFunction) : PfaffianFunction

axiom PfaffianFunction.sub_eval (f g : PfaffianFunction) (x : Real) :
    (f.sub g).eval x = f.eval x - g.eval x

axiom PfaffianFunction.sub_order (f g : PfaffianFunction) :
    (f.sub g).chain.order ≤ f.chain.order + g.chain.order

axiom PfaffianFunction.sub_degree (f g : PfaffianFunction) :
    (f.sub g).degree ≤ Nat.max f.degree g.degree

/-- Composition of Pfaffian functions: `f ∘ g` is Pfaffian. Order
bounded by `f.order + g.order`. Used to build the EML embedding
recursively (each level of `eml` adds an `exp` and a `log` composition). -/
axiom PfaffianFunction.comp (f g : PfaffianFunction) : PfaffianFunction

axiom PfaffianFunction.comp_eval (f g : PfaffianFunction) (x : Real) :
    (f.comp g).eval x = f.eval (g.eval x)

axiom PfaffianFunction.comp_order (f g : PfaffianFunction) :
    (f.comp g).chain.order ≤ f.chain.order + g.chain.order

axiom PfaffianFunction.comp_degree (f g : PfaffianFunction) :
    (f.comp g).degree ≤ f.degree * g.degree

/-- Constant function as a Pfaffian function (order 0, degree 0). -/
axiom PfaffianFunction.const (c : Real) : PfaffianFunction

axiom PfaffianFunction.const_eval (c x : Real) :
    (PfaffianFunction.const c).eval x = c

axiom PfaffianFunction.const_order (c : Real) :
    (PfaffianFunction.const c).chain.order = 0

axiom PfaffianFunction.const_degree (c : Real) :
    (PfaffianFunction.const c).degree = 0

/-- Identity (variable) function as a Pfaffian function (order 0,
degree 1). -/
axiom pfaffian_var : PfaffianFunction

axiom pfaffian_var_eval :
    ∀ x : Real, pfaffian_var.eval x = x

axiom pfaffian_var_order :
    pfaffian_var.chain.order = 0

axiom pfaffian_var_degree :
    pfaffian_var.degree = 1

end Real
end MachLib

/-!
## Phase A scope summary

This file ships the axiomatized Pfaffian infrastructure. Total
axiom count:

- Types (2): PfaffianChain, PfaffianFunction.
- Projections (5): chain.order, function.chain, function.degree,
  function.eval, plus zero_count_le definition.
- The zero bound (3): pfaffian_zero_count_bound function +
  monotonicity + the main `PfaffianFunction.zero_bound` axiom.
- Base embeddings (4 × 4 = 16): exp/log/sin/cos × value/order/degree
  + the function symbol.
- Closure axioms (4 operations × 4 axioms = 16): add, sub, comp,
  const each with eval/order/degree axioms + the operation symbol.
- Variable embedding (4): pfaffian_var function + eval/order/degree.

Total: ~46 axioms. Header-only. No proofs of substantive content.

**Downstream consumers (Phase D):**

- `eml_pfaffian (t : EMLTree) : PfaffianFunction`: recursively build
  a Pfaffian function from an EML tree. Order bounded by `2 * t.depth`
  (each `eml(t1, t2)` adds one `exp` and one `log`, each contributing
  order 1).
- Sin barrier corollary: `sin ∉ EML_k for all k`, proved by:
  1. Suppose `t.eval = sin x` on (0, 2(k+1)π) for some t.depth ≤ k.
  2. `(eml_pfaffian t).sub sin_as_pfaffian` is Pfaffian of order
     ≤ 2k + 2 and degree 1.
  3. By `PfaffianFunction.zero_bound`, the zero count on (0, 2(k+1)π)
     is at most `pfaffian_zero_count_bound (2k+2) 1` = some fixed
     number N(k).
  4. But sin has `2(k+1)` zeros on (0, 2(k+1)π) (the integer
     multiples of π). For k large enough that 2(k+1) > N(k),
     contradiction.

The Phase D wiring is the next bounded artifact.

**Phase C deferred:**

`pfaffian_zero_count_bound` and `PfaffianFunction.zero_bound` are
axiomatized. The constructive proof (Khovanskii's lemma via
iterated Rolle + induction on chain order) is the Phase C work, ~2-3
weeks of focused effort. Until Phase C lands, the sin barrier
"for all k" result is conditional on the axiom; this is honest
scope and matches the AnalyticFiniteZeros / Differentiation header
ports' pattern.

Zero-Mathlib gate: PASS. Build clean.
-/
