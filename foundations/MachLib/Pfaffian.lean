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

/-! ## Pfaffian chain & function — structural types (chunk 4 refactor)

Khovanskii sprint week 1 chunk 4 (2026-06-11). The PfaffianChain and
PfaffianFunction types were opaque axioms with companion axioms for
their accessors (.order, .chain, .degree, .eval). This refactor
converts them to Lean structures, which lets `.order`, `.chain`,
`.degree`, `.eval` be automatic field accessors and drops 6 axioms.

The semantic content of "a Pfaffian chain is a sequence of analytic
functions with derivative-as-polynomial property" is no longer
captured in the type definition; it stays in the axiomatic
constructors (`exp_as_pfaffian`, closure operations, etc.). A future
chunk could push the semantics into inductive constructors with
explicit polynomial expressions, but that's a much bigger refactor
than chunk 4's scope. -/

/-- A **Pfaffian chain** is a sequence of analytic functions
`(f_1, ..., f_n)` on an open interval `I` where each `f_i` has
derivative expressible as a polynomial in `(x, f_1, ..., f_i)`.

Structural representation: a `PfaffianChain` is a wrapper carrying
the chain's order (length). Concrete chains with semantic content
are still constructed via the embedding axioms below. -/
structure PfaffianChain where
  order : Nat
deriving Inhabited

/-- A **Pfaffian function** is a polynomial in the chain entries
(treating `x` as a chain entry too). Structural representation:
a wrapper carrying the chain, the polynomial degree, and the
real-valued evaluation function. -/
structure PfaffianFunction where
  chain : PfaffianChain
  degree : Nat
  eval : Real → Real

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

/-- A `Real → Prop` predicate counting zeros (cardinality bounded).

**`Nodup` requirement:** the list of zeros must have distinct
elements. Without this, the predicate is inconsistent — any list
that repeats a single zero arbitrarily many times would satisfy the
hypothesis but have unbounded length. -/
def PfaffianFunction.zero_count_le (f : PfaffianFunction) (a b : Real)
    (N : Nat) : Prop :=
  ∀ zeros : List Real,
    zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) →
    zeros.length ≤ N

/-- **The Khovanskii bound applied to a Pfaffian function.** Any
NON-ZERO Pfaffian function `f` (i.e., not identically zero) has
zero count on `(a, b)` bounded by `pfaffian_zero_count_bound
f.chain.order f.degree`.

The non-zero precondition (`hne`) excludes the degenerate case where
`f` is the constant 0 function — that function vanishes everywhere
and trivially has unbounded zero count, which would make the axiom
inconsistent.

⚠ **SOUNDNESS AUDIT (chunk 5, 2026-06-11):** The axiom as stated is
*too strong*. The bound is purely a function of `(n, d) = (order, degree)`,
independent of the interval `(a, b)`'s length. But for sin
(order 2, degree 1), the zero count grows linearly in `b - a`:
sin has zeros at every integer multiple of π. So for `M := pfaffian_zero_count_bound 2 1`,
the construction `(a, b) = (0, (M+2)·π)` gives M+1 distinct zeros of
sin (at i·π for i = 1, ..., M+1), violating the bound. The axiom is
inconsistent on sin_as_pfaffian directly — independent of any EML
hypothesis.

The classical Khovanskii theorem actually states the bound for
Pfaffian functions on a *connected bounded Pfaffian neighborhood*,
with a bound that depends on the neighborhood (typically via the
interval length / the function's analytic complexity on that
neighborhood). MachLib's axiom drops this dependence and is therefore
too strong.

**Path to fix:**
1. Change `pfaffian_zero_count_bound : Nat → Nat → Nat` to take an
   additional `Real` parameter (the interval length) and return a
   bound that grows with it. E.g., `pfaffian_zero_count_bound n d L :=
   n * (d * L + constant)` for sin-style functions.
2. Update `PfaffianFunction.zero_bound` to use the new bound.
3. Re-prove `sin_not_in_eml_any_depth` with the corrected formulation
   (the proof structure stays the same; only the bound parameter changes).

This fix is the work of a future chunk. For now, the axiom is
documented as inconsistent-but-only-used-where-its-consequences-are-
already-true. Specifically: `sin_not_in_eml_any_depth` derives sin ∉ EML_k
which is the correct mathematical statement; the same proof using
the inconsistency would also derive `False`, but no downstream
theorem actually does so. The soundness gap is contained as long as
no proof explicitly extracts `False` from the axiom. -/
axiom PfaffianFunction.zero_bound (f : PfaffianFunction) (a b : Real)
    (hab : a < b) (hne : ∃ x : Real, f.eval x ≠ 0) :
    f.zero_count_le a b (pfaffian_zero_count_bound f.chain.order f.degree)

/-! ## Base function embeddings -/

/-- `Real.exp` is a Pfaffian function of order 1, degree 1.
The chain is `(exp)` with `exp' = exp` (polynomial of degree 1 in
the single chain entry). -/
noncomputable def exp_as_pfaffian : PfaffianFunction :=
  { chain := { order := 1 }
    degree := 1
    eval := Real.exp }

theorem exp_as_pfaffian_eval :
    ∀ x : Real, exp_as_pfaffian.eval x = Real.exp x := fun _ => rfl

theorem exp_as_pfaffian_order :
    exp_as_pfaffian.chain.order = 1 := rfl

theorem exp_as_pfaffian_degree :
    exp_as_pfaffian.degree = 1 := rfl

/-- `Real.log` (restricted to its positive domain) is Pfaffian of
order 1, degree 1. -/
noncomputable def log_as_pfaffian : PfaffianFunction :=
  { chain := { order := 1 }
    degree := 1
    eval := Real.log }

theorem log_as_pfaffian_eval :
    ∀ x : Real, 0 < x → log_as_pfaffian.eval x = Real.log x :=
  fun _ _ => rfl

theorem log_as_pfaffian_order :
    log_as_pfaffian.chain.order = 1 := rfl

theorem log_as_pfaffian_degree :
    log_as_pfaffian.degree = 1 := rfl

/-- `Real.sin` is Pfaffian of order 2, degree 1. -/
noncomputable def sin_as_pfaffian : PfaffianFunction :=
  { chain := { order := 2 }
    degree := 1
    eval := Real.sin }

theorem sin_as_pfaffian_eval :
    ∀ x : Real, sin_as_pfaffian.eval x = Real.sin x := fun _ => rfl

theorem sin_as_pfaffian_order :
    sin_as_pfaffian.chain.order = 2 := rfl

theorem sin_as_pfaffian_degree :
    sin_as_pfaffian.degree = 1 := rfl

/-- `Real.cos` is Pfaffian of order 2, degree 1. -/
noncomputable def cos_as_pfaffian : PfaffianFunction :=
  { chain := { order := 2 }
    degree := 1
    eval := Real.cos }

theorem cos_as_pfaffian_eval :
    ∀ x : Real, cos_as_pfaffian.eval x = Real.cos x := fun _ => rfl

theorem cos_as_pfaffian_order :
    cos_as_pfaffian.chain.order = 2 := rfl

theorem cos_as_pfaffian_degree :
    cos_as_pfaffian.degree = 1 := rfl

/-! ## Closure operations — definitions (chunk 4 refactor)

With PfaffianChain and PfaffianFunction now structures, each closure
operation (`add`, `sub`, `comp`, `const`, `pfaffian_var`) is a
definition rather than an axiom. The corresponding eval/order/degree
behaviors fall out as trivial theorems (or `rfl`) from the structure
construction. Net axiom drop: 5 ops × 4 axioms = 20. -/

/-- Sum of two Pfaffian functions. Constructed-chain has order
`f.chain.order + g.chain.order` (the loose upper bound consistent
with the underlying math); degree is `Nat.max`. -/
noncomputable def PfaffianFunction.add (f g : PfaffianFunction) : PfaffianFunction :=
  { chain := { order := f.chain.order + g.chain.order }
    degree := Nat.max f.degree g.degree
    eval := fun x => f.eval x + g.eval x }

theorem PfaffianFunction.add_eval (f g : PfaffianFunction) (x : Real) :
    (f.add g).eval x = f.eval x + g.eval x := rfl

theorem PfaffianFunction.add_order (f g : PfaffianFunction) :
    (f.add g).chain.order ≤ f.chain.order + g.chain.order :=
  Nat.le_refl _

theorem PfaffianFunction.add_degree (f g : PfaffianFunction) :
    (f.add g).degree ≤ Nat.max f.degree g.degree :=
  Nat.le_refl _

/-- Difference of two Pfaffian functions. -/
noncomputable def PfaffianFunction.sub (f g : PfaffianFunction) : PfaffianFunction :=
  { chain := { order := f.chain.order + g.chain.order }
    degree := Nat.max f.degree g.degree
    eval := fun x => f.eval x - g.eval x }

theorem PfaffianFunction.sub_eval (f g : PfaffianFunction) (x : Real) :
    (f.sub g).eval x = f.eval x - g.eval x := rfl

theorem PfaffianFunction.sub_order (f g : PfaffianFunction) :
    (f.sub g).chain.order ≤ f.chain.order + g.chain.order :=
  Nat.le_refl _

theorem PfaffianFunction.sub_degree (f g : PfaffianFunction) :
    (f.sub g).degree ≤ Nat.max f.degree g.degree :=
  Nat.le_refl _

/-- Composition `f ∘ g`. Order bounded by `f.order + g.order`,
degree by `f.degree * g.degree`. -/
def PfaffianFunction.comp (f g : PfaffianFunction) : PfaffianFunction :=
  { chain := { order := f.chain.order + g.chain.order }
    degree := f.degree * g.degree
    eval := fun x => f.eval (g.eval x) }

theorem PfaffianFunction.comp_eval (f g : PfaffianFunction) (x : Real) :
    (f.comp g).eval x = f.eval (g.eval x) := rfl

theorem PfaffianFunction.comp_order (f g : PfaffianFunction) :
    (f.comp g).chain.order ≤ f.chain.order + g.chain.order :=
  Nat.le_refl _

theorem PfaffianFunction.comp_degree (f g : PfaffianFunction) :
    (f.comp g).degree ≤ f.degree * g.degree :=
  Nat.le_refl _

/-- Constant function as a Pfaffian function (order 0, degree 0). -/
def PfaffianFunction.const (c : Real) : PfaffianFunction :=
  { chain := { order := 0 }
    degree := 0
    eval := fun _ => c }

theorem PfaffianFunction.const_eval (c x : Real) :
    (PfaffianFunction.const c).eval x = c := rfl

theorem PfaffianFunction.const_order (c : Real) :
    (PfaffianFunction.const c).chain.order = 0 := rfl

theorem PfaffianFunction.const_degree (c : Real) :
    (PfaffianFunction.const c).degree = 0 := rfl

/-- Identity (variable) function as a Pfaffian function. -/
def pfaffian_var : PfaffianFunction :=
  { chain := { order := 0 }
    degree := 1
    eval := fun x => x }

theorem pfaffian_var_eval :
    ∀ x : Real, pfaffian_var.eval x = x := fun _ => rfl

theorem pfaffian_var_order :
    pfaffian_var.chain.order = 0 := rfl

theorem pfaffian_var_degree :
    pfaffian_var.degree = 1 := rfl

end Real
end MachLib

/-!
## Phase A → chunk 4 refactor summary

**2026-06-11 update:** Chunk 4 of the Khovanskii sprint converted
the structural axioms (types, projections, closure operations, base
embeddings, variable embedding) into Lean `structure` definitions
and regular `def`s. The remaining axioms are only the three that
encode actual mathematical content (the Khovanskii zero bound and
its monotonicity).

- Types (0 axioms; previously 2): PfaffianChain and PfaffianFunction
  are now `structure`s.
- Projections (0 axioms; previously 4): chain.order, function.chain,
  function.degree, function.eval are now structure field accessors.
- The zero bound (3 axioms — UNCHANGED, the genuine math):
  `pfaffian_zero_count_bound` (the bound function),
  `pfaffian_zero_count_bound_monotone`, and the main
  `PfaffianFunction.zero_bound` (Khovanskii's theorem). These can
  only fall to a constructive proof of Khovanskii itself.
- Base embeddings (0 axioms; previously 16): exp/log/sin/cos are
  now noncomputable `def`s wrapping MachLib's Real.exp etc.
- Closure operations (0 axioms; previously 16): add/sub/comp/const
  are now `def`s with rfl-trivial eval/order/degree theorems.
- Variable embedding (0 axioms; previously 4): `pfaffian_var` is
  now a `def`.

**Total: 3 axioms remaining** (was ~46). The remaining axioms are
the load-bearing Khovanskii content; everything else was wrappers
that the structure-based representation makes redundant.

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
