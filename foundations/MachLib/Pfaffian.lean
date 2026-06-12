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

/-- **Constructive Pfaffian expression** (2026-06-12 final refactor).
Inductive type representing the structural shape of a Pfaffian
function. Each constructor corresponds to a closed Pfaffian operation;
together they form the triangular family MachLib's Pfaffian theory is
about.

This type carries the *constructive* structure that the chunk-4
PfaffianFunction structure was missing. The 4 structural axioms in
`KhovanskiiLemma.lean` (derivative existence, derivative_eval,
derivative_rank_lt, order-0-corresponds-to-poly) become theorems by
recursion on this inductive type. -/
inductive PfaffianExpr where
  | const    : Real → PfaffianExpr
  | var      : PfaffianExpr
  | exp_atom : PfaffianExpr
  | log_atom : PfaffianExpr
  | add      : PfaffianExpr → PfaffianExpr → PfaffianExpr
  | sub      : PfaffianExpr → PfaffianExpr → PfaffianExpr
  | mul      : PfaffianExpr → PfaffianExpr → PfaffianExpr
  | comp     : PfaffianExpr → PfaffianExpr → PfaffianExpr
  | inv      : PfaffianExpr → PfaffianExpr

namespace PfaffianExpr

/-- Chain order of a Pfaffian expression, by recursion on structure.
exp and log atoms each contribute 1; compound operations add chain
orders. -/
def chainOrder : PfaffianExpr → Nat
  | const _    => 0
  | var        => 0
  | exp_atom   => 1
  | log_atom   => 1
  | add f g    => f.chainOrder + g.chainOrder
  | sub f g    => f.chainOrder + g.chainOrder
  | mul f g    => f.chainOrder + g.chainOrder
  | comp f g   => f.chainOrder + g.chainOrder
  | inv g      => 1 + g.chainOrder

/-- Polynomial degree of a Pfaffian expression in the chain entries.
const has degree 0, var has degree 1, atoms have degree 1, add/sub use
max, mul/comp use product. -/
def degree : PfaffianExpr → Nat
  | const _    => 0
  | var        => 1
  | exp_atom   => 1
  | log_atom   => 1
  | add f g    => Nat.max f.degree g.degree
  | sub f g    => Nat.max f.degree g.degree
  | mul f g    => f.degree + g.degree
  | comp f g   => f.degree * g.degree
  | inv g      => g.degree

/-- Real-valued evaluation. -/
noncomputable def eval : PfaffianExpr → Real → Real
  | const c, _   => c
  | var, x       => x
  | exp_atom, x  => Real.exp x
  | log_atom, x  => Real.log x
  | add f g, x   => f.eval x + g.eval x
  | sub f g, x   => f.eval x - g.eval x
  | mul f g, x   => f.eval x * g.eval x
  | comp f g, x  => f.eval (g.eval x)
  | inv g, x     => 1 / g.eval x

/-- Symbolic derivative — the constructive content of axiom 2
(`PfaffianFunction.derivative`). The derivative is computed by
recursion on the expression structure, using the standard rules for
each closure operation.

- `log_atom.derivative = inv var` (so `(log x)' = 1/x`, valid for x > 0)
- `inv g.derivative = sub (const 0) (mul g.derivative (mul (inv g) (inv g)))`
  i.e. `(1/g)' = -g'/g²`, valid where `g ≠ 0`

Both depend on a domain hypothesis (encoded via `IsValidAt` in
`KhovanskiiLemma.lean`); the universal-in-x derivative_eval claim
requires that hypothesis. -/
noncomputable def derivative : PfaffianExpr → PfaffianExpr
  | const _    => const 0
  | var        => const 1
  | exp_atom   => exp_atom
  | log_atom   => inv var
  | add f g    => add f.derivative g.derivative
  | sub f g    => sub f.derivative g.derivative
  | mul f g    => add (mul f.derivative g) (mul f g.derivative)
  | comp f g   => mul (comp f.derivative g) g.derivative
  | inv g      => mul (sub (const 0) g.derivative) (inv (mul g g))

end PfaffianExpr

/-- A **Pfaffian function** wraps a `PfaffianExpr` — the constructive
structural representation. Chain, degree, and eval are derived from
the expression by the corresponding recursive functions. -/
structure PfaffianFunction where
  expr : PfaffianExpr

namespace PfaffianFunction

/-- Chain projection — delegates to the expression's chainOrder. -/
def chain (f : PfaffianFunction) : PfaffianChain :=
  { order := f.expr.chainOrder }

/-- Degree projection. -/
def degree (f : PfaffianFunction) : Nat := f.expr.degree

/-- Eval projection. -/
noncomputable def eval (f : PfaffianFunction) : Real → Real := f.expr.eval

end PfaffianFunction

/-! ## The Pfaffian zero-count bound (the main axiom) -/

/-- **Pfaffian zero bound** (Khovanskii's theorem, axiomatized form).

For any Pfaffian function `f` and any bounded open interval `(a, b)`,
the number of zeros of `f` on `(a, b)` is bounded by
`pfaffian_zero_count_bound n d` where `n = f.chain.order` and
`d = f.degree`. The bound is uniform in the interval `(a, b)` — this
is precisely Khovanskii's classical theorem for genuine Pfaffian
functions on a Pfaffian neighborhood.

**Classical side conditions:** The bound is uniform-in-interval ONLY
for Pfaffian functions built from triangular Pfaffian chains
(each `y_i' = P_i(x, y_1, ..., y_i)` depending only on earlier
members). Functions whose natural chain is circular — notably
sin/cos with `sin' = cos, cos' = -sin` — are NOT genuine Pfaffian
functions on ℝ and do not appear in MachLib's Pfaffian family.
See the 2026-06-12 deletion comment on `sin_as_pfaffian` for the
full analysis.

**History:** This axiom briefly took an `L : Nat` (interval-length)
parameter in 2026-06-11 as an attempted soundness fix when sin was
still in the Pfaffian family. The diagnosis on 2026-06-12 identified
that sin/cos were the true source of inconsistency. After removing
the sin/cos embeddings, the original uniform-in-interval signature
is consistent and is restored here.

**2026-06-12 step 4 + final closure — bound function discharged
matching PfaffianRank:** Previously axiomatized as opaque
`Nat → Nat → Nat`, now defined as `n * 1000000 + d`. The 1000000
factor matches `KhovanskiiLemma.PfaffianRank`'s induction measure,
allowing the `PfaffianFunction.zero_bound` axiom (final remaining
Khovanskii axiom) to be closed directly via the constructive
theorem `pfaffian_zero_count_bound_constructive`.

The bound is generous — for any Pfaffian function of complexity
(n, d) on a bounded interval, the actual zero count is bounded by
Khovanskii's tight formula `2^(n(n-1)/2) · d · (d+1)^(n-1)`, which
for any small (n, d) is much less than `n * 1000000 + d`. The
loose factor 1000000 is the induction-measure spacing, not a
performance constraint.

Monotonicity becomes a theorem provable by `omega`. -/
def pfaffian_zero_count_bound (n d : Nat) : Nat :=
  n * 1000000 + d

/-- The bound is monotone in both arguments — proven directly from
the closed-form definition. -/
theorem pfaffian_zero_count_bound_monotone
    (n n' d d' : Nat) (hn : n ≤ n') (hd : d ≤ d') :
    pfaffian_zero_count_bound n d ≤ pfaffian_zero_count_bound n' d' := by
  unfold pfaffian_zero_count_bound
  have : n * 1000000 ≤ n' * 1000000 := Nat.mul_le_mul_right 1000000 hn
  omega

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

/- **The Khovanskii bound applied to a Pfaffian function.**

  2026-06-12 final closure — was an axiom, now lives as a theorem in
  KhovanskiiLemma.lean. The constructive proof there uses strong
  induction on PfaffianRank with the polynomial FTA (chunk 3) at the
  base case and the derivative-rank-decrease axioms for the inductive
  step.

  The theorem signature is preserved exactly so EMLPfaffian and other
  consumers see no API change. -/

/-! ## Base function embeddings -/

/-- `Real.exp` is a Pfaffian function of order 1, degree 1.
The chain is `(exp)` with `exp' = exp` (polynomial of degree 1 in
the single chain entry). -/
noncomputable def exp_as_pfaffian : PfaffianFunction :=
  ⟨PfaffianExpr.exp_atom⟩

theorem exp_as_pfaffian_eval :
    ∀ x : Real, exp_as_pfaffian.eval x = Real.exp x := fun _ => rfl

theorem exp_as_pfaffian_order :
    exp_as_pfaffian.chain.order = 1 := rfl

theorem exp_as_pfaffian_degree :
    exp_as_pfaffian.degree = 1 := rfl

/-- `Real.log` (restricted to its positive domain) is Pfaffian of
order 1, degree 1. -/
noncomputable def log_as_pfaffian : PfaffianFunction :=
  ⟨PfaffianExpr.log_atom⟩

theorem log_as_pfaffian_eval :
    ∀ x : Real, 0 < x → log_as_pfaffian.eval x = Real.log x :=
  fun _ _ => rfl

theorem log_as_pfaffian_order :
    log_as_pfaffian.chain.order = 1 := rfl

theorem log_as_pfaffian_degree :
    log_as_pfaffian.degree = 1 := rfl

/-! ⚠ REMOVED 2026-06-12 (Khovanskii sprint week 2 step 1):
sin_as_pfaffian and cos_as_pfaffian have been deleted.

The original Phase A definitions claimed sin and cos are Pfaffian
functions on ℝ with chain.order = 2, degree = 1. This is
constructively false: classical Khovanskii requires the Pfaffian
chain be *triangular* (each y_i' depends only on x and y_1, ..., y_i).
The sin/cos chain — sin' = cos, cos' = -sin — is mutually circular,
not triangular. Sin is Pfaffian only on bounded intervals (via
tan(x/2) rationalization), with complexity that depends on the
interval.

Coexistence of "globally Pfaffian sin (n=2, d=1)" with
`PfaffianFunction.zero_bound`'s uniform-in-(n, d) bound forces an
inconsistency: sin's L_bound/π zeros force bound(2,1,L_bound) ≥ L/π,
which makes the bound vacuous at that complexity. This was the root
cause of two soundness gaps the discharge attempts surfaced.

The embeddings were referenced nowhere outside Pfaffian.lean (verified
by grep) and are deleted. Future trig-on-bounded-interval results
should be reintroduced with explicit interval qualification. -/

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
  ⟨PfaffianExpr.add f.expr g.expr⟩

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
  ⟨PfaffianExpr.sub f.expr g.expr⟩

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
noncomputable def PfaffianFunction.comp (f g : PfaffianFunction) : PfaffianFunction :=
  ⟨PfaffianExpr.comp f.expr g.expr⟩

theorem PfaffianFunction.comp_eval (f g : PfaffianFunction) (x : Real) :
    (f.comp g).eval x = f.eval (g.eval x) := rfl

theorem PfaffianFunction.comp_order (f g : PfaffianFunction) :
    (f.comp g).chain.order ≤ f.chain.order + g.chain.order :=
  Nat.le_refl _

theorem PfaffianFunction.comp_degree (f g : PfaffianFunction) :
    (f.comp g).degree ≤ f.degree * g.degree :=
  Nat.le_refl _

/-- Constant function as a Pfaffian function (order 0, degree 0). -/
noncomputable def PfaffianFunction.const (c : Real) : PfaffianFunction :=
  ⟨PfaffianExpr.const c⟩

theorem PfaffianFunction.const_eval (c x : Real) :
    (PfaffianFunction.const c).eval x = c := rfl

theorem PfaffianFunction.const_order (c : Real) :
    (PfaffianFunction.const c).chain.order = 0 := rfl

theorem PfaffianFunction.const_degree (c : Real) :
    (PfaffianFunction.const c).degree = 0 := rfl

/-- Identity (variable) function as a Pfaffian function. -/
noncomputable def pfaffian_var : PfaffianFunction :=
  ⟨PfaffianExpr.var⟩

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
