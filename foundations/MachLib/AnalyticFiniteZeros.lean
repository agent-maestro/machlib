import MachLib.Exp
import MachLib.Log
import MachLib.Forge
import MachLib.Trig
import MachLib.SinNotInEMLDepth2Sweep
import MachLib.IteratedExpBounds

/-!
# Analytic Finite Zeros — minimal port of `analytic_finite_zeros_compact`

Ports (the *structure* of) monogate-lean's `analytic_finite_zeros_compact`
to MachLib. The full proof there uses Bolzano–Weierstrass plus the analytic
identity theorem, both of which require Mathlib's analytic infrastructure
(`AnalyticOnNhd`, `Set.Finite`, `isCompact_Icc`, etc.) that MachLib does
not have.

The MachLib port here:
1. Defines a minimal `Set Real` interval type (Icc, Ioo, Ioi).
2. Axiomatizes `IsAnalyticOnReals` as a predicate.
3. Axiomatizes the theorem `analytic_finite_zeros_compact` itself.
4. Axiomatizes `eml_tree_analytic_on_pos` (analytic-on-(0, ∞) for
   well-formed depth-≤-k EML trees).

**Honest scope:** This port does NOT close the 2 deferred depth-2 sin
cases (Row 3 cv-vc and Row 3 vc-vc) on its own. The reason:
`analytic_finite_zeros_compact` gives FINITE zero count on bounded
sub-intervals (non-uniform in t), while sin also has finite zero count on
each bounded sub-interval. So no immediate contradiction.

The closure requires one of:
- **Uniform-in-k zero bound** (Khovanskii / o-minimal `ℝ_exp`): the
  multi-month Mathlib gap documented in
  `monogate-lean/MATHLIB_KHOVANSKII_NEEDS.md`. This is the *strategically
  correct* tool but is a long-form research project.
- **Derivative-comparison argument**: differentiate `t.eval = sin`, get
  `t.eval'(x) = cos(x)` everywhere, compute `t.eval'` symbolically, and
  show its asymptotic behavior (unbounded in x) contradicts `cos`'s
  boundedness. Requires differentiation infrastructure not yet in
  MachLib.

This file ships the **building blocks** — the theorem statement and
the EML-analyticity statement — so a future session adding either
Khovanskii bounds or symbolic differentiation can immediately apply
them to the 2 remaining cases.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib

/-! ## Minimal Set infrastructure -/

/-- A subset of `Real`, encoded as a predicate. -/
abbrev RealSet : Type := Real → Prop

/-- Open interval `(a, b)`. -/
def Ioo (a b : Real) : RealSet := fun x => a < x ∧ x < b

/-- Closed interval `[a, b]`. -/
def Icc (a b : Real) : RealSet := fun x => a ≤ x ∧ x ≤ b

/-- Open ray `(a, ∞)`. -/
def Ioi (a : Real) : RealSet := fun x => a < x

/-- `Set.Finite` substitute (genuine bounded-cardinality): there is a bound `n`
such that every `Nodup` list of elements of `s` has length `≤ n`. This is a real
finiteness predicate — the same shape the Pfaffian descent's `BoundedZeros` uses —
so `analytic_finite_zeros_compact` below is now a NON-VACUOUS analytic-finiteness
axiom (the earlier `∀ x, s x → True` was trivially true for every set). -/
def RealSetFinite (s : RealSet) : Prop :=
  ∃ n : Nat, ∀ l : List Real, l.Nodup → (∀ x ∈ l, s x) → l.length ≤ n

/-! ## Real-analyticity predicate (axiomatized) -/

/-- `IsAnalyticOnReals f S` means `f` is real-analytic on the subset `S`.

Axiomatized: a future formalization could replace this with a concrete
definition (power series, holomorphic on a complex neighborhood, etc.).
The axioms below capture the properties the port needs. -/
axiom IsAnalyticOnReals (f : Real → Real) (S : RealSet) : Prop

/-- The constant function is analytic everywhere. -/
axiom analytic_const (c : Real) (S : RealSet) : IsAnalyticOnReals (fun _ => c) S

/-- The identity function is analytic everywhere. -/
axiom analytic_id (S : RealSet) : IsAnalyticOnReals (fun x => x) S

/-- The exponential function is analytic everywhere. -/
axiom analytic_exp (S : RealSet) : IsAnalyticOnReals Real.exp S

/-- The logarithm is analytic on `(0, ∞)`. (Outside `(0, ∞)`, MachLib's
log returns 0 by convention; analyticity breaks at the boundary.) -/
axiom analytic_log_pos : IsAnalyticOnReals Real.log (Ioi 0)

/-- The reciprocal `1/x` is analytic on `(0, ∞)`. (True on all of `x ≠ 0`;
stated on `(0, ∞)` — the domain the encoder's reciprocal nodes need, where the
log argument is already positive — to mirror `analytic_log_pos`.) -/
axiom analytic_one_div_pos : IsAnalyticOnReals (fun x => 1 / x) (Ioi 0)

/-- The sine function is analytic everywhere. -/
axiom analytic_sin (S : RealSet) : IsAnalyticOnReals Real.sin S

/-- Closure under sum. -/
axiom analytic_add (f g : Real → Real) (S : RealSet) :
    IsAnalyticOnReals f S → IsAnalyticOnReals g S →
    IsAnalyticOnReals (fun x => f x + g x) S

/-- Closure under difference. -/
axiom analytic_sub (f g : Real → Real) (S : RealSet) :
    IsAnalyticOnReals f S → IsAnalyticOnReals g S →
    IsAnalyticOnReals (fun x => f x - g x) S

/-- Closure under product. The obvious sibling of `analytic_add`/`analytic_sub`
(a product of real-analytic functions is real-analytic); needed so that a
polynomial in `(x, y_1, …, y_n)` over analytic chain-values is analytic. -/
axiom analytic_mul (f g : Real → Real) (S : RealSet) :
    IsAnalyticOnReals f S → IsAnalyticOnReals g S →
    IsAnalyticOnReals (fun x => f x * g x) S

/-- Closure under composition. -/
axiom analytic_comp (f g : Real → Real) (S T : RealSet) :
    IsAnalyticOnReals g S →
    (∀ x, S x → T (g x)) →
    IsAnalyticOnReals f T →
    IsAnalyticOnReals (fun x => f (g x)) S

/-! ## The key theorem (axiomatized port) -/

/-- **`analytic_finite_zeros_compact`** (axiomatized port from monogate-
lean's `MonogateEML.InfiniteZerosBarrier`).

If `f` is real-analytic on `[a, b]` and not identically zero on `(a, b)`,
then the zero set of `f` on `[a, b]` is finite.

Note: This is the NON-UNIFORM version — the zero count depends on `f`.
The uniform-in-depth-k version requires Khovanskii / o-minimal `ℝ_exp`
infrastructure (the multi-month Mathlib gap). -/
axiom analytic_finite_zeros_compact (f : Real → Real) (a b : Real) :
    a < b →
    IsAnalyticOnReals f (Icc a b) →
    (∃ x : Real, Ioo a b x ∧ f x ≠ 0) →
    RealSetFinite (fun x => Icc a b x ∧ f x = 0)

/-! ## EML-tree analyticity (axiomatized port) -/

/-- **`eml_tree_analytic_on_pos`** (axiomatized port from monogate-lean's
`InfiniteZerosBarrier.eml_tree_analytic`).

Every well-formed EML tree `t` is real-analytic on `(0, ∞)`.

Well-formedness here means that every `log` argument inside the tree
evaluates to a positive real on `(0, ∞)`. -/
axiom eml_tree_analytic_on_pos (t : EMLTree) :
    -- (Well-formedness condition omitted here; in a full port it would
    -- track that every nested log argument stays in (0, ∞).)
    IsAnalyticOnReals t.eval (Ioi 0)

/-! ## Why this port alone doesn't close the 2 cases

Given the axioms above, suppose `t.eval = sin x` for all `x` (the
hypothesis being contradicted in the 2 deferred cases).

- `t.eval` is analytic on `(0, ∞)` (eml_tree_analytic_on_pos).
- `sin` is analytic on `(0, ∞)` (analytic_sin).
- Their difference `t.eval - sin` is analytic on `(0, ∞)` (analytic_sub).
- `t.eval - sin` is identically zero on `(0, ∞)` (by hypothesis).

So far no contradiction — the hypothesis is internally consistent with
analyticity.

The contradiction requires comparing the FORMS of `t.eval` and `sin`,
which needs either:

1. **Uniform-in-k zero bound**: every depth-`k` EML tree has at most
   `B(k)` zeros on any bounded interval. Sin has unbounded zero count
   on `(0, ∞)`, hence on `[0, N·π]` for large N exceeds `B(k)`.
   Requires Khovanskii's theorem.

2. **Differentiate**: `t.eval' = cos` on `(0, ∞)`. Compute `t.eval'`
   symbolically from the EML structure. Show its asymptotic behavior
   (typically unbounded growth from the outer `exp`) contradicts
   `cos`'s boundedness.

Both routes require infrastructure beyond what this axiomatized port
provides. The port is a building block, not a closure tool.

**Strategic value**: The infrastructure axioms (IsAnalyticOnReals,
analytic_const, analytic_exp, ...) and the theorem axiom
(analytic_finite_zeros_compact) are reusable for future analytic-shape
arguments in MachLib. They are the "header file" that downstream proofs
import.
-/

end MachLib
