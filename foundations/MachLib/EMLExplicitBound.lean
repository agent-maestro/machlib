import MachLib.PfaffianExpRecipDescent

/-!
# MachLib.EMLExplicitBound — explicit/uniform-K descent, brick 1 (base case)

Foundation for the interval-UNIFORM Khovanskii bound the axiom deletion needs.
`eml_eval_boundedZeros_unconditional` is `#print axioms`-clean but its
`BoundedZeros` conclusion is `∃K` **per interval** — too weak for
`sin/cos_not_in_eml`, which need a bound independent of the interval (with
`∃K(a,b)`, sin's `⌊b/π⌋` zeros are merely `≤ K(b)` — no contradiction).

This module introduces `BoundedZerosBy f a b K` — the explicit-bound predicate
(bound is a named `Nat`, so when it depends only on the chain it is
interval-independent) — and discharges the **base case** explicitly: a depth-0
chain function is a univariate polynomial, bounded by its syntactic degree
`degreeUpper (mpoly0ToPoly p)`, which does not mention `(a, b)`.

This is brick 1 of the explicit-K refactor (AXIOM_AUDIT_V2.md §2c(2)). Remaining:
the reciprocal / exp / log arms and the composition (`combined_descent_*`) need
explicit-bound versions that accumulate the per-step Rolle counts, after which
`sin/cos_not_in_eml` can drop `PfaffianFunction.zero_bound` and the axiom is deleted.
-/

namespace MachLib
namespace EMLExplicitBound

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PolynomialEvidence
open MachLib.PolynomialRootCount
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpRecip
open MachLib.PfaffianExpRecipW

/-- Explicit-bound form of `PfaffianExpRecipW.BoundedZeros`: at most `K` zeros on
`(a, b)`, with `K` a named `Nat`. When `K` depends only on the chain (not the
interval), this is interval-independent — the property `sin/cos_not_in_eml` need. -/
def BoundedZerosBy (f : PfaffianFn) (a b : Real) (K : Nat) : Prop :=
  ∀ zeros : List Real, zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ f.eval z = 0) → zeros.length ≤ K

/-- An explicit bound gives the existential `BoundedZeros` (forgetting `K`). -/
theorem BoundedZerosBy.toBoundedZeros {f : PfaffianFn} {a b : Real} {K : Nat}
    (h : BoundedZerosBy f a b K) : BoundedZeros f a b :=
  ⟨K, h⟩

/-- **Base case, EXPLICIT.** A depth-0 chain function `pfaffianChainFn c p`
(`c : PfaffianChain 0`) is the univariate polynomial `mpoly0ToPoly p`, so — given
it is not identically zero (`hne`) — its zero count on `(a, b)` is
`≤ degreeUpper (mpoly0ToPoly p)`, a bound built from `p`'s syntactic degree ALONE,
with no dependence on the interval `(a, b)`. Same content as `base_case`, but with
the bound exposed as a named `Nat`. -/
theorem base_case_explicit (a b : Real) (hab : a < b) (c : PfaffianChain 0) (p : MultiPoly 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn c p) a b (degreeUpper (mpoly0ToPoly p)) := by
  intro zeros hnd hz
  have hbridge : ∀ z : Real, (pfaffianChainFn c p).eval z = Poly.eval (mpoly0ToPoly p) z :=
    fun z => mpoly0_eval p z (c.chainValues z)
  refine poly_root_count_bound (mpoly0ToPoly p) a b hab ?_ zeros hnd ?_
  · obtain ⟨z, _, _, hne0⟩ := hne
    exact ⟨z, by rw [← hbridge z]; exact hne0⟩
  · intro z hzmem
    obtain ⟨ha, hb, hz0⟩ := hz z hzmem
    exact ⟨ha, hb, by rw [← hbridge z]; exact hz0⟩

/-- The explicit base case refines the existential `base_case`. -/
theorem base_case_of_explicit (a b : Real) (hab : a < b) (c : PfaffianChain 0) (p : MultiPoly 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    BoundedZeros (pfaffianChainFn c p) a b :=
  (base_case_explicit a b hab c p hne).toBoundedZeros

/-- **Reciprocal arm, EXPLICIT — for free.** The reciprocal top step is
bound-*preserving*: `recip_top_combined` already threads an explicit `K` from the
cleared/restricted problem to the original with NO increase (a reciprocal top
creates no new zeros; the cleared numerator `= v^d · p` has the same zeros where
`v > 0`). So the reciprocal arm carries the explicit uniform bound through
unchanged — no re-proof needed for the explicit-K refactor. -/
theorem recip_arm_explicit {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (v : MultiPoly (N + 1))
    (hvtf : ∀ j : Fin (N + 1), N ≤ j.val → MultiPoly.degreeY j v = 0)
    (hvcoh : ∀ x : Real, a < x → x < b →
        c.evals ⟨N, Nat.lt_succ_self N⟩ x * MultiPoly.eval v x (c.chainValues x) = 1)
    (hvpos : ∀ x : Real, a < x → x < b → 0 < MultiPoly.eval v x (c.chainValues x))
    (p : MultiPoly (N + 1)) (K : Nat)
    (hK : BoundedZerosBy
        (pfaffianChainFn (chainRestrict c) (clearTop (MultiPoly.dropLastY v) p)) a b K) :
    BoundedZerosBy (pfaffianChainFn c p) a b K :=
  recip_top_combined c a b v hvtf hvcoh hvpos p K hK

end EMLExplicitBound
end MachLib
