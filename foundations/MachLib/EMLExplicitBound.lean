import MachLib.PfaffianExpRecipDescent
import MachLib.WronskianProportional

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

/-- **`degreeY_top = 0` arm, EXPLICIT.** When `p` does not depend on the top chain
variable, `pfaffianChainFn c p` collapses to the restricted chain's
`pfaffianChainFn (chainRestrict c) (dropLastY p)`, so its explicit bound is
exactly the depth-IH's explicit bound `Kih (dropLastY p)` — no increase. Threads
an explicit IH bound function `Kih` in place of the existential IH of
`pfaffianChainFn_bound_of_degreeYtop_zero`. -/
theorem degreeYtop_zero_explicit {N : Nat} (c : PfaffianChain (N + 1)) (p : MultiPoly (N + 1))
    (hd : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0) (a b : Real)
    (Kih : MultiPoly N → Nat)
    (IH_ex : ∀ q : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn (chainRestrict c) q) a b (Kih q))
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn c p) a b (Kih (MultiPoly.dropLastY p)) := by
  have heval : ∀ z, (pfaffianChainFn c p).eval z
      = (pfaffianChainFn (chainRestrict c) (MultiPoly.dropLastY p)).eval z := by
    intro z
    show MultiPoly.eval p z (c.chainValues z)
      = MultiPoly.eval (MultiPoly.dropLastY p) z ((chainRestrict c).chainValues z)
    have hrestrict : (chainRestrict c).chainValues z
        = (fun i => (c.chainValues z) ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) := by
      funext i; exact chainRestrict_chainValues c z i
    rw [hrestrict, MultiPoly.eval_dropLastY p hd z (c.chainValues z)]
  have hne_proj : ∃ z, a < z ∧ z < b
      ∧ (pfaffianChainFn (chainRestrict c) (MultiPoly.dropLastY p)).eval z ≠ 0 := by
    obtain ⟨z, hza, hzb, hzne⟩ := hne
    exact ⟨z, hza, hzb, by rw [← heval]; exact hzne⟩
  intro zeros hnd hz
  refine IH_ex (MultiPoly.dropLastY p) hne_proj zeros hnd (fun z' hz'mem => ?_)
  obtain ⟨ha, hb', hzero⟩ := hz z' hz'mem
  exact ⟨ha, hb', by rw [← heval]; exact hzero⟩

/-- **Wronskian degenerate-leaf arm, EXPLICIT.** When two analytic functions have
vanishing Wronskian (`Fp·G − F·Gp = 0`, i.e. proportional), every zero of `F` is a
zero of `G` (`wronskian_zero_zeros_subset`), so `F` inherits `G`'s explicit zero
bound `N` unchanged. This is the `∃`-free form of `wronskian_zero_bounded_zeros`
(which returns exactly `⟨N, …⟩`). -/
theorem wronskian_arm_explicit
    (F G Fp Gp : Real → Real) (a b : Real) (hab : a < b)
    (hFanalytic : IsAnalyticOnReals F (Icc a b))
    (hGanalytic : IsAnalyticOnReals G (Icc a b))
    (hFderiv : ∀ x, a < x → x < b → HasDerivAt F (Fp x) x)
    (hGderiv : ∀ x, a < x → x < b → HasDerivAt G (Gp x) x)
    (hW : ∀ x, a < x → x < b → Fp x * G x - F x * Gp x = 0)
    (hFne : ∃ x, Ioo a b x ∧ F x ≠ 0)
    (N : Nat)
    (hGbound : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ G z = 0) → zeros.length ≤ N) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ F z = 0) → zeros.length ≤ N := by
  intro zeros hnd hz
  refine hGbound zeros hnd (fun z hzm => ?_)
  obtain ⟨hza, hzb, hFz⟩ := hz z hzm
  exact ⟨hza, hzb,
    wronskian_zero_zeros_subset F G Fp Gp a b hab hFanalytic hGanalytic
      hFderiv hGderiv hW hFne z hza hzb hFz⟩

end EMLExplicitBound
end MachLib
