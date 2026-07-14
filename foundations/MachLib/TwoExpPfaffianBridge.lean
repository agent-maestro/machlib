import MachLib.TwoExpCurveCount
import MachLib.TwoExpArcCount
import MachLib.PfaffianGeneralBoundUncond

/-!
# Pfaffian count bounds as two-exp lower-level inputs

The two-exp Khovanskii-Rolle layer asks for list bounds in a very specific
shape:

* `hJ_bound`: every nodup list of Jacobian zeros has length `≤ N`;
* `hNcrit`: every nodup list of critical/separator points has length `≤ Ncrit`.

The general positive-coherent Pfaffian theorem already produces zero-count
bounds for one-variable Pfaffian-chain functions. This file is the small
adapter layer: if a predicate implies the vanishing of a represented
Pfaffian-chain function on `(a,b)`, then the Pfaffian zero-count theorem
supplies exactly the list-bound shape the two-exp assembly consumes.

No topology and no Mathlib dependency are introduced here. The remaining
mathematical bridge is representation: showing that a concrete lower-level
Jacobian/critical expression is represented by the chosen Pfaffian chain.
-/

namespace MachLib
namespace MultiVarMod
namespace TwoExp

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce

/-- **Predicate-list bound from a Pfaffian representation.** If every point
satisfying `P` on `(a,b)` is a zero of the Pfaffian-chain function represented
by `(c,p)`, then the positive-coherent Pfaffian Khovanskii theorem supplies a
finite bound for every nodup list of `P`-points.

This is the generic adapter behind both lower-level two-exp inputs:
Jacobian-zero bounds and critical/separator-point bounds. -/
theorem pfaffian_predicate_count_bridge (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2)) (p : MultiPoly (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0)
    (P : Real → Prop)
    (hP_zero : ∀ z, a < z → z < b → P z → (pfaffianChainFn c p).eval z = 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ P z) → zeros.length ≤ N := by
  obtain ⟨N, hN⟩ := pfaffian_khovanskii_bound_gen_uncond a b hab M c hexp hcoh hpos p hne
  refine ⟨N, ?_⟩
  intro zeros hnd hz
  exact hN zeros hnd (fun z hzmem => by
    obtain ⟨hza, hzb, hPz⟩ := hz z hzmem
    exact ⟨hza, hzb, hP_zero z hza hzb hPz⟩)

/-- **Jacobian-bound adapter.** A Pfaffian representation of the lower-level
Jacobian vanishing predicate yields the `hJ_bound` shape used by
`khovanskii_rolle_count` / `khovanskii_rolle_count_curve`. -/
theorem pfaffian_jacobian_count_bridge (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2)) (p : MultiPoly (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0)
    (fx fy gx gy : Real → Real)
    (hJ_zero : ∀ z, a < z → z < b →
      fx z * gy z - fy z * gx z = 0 → (pfaffianChainFn c p).eval z = 0) :
    ∃ N : Nat, ∀ zeros_J : List Real, zeros_J.Nodup →
      (∀ z ∈ zeros_J, a < z ∧ z < b ∧ fx z * gy z - fy z * gx z = 0) →
      zeros_J.length ≤ N :=
  pfaffian_predicate_count_bridge a b hab M c p hexp hcoh hpos hne
    (fun z => fx z * gy z - fy z * gx z = 0)
    (fun z hza hzb hJ => hJ_zero z hza hzb hJ)

/-- **Critical/separator-bound adapter.** A Pfaffian representation of a
separator predicate yields the `hNcrit` shape consumed by
`khovanskii_rolle_full`, after `arc_count_le` turns critical separators into
an arc-count bound. -/
theorem pfaffian_separator_count_bridge (a b : Real) (hab : a < b)
    (M : Nat) (c : PfaffianChain (M + 2)) (p : MultiPoly (M + 2))
    (hexp : IsExpChain c)
    (hcoh : c.IsCoherentOn a b)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0)
    (sep : Real → Prop)
    (hsep_zero : ∀ z, a < z → z < b → sep z → (pfaffianChainFn c p).eval z = 0) :
    ∃ Ncrit : Nat, ∀ ss : List Real, ss.Nodup →
      (∀ s ∈ ss, a < s ∧ s < b ∧ sep s) → ss.length ≤ Ncrit :=
  pfaffian_predicate_count_bridge a b hab M c p hexp hcoh hpos hne sep hsep_zero

end TwoExp
end MultiVarMod
end MachLib
