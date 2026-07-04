import MachLib.PfaffianGeneralBound2
import MachLib.PfaffianGeneralHnzWF
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.PfaffianChainMod MachLib.MultiPolyMod
open MachLib.PfaffianGeneralVehExpo

/-- **Positivity is preserved under `chainRestrict`.** The restricted chain's values are a prefix of the
full chain's, so `yᵢ>0` on `(a,b)` descends. -/
theorem positivity_chainRestrict {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real)
    (hpos : ∀ z, a < z → z < b → ∀ i : Fin (N + 1), 0 < c.evals i z) :
    ∀ z, a < z → z < b → ∀ i : Fin N, 0 < (chainRestrict c).evals i z := by
  intro z hza hzb i
  show 0 < c.evals ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ z
  exact hpos z hza hzb ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩

set_option maxHeartbeats 800000 in
/-- **The general Khovanskii bound for POSITIVE-COHERENT exp-chains — hBaseHnz + hBound2 discharged.**
`pfaffian_khovanskii_bound_hnz_gen` with its depth-2 base (`hBound2`, now `pfaffian_bound2_gen`) and its reduce
base (`hBaseHnz`, now `pfaffian_base_hnz_gen`) supplied internally. Conditional on ONLY `hIF_glob` (the
integrating factors) plus positive coherence (`yᵢ>0`, threaded through `chainRestrict`). Induction on the
extra depth `M`: base `M=0` is `pfaffian_bound2_gen`; step is `pfaffian_bound_step_hnz_gen` fed
`pfaffian_base_hnz_gen`, `hIF_glob`, and the depth-below IH on `chainRestrict c`. -/
theorem pfaffian_khovanskii_bound_gen_pos (a b : Real) (hab : a < b)
    (hIF_glob : ∀ (d : Nat) (c' : PfaffianChain d) (mm : MultiPoly d),
        ∃ E : Real → Real, ∀ z, a < z → z < b → HasDerivAt E (-(pfaffianChainFn c' mm).eval z) z) :
    ∀ (M : Nat) (c : PfaffianChain (M + 2)), IsExpChain c → c.IsCoherentOn a b →
      (∀ z, a < z → z < b → ∀ i : Fin (M + 2), 0 < c.evals i z) →
      ∀ (p : MultiPoly (M + 2)), (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ N := by
  intro M
  induction M with
  | zero =>
    intro c hexp hcoh hpos p hne
    exact pfaffian_bound2_gen c hexp a b hab hcoh hpos p hne
  | succ M ih =>
    intro c hexp hcoh hpos p hne
    exact pfaffian_bound_step_hnz_gen c hexp a b hab hcoh pfaffian_base_hnz_gen (hIF_glob (M + 3) c)
      (ih (chainRestrict c) (IsExpChain_chainRestrict c hexp)
        (chainRestrict_isCoherentOn c hexp a b hcoh)
        (positivity_chainRestrict c a b hpos)) p hne

end MachLib.PfaffianGeneralReduce
