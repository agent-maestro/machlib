import MachLib.PfaffianGeneralBoundUncond
import MachLib.Exp
namespace MachLib.PfaffianGeneralReduce
open MachLib.Real MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly MachLib.PfaffianChainMod
open MachLib.IterExpTopIdentity

/-- **A concrete exp-type Pfaffian chain** (both levels `= exp`, relations `1·yᵢ`). The simplest witness
that the general bound's hypotheses are inhabited: coherent (`yᵢ' = yᵢ = exp`), exponential-type
(`Gᵢ = const 1`), and positive (`exp > 0`). -/
noncomputable def uniExpChain : PfaffianChain 2 :=
  { evals := fun _ => Real.exp,
    relations := fun i => MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i) }

theorem uniExpChain_isExp : IsExpChain uniExpChain := by
  intro i
  refine ⟨⟨MultiPoly.const 1, degreeY_const i 1, rfl⟩, ?_⟩
  intro j hij
  show MultiPoly.degreeY j (MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)) = 0
  rw [degreeY_mul' j (MultiPoly.const 1) (MultiPoly.varY i), degreeY_const]
  have hij' : i ≠ j := fun h => (Nat.ne_of_lt hij) (congrArg Fin.val h)
  show 0 + (if j = i then 1 else 0) = 0
  rw [if_neg (Ne.symm hij')]

theorem uniExpChain_coh (a b : Real) : uniExpChain.IsCoherentOn a b := by
  intro x _ _ i
  show HasDerivAt Real.exp
    (MultiPoly.eval (MultiPoly.mul (MultiPoly.const 1) (MultiPoly.varY i)) x (uniExpChain.chainValues x)) x
  rw [MultiPoly.eval_mul, MultiPoly.eval_const, MultiPoly.eval_varY]
  show HasDerivAt Real.exp (1 * Real.exp x) x
  rw [one_mul_thm]
  exact HasDerivAt_exp x

theorem uniExpChain_pos (a b : Real) :
    ∀ z, a < z → z < b → ∀ i : Fin 2, 0 < uniExpChain.evals i z := by
  intro z _ _ _
  exact exp_pos z

/-- **NON-VACUITY: the general Khovanskii bound applied to a concrete chain.** The hypotheses of
`pfaffian_khovanskii_bound_gen_uncond` are inhabited — so the theorem is not vacuously true. For the concrete
exp-type chain `uniExpChain`, any `p` not identically vanishing on `(a,b)` has finitely many zeros there.
Inherits `rolle` as the sole analytic axiom. -/
theorem uniExpChain_khovanskii (a b : Real) (hab : a < b) (p : MultiPoly 2)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn uniExpChain p).eval z ≠ 0) :
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn uniExpChain p).eval z = 0) → zeros.length ≤ N :=
  pfaffian_khovanskii_bound_gen_uncond a b hab 0 uniExpChain uniExpChain_isExp
    (uniExpChain_coh a b) (uniExpChain_pos a b) p hne

end MachLib.PfaffianGeneralReduce
