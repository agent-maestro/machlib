import MachLib.PfaffianGeneralReduce
import MachLib.IterExpDepthNCapstone

/-!
# Generalize — WF assembly (layer v) for arbitrary exponential-type Pfaffian chains

The measure/order infrastructure `chainNMeasure5` / `chainNOrder5` / `chainNOrder5_wf` and the trim
descents (`chainN_degreeYtop_trim_order5`, `innerTrimN_order5`) are **chain-agnostic** — pure polynomial
facts (`IterExpDepthNCapstone` mentions no chain). So the general WF assembly reuses them verbatim; the
only chain-specific measure piece is the reduce arm's M5 descent, which this file supplies by wiring the
general layer (i) syntactic descent (`chainReduce_syntactic_descent_gen`) to the general layer (iii)
recursion (`chainReduce_descends_gen`).

Everything here is conditional on the single-exponential depth-2 base descent `hBase` (the remaining
sub-arc). What is NOT yet ported: the chain-function eval helpers (`chainNFn_*`) that relate the zeros of
`(pfaffianChainFn c p).eval` across trim/reduce — those need the general chain's coherence and are the
next block of layer (v).
-/

namespace MachLib.PfaffianGeneralReduce

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpDepthN
open MachLib.IterExpDepth3CdegY1
open MachLib.ChainExp2CanonMeasure

/-- **Layer (v-a): the general reduce's `chainNMeasureCanon` descent.** The layer (i) syntactic descent
(`chainReduce_syntactic_descent_gen`, top `y`-degree ties, inner measure drops) lifted by the layer (iii)
inner recursion (`chainReduce_descends_gen`), which supplies the inner `chainNMeasureEI` drop. The
multiplier is existential — built from the exp-type factor `G` over the lifted sub-level multiplier.
`chainNMeasureCanon M p = (degreeY_top p, chainNMeasureEI M (dropLastY (lcY_top p)))`, so the syntactic
descent's conclusion IS this after `simp`. Conditional on the depth-2 base `hBase`. -/
theorem chainReduce_orderCanon_gen
    (hBase : ∀ (c : PfaffianChain 2), IsExpChain c → ∀ (q : MultiPoly 2), ReducingGen 0 q →
      ∃ m : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) m = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c m q)) (chainNMeasureEI 0 q))
    {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c) (p : MultiPoly (M + 3))
    (hred : ReducingGen M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    ∃ m : MultiPoly (M + 3), MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0 ∧
      nestedOrder (M + 3) (chainNMeasureCanon M (chainReduce c m p)) (chainNMeasureCanon M p) := by
  obtain ⟨⟨G, hG, hrel⟩, htri⟩ := IsExpChain_top c hexp
  obtain ⟨m', hm'0, hm'desc⟩ := chainReduce_descends_gen hBase M (chainRestrict c)
    (IsExpChain_chainRestrict c hexp)
    (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p)) hred
  refine ⟨gradedMultStep G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m'),
    gradedMultStep_degreeY_top_zero G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m') hG
      (MultiPoly.degreeY_top_liftLastY m'), ?_⟩
  have hInner : nestedOrder (M + 2)
      (chainNMeasureEI M (chainReduce (chainRestrict c) (MultiPoly.dropLastY (MultiPoly.liftLastY m'))
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))))
      (chainNMeasureEI M (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) := by
    rw [MultiPoly.dropLastY_liftLastY]; exact hm'desc
  show nestedOrder (M + 3)
    (chainNMeasureCanon M (chainReduce c (gradedMultStep G (⟨M + 2, by omega⟩ : Fin (M + 3)) p (MultiPoly.liftLastY m')) p))
    (chainNMeasureCanon M p)
  simp only [chainNMeasureCanon]
  exact chainReduce_syntactic_descent_gen c G hrel hG htri (MultiPoly.liftLastY m') p
    (MultiPoly.degreeY_top_liftLastY m') hInner

/-- **Layer (v-a′): the general reduce's `M5` descent.** Lifts the `chainNMeasureCanon` drop to the
augmented measure `chainNMeasure5 = (chainNMeasureCanon, degreeY_{top-1}(lcY_top ·))` by dropping the
first component (`lexProd_of_fst`) — the exact reuse of `chainNReduce_order5`'s pattern, now for a general
exp-type chain. This is the reduce arm the general WF induction will dispatch. -/
theorem chainReduce_order5_gen
    (hBase : ∀ (c : PfaffianChain 2), IsExpChain c → ∀ (q : MultiPoly 2), ReducingGen 0 q →
      ∃ m : MultiPoly 2, MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) m = 0 ∧
        nestedOrder 2 (chainNMeasureEI 0 (chainReduce c m q)) (chainNMeasureEI 0 q))
    {M : Nat} (c : PfaffianChain (M + 3)) (hexp : IsExpChain c) (p : MultiPoly (M + 3))
    (hred : ReducingGen M (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨M + 2, by omega⟩ : Fin (M + 3)) p))) :
    ∃ m : MultiPoly (M + 3), MultiPoly.degreeY (⟨M + 2, by omega⟩ : Fin (M + 3)) m = 0 ∧
      chainNOrder5 M (chainReduce c m p) p := by
  obtain ⟨m, hm0, hdesc⟩ := chainReduce_orderCanon_gen hBase c hexp p hred
  exact ⟨m, hm0, lexProd_of_fst hdesc⟩

/-! ## Layer (v) chain-function side — the analytic core

The measure side above is chain-agnostic + wired. The chain-FUNCTION side relates the zeros of
`(pfaffianChainFn c p).eval` across the reduce/trim moves. The shared analytic foundation is the
reduce-eval identity below; the no-zeros arm's integrating factor for an exp-type chain is the monomial
`Π yᵢ^{degᵢ}` in the chain values (since `Gᵢ = yᵢ'/yᵢ`), the general analog of the iterated-exp `vehExpo`. -/

/-- **General reduce-eval identity.** The reduce, evaluated along the chain, is `f' − (m·f)` — the
`f' − M·f` that the Rolle transfer (reduce arm) and the vehicle no-zeros argument both count. Defeq-trivial:
`chainReduce = cTD − m·p` and `(pfaffianChainFn c p).chainTotalDerivative = pfaffianChainFn c (chainTotalDeriv c p)`
by definition, so this is `eval_sub` + `eval_mul`. Chain-agnostic (holds for ANY Pfaffian chain). -/
theorem pfaffianChainFn_reduce_eval {n : Nat} (c : PfaffianChain n) (m p : MultiPoly n) (z : Real) :
    (pfaffianChainFn c (chainReduce c m p)).eval z
    = (pfaffianChainFn c p).chainTotalDerivative.eval z
      - (pfaffianChainFn c m).eval z * (pfaffianChainFn c p).eval z := by
  show MultiPoly.eval (chainReduce c m p) z (c.chainValues z)
    = MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
      - MultiPoly.eval m z (c.chainValues z) * MultiPoly.eval p z (c.chainValues z)
  unfold chainReduce
  rw [MultiPoly.eval_sub, MultiPoly.eval_mul]

end MachLib.PfaffianGeneralReduce
