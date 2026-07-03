import MachLib.IterExpDepthNMeasure5Plus
import MachLib.IterExpDepthNEstablishHnz
import MachLib.IterExpDepthNReduceOrder5Hnz
import MachLib.IterExpDepthNTrimArm

/-!
# Phase C→D absorption — the three `M5⁺` descents

The reduce and `degreeY_top`-trim drop `chainNMeasureCanon` (`M5⁺`'s first component, `lexProd_of_fst`); the
deep phantom-trim (`liftInner`) TIES `chainNMeasureCanon` and drops `synMeasure` (`lexProd_of_snd`). The tie
`chainNMeasureCanon_liftInner_eq` is the intricate one: the reconstructed leading coefficient carries a
power-unit factor that evaluates to `1` (`eval_dropLastY_powunit`), so `dropLastY(lcY_top(liftInner))` is
eval-equal to `q`, and `chainNMeasureEI` (eval-invariant) ties. No `sorry`.
-/

namespace MachLib.IterExpDepthN

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.MultiPolyMod.MultiPoly
open MachLib.IterExpDepth3InnerTrim
open MachLib.IterExpDepthNReduce
open MachLib.ChainExp2Trim
open MachLib.IterExpDepth3CdegY1

/-- **The reconstructY power-unit evaluates to `1` after `dropLastY`.** `leadingCoeffY_top (y_top^D)` is
`y`-free and evaluates to `1`; `dropLastY` (top-free) preserves that. -/
theorem eval_dropLastY_powunit (m : Nat) (D : Nat) (x : Real) (env' : Fin (m + 2) → Real) :
    MultiPoly.eval (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
      (MultiPoly.pow (MultiPoly.varY (⟨m + 2, by omega⟩ : Fin (m + 3))) D))) x env' = 1 := by
  have hrestrict : (fun i : Fin (m + 2) =>
      (fun j : Fin (m + 3) => if hj : j.val < m + 2 then env' ⟨j.val, hj⟩ else 0)
        ⟨i.val, by omega⟩) = env' := by
    funext i
    show (if hj : i.val < m + 2 then env' ⟨i.val, hj⟩ else 0) = env' i
    rw [dif_pos i.isLt]
  have e := MultiPoly.eval_dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
      (MultiPoly.pow (MultiPoly.varY (⟨m + 2, by omega⟩ : Fin (m + 3))) D))
      (MultiPoly.degreeY_leadingCoeffY _ _) x
      (fun j : Fin (m + 3) => if hj : j.val < m + 2 then env' ⟨j.val, hj⟩ else 0)
  rw [hrestrict] at e
  rw [e]
  exact leadingCoeffY_pow_self_eval (⟨m + 2, by omega⟩ : Fin (m + 3)) x _ D

/-- **The deep-trim ties `chainNMeasureCanon`.** `liftInner` preserves the syntactic top degree, and its
dropped leading coefficient is eval-equal to `q` (the power-unit evaluates to `1`), so the eval-invariant
inner measure is unchanged. -/
theorem chainNMeasureCanon_liftInner_eq (m : Nat) (p : MultiPoly (m + 3)) (q' : MultiPoly (m + 2))
    (hpos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
    (hq'_eval : ∀ (x : Real) (env : Fin (m + 2) → Real),
      MultiPoly.eval q' x env = MultiPoly.eval (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env) :
    chainNMeasureCanon m (liftInner m p q') = chainNMeasureCanon m p := by
  have hlc : MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
        (liftInner m p q'))
      = MultiPoly.mul q' (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
          (MultiPoly.pow (MultiPoly.varY (⟨m + 2, by omega⟩ : Fin (m + 3)))
            (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))) := by
    rw [leadingCoeffYtop_liftInner m p q' hpos]
    show MultiPoly.mul (MultiPoly.dropLastY (liftLastY q'))
        (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3))
          (MultiPoly.pow (MultiPoly.varY (⟨m + 2, by omega⟩ : Fin (m + 3)))
            (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))) = _
    rw [dropLastY_liftLastY]
  have hinner : chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
        (⟨m + 2, by omega⟩ : Fin (m + 3)) (liftInner m p q')))
      = chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
        (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) := by
    apply chainNMeasureEI_eq_of_eval_eq m
    intro x env
    rw [hlc, MultiPoly.eval_mul, hq'_eval x env, eval_dropLastY_powunit m
      (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) x env, MachLib.Real.mul_one_ax]
  show (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) (liftInner m p q'),
        chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
          (⟨m + 2, by omega⟩ : Fin (m + 3)) (liftInner m p q'))))
      = (MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p,
         chainNMeasureEI m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
          (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))
  rw [degreeYtop_liftInner m p q', hinner]

/-- **Reduce M5⁺-descent** — drops the first component (`chainNMeasureCanon`), via `lexProd_of_fst`. -/
theorem chainNReduce_order5p_hnz (m : Nat) (p : MultiPoly (m + 3))
    (hnz : hnzTower m (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) :
    chainNOrder5p m (chainNReduce (m + 1) (fullMult (m + 1) p) p) p :=
  lexProd_of_fst (chainNReduce_orderCanon_hnz m p hnz)

/-- **`degreeY_top`-trim M5⁺-descent** — drops the first component, via `lexProd_of_fst`. -/
theorem chainN_degreeYtop_trim_order5p (m : Nat) (p : MultiPoly (m + 3))
    (hd : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p) :
    chainNOrder5p m (dropLeadingYAt (⟨m + 2, by omega⟩ : Fin (m + 3)) p) p :=
  lexProd_of_fst (chainN_degreeYtop_trim_order m p hd)

/-- **Deep phantom-trim M5⁺-descent** — TIES the first component (`chainNMeasureCanon`) and drops the second
(`synMeasure`), via `lexProd_of_snd`. This is the descent that resolves the deep `¬hnzTower` case. -/
theorem liftInner_order5p (m : Nat) (p : MultiPoly (m + 3)) (q' : MultiPoly (m + 2))
    (hpos : 0 < MultiPoly.degreeY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)
    (hq'_eval : ∀ (x : Real) (env : Fin (m + 2) → Real),
      MultiPoly.eval q' x env = MultiPoly.eval (MultiPoly.dropLastY
        (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p)) x env)
    (hdrop : synOrder m q' (MultiPoly.dropLastY
      (MultiPoly.leadingCoeffY (⟨m + 2, by omega⟩ : Fin (m + 3)) p))) :
    chainNOrder5p m (liftInner m p q') p := by
  refine LexProd.lexProd_of_snd (chainNMeasureCanon_liftInner_eq m p q' hpos hq'_eval) ?_
  show nestedOrder (m + 2)
      (synMeasure m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
        (⟨m + 2, by omega⟩ : Fin (m + 3)) (liftInner m p q'))))
      (synMeasure m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
        (⟨m + 2, by omega⟩ : Fin (m + 3)) p)))
  rw [show synMeasure m (MultiPoly.dropLastY (MultiPoly.leadingCoeffY
        (⟨m + 2, by omega⟩ : Fin (m + 3)) (liftInner m p q'))) = synMeasure m q'
      from congrArg Prod.snd (synMeasure_liftInner m p q' hpos)]
  exact hdrop

end MachLib.IterExpDepthN
