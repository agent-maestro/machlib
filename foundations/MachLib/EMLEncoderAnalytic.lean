import MachLib.EMLEncoder
import MachLib.PfaffianAnalytic

/-!
# The encoder's chain is analytic — completing the `hAnalytic` obligation

`PfaffianAnalytic` reduced the descent's `hAnalytic` (`∀ r,
IsAnalyticOnReals (pfaffianChainFn c r).eval S`) to a single obligation: **each
chain value `c.evals i` is analytic on `S`**. This file discharges it for the
encoder's chain `enc t chain`.

Each `eml` node adds three functions on top of the chain: `1/⟦t2⟧` (reciprocal),
`log⟦t2⟧`, `exp⟦t1⟧`. `exp∘poly` and `log∘poly` / `1/poly` are analytic by
`analytic_comp` with `analytic_exp` / `analytic_log_pos` / `analytic_one_div_pos`
— but `log` and `1/·` are only analytic on `(0, ∞)`, so their arguments must stay
positive. That is exactly `⟦t2⟧ > 0`, tracked by `LogArgPosOn` (the RealSet
analogue of `LogArgPos`). Positivity of `⟦t2⟧` reaches each node through the
`enc_encLift_eval` / `stepCC_liftLastY_eval` bridges.

`enc_hAnalytic` is the payoff: `enc`'s chain feeds `hAnalytic` directly, on any
set `S` where the context chain is analytic and every log-argument is positive.

No new axioms here (`analytic_mul`/`analytic_one_div_pos` live in
`AnalyticFiniteZeros`).
-/

namespace MachLib

open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
  MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain
  MachLib.PfaffianChainMod.PfaffianFn MachLib.PfaffianGeneralReduce

/-- **`chainExtend` preserves evals-analyticity.** If every chain value of `c` is
analytic on `S` and the new top function `ne` is analytic on `S`, then every
chain value of `chainExtend c ne nr` is analytic on `S` (relations irrelevant). -/
theorem chainExtend_evals_analytic {n : Nat} (c : PfaffianChain n) (ne : Real → Real)
    (nr : MultiPoly (n + 1)) (S : RealSet)
    (hc : ∀ i, IsAnalyticOnReals (fun x => c.evals i x) S)
    (hne : IsAnalyticOnReals ne S) :
    ∀ i : Fin (n + 1), IsAnalyticOnReals (fun x => (chainExtend c ne nr).evals i x) S := by
  intro i
  by_cases h : i.val < n
  · rw [chainExtend_evals_of_lt c ne nr i h]
    exact hc ⟨i.val, h⟩
  · have hval : i.val = n := by omega
    have hi : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hval
    rw [hi, chainExtend_evals_last c ne nr]
    exact hne

/-- **The eml step's chain is analytic.** Given `cb`'s chain values analytic on
`S` and the log-argument `⟦t2⟧` (`= eval w` along `cb`) positive on `S`, every
chain value of `encEmlStepR cb b1 w` is analytic on `S`. Builds up node by node
(recip → log → exp), mirroring `encEmlStepR_isCoherentOn`. -/
theorem encEmlStepR_evals_analytic {M : Nat} (cb : PfaffianChain M) (b1 w : MultiPoly M)
    (S : RealSet)
    (hcbev : ∀ i, IsAnalyticOnReals (fun x => cb.evals i x) S)
    (hwpos : ∀ x, S x → 0 < MultiPoly.eval w x (cb.chainValues x)) :
    ∀ i, IsAnalyticOnReals (fun x => (encEmlStepR cb b1 w).evals i x) S := by
  -- reciprocal node: `1/⟦t2⟧`
  have hwan : IsAnalyticOnReals (fun x => MultiPoly.eval w x (cb.chainValues x)) S :=
    poly_eval_analytic S (fun x => cb.chainValues x) hcbev w
  have hrecip : IsAnalyticOnReals
      (fun y => 1 / MultiPoly.eval w y (cb.chainValues y)) S :=
    analytic_comp (fun z => 1 / z) _ S (Ioi 0) hwan (fun x hx => hwpos x hx) analytic_one_div_pos
  have hccev : ∀ i, IsAnalyticOnReals (fun x => (stepCC cb w).evals i x) S := by
    simp only [stepCC]
    exact chainExtend_evals_analytic cb _ _ S hcbev hrecip
  -- log node: `log⟦t2⟧`, argument positive via `stepCC_liftLastY_eval`
  have hloginner : IsAnalyticOnReals
      (fun y => MultiPoly.eval (MultiPoly.liftLastY w) y ((stepCC cb w).chainValues y)) S :=
    poly_eval_analytic S (fun x => (stepCC cb w).chainValues x) hccev (MultiPoly.liftLastY w)
  have hlogpos : ∀ x, S x →
      0 < MultiPoly.eval (MultiPoly.liftLastY w) x ((stepCC cb w).chainValues x) := by
    intro x hx; rw [stepCC_liftLastY_eval cb w x]; exact hwpos x hx
  have hlog : IsAnalyticOnReals
      (fun y => Real.log (MultiPoly.eval (MultiPoly.liftLastY w) y ((stepCC cb w).chainValues y)))
      S :=
    analytic_comp Real.log _ S (Ioi 0) hloginner (fun x hx => hlogpos x hx) analytic_log_pos
  have hcdev : ∀ i, IsAnalyticOnReals (fun x => (stepCD cb w).evals i x) S := by
    simp only [stepCD]
    exact chainExtend_evals_analytic (stepCC cb w) _ _ S hccev hlog
  -- exp node: `exp⟦t1⟧`, no positivity needed
  have hexpinner : IsAnalyticOnReals
      (fun y => MultiPoly.eval (liftLastYBy 2 b1) y ((stepCD cb w).chainValues y)) S :=
    poly_eval_analytic S (fun x => (stepCD cb w).chainValues x) hcdev (liftLastYBy 2 b1)
  have hexp : IsAnalyticOnReals
      (fun y => Real.exp (MultiPoly.eval (liftLastYBy 2 b1) y ((stepCD cb w).chainValues y)))
      S :=
    analytic_comp Real.exp _ S (fun _ => True) hexpinner (fun _ _ => trivial)
      (analytic_exp (fun _ => True))
  simp only [encEmlStepR]
  exact chainExtend_evals_analytic (stepCD cb w) _ _ S hcdev hexp

/-- The genuine positivity side-condition on a set `S` (RealSet analogue of
`LogArgPos`): every `eml` node's log argument `⟦t2⟧` is positive on `S`. -/
def LogArgPosOn : EMLTree → RealSet → Prop
  | .const _, _ => True
  | .var,     _ => True
  | .eml t1 t2, S => LogArgPosOn t1 S ∧ LogArgPosOn t2 S ∧ (∀ x, S x → 0 < t2.eval x)

/-- **The encoder's chain values are analytic.** If the context chain is analytic
on `S` and every log-argument stays positive there (`LogArgPosOn`), each chain
value of `enc t chain` is analytic on `S`. Leaves reuse the context; each `eml`
node is `encEmlStepR_evals_analytic` with `cb` = the (inductively analytic) `t1`
sub-chain and positivity via `enc_eval`. -/
theorem enc_evals_analytic (t : EMLTree) :
    ∀ {N : Nat} (chain : PfaffianChain N) (S : RealSet),
      (∀ i, IsAnalyticOnReals (fun x => chain.evals i x) S) →
      LogArgPosOn t S →
      ∀ i, IsAnalyticOnReals (fun x => (enc t chain).1.evals i x) S := by
  induction t with
  | const c => intro N chain S hchain _ i; exact hchain i
  | var => intro N chain S hchain _ i; exact hchain i
  | eml t1 t2 ih1 ih2 =>
    intro N chain S hchain hpos
    obtain ⟨hpos1, hpos2, hposLog⟩ := hpos
    have hcbev := ih1 (enc t2 chain).1 S (ih2 chain S hchain hpos2) hpos1
    have hwpos : ∀ x, S x → 0 < MultiPoly.eval (encLift t1 (enc t2 chain).2) x
        ((enc t1 (enc t2 chain).1).1.chainValues x) := by
      intro x hx
      rw [enc_encLift_eval t1 t2 chain x (t2.eval x) (enc_eval t2 chain x)]
      exact hposLog x hx
    show ∀ i, IsAnalyticOnReals (fun x =>
      (encEmlStepR (enc t1 (enc t2 chain).1).1 (enc t1 (enc t2 chain).1).2
        (encLift t1 (enc t2 chain).2)).evals i x) S
    exact encEmlStepR_evals_analytic (enc t1 (enc t2 chain).1).1
      (enc t1 (enc t2 chain).1).2 (encLift t1 (enc t2 chain).2) S hcbev hwpos

/-- **The encoder feeds `hAnalytic`.** Every Pfaffian function `pfaffianChainFn
(enc t chain).1 r` is analytic on `S`, given the context chain analytic on `S`
and `LogArgPosOn t S`. This is exactly the `∀ r`-hypothesis of
`log_step_multilinear_analytic` (instantiate `S := Icc a b`). -/
theorem enc_hAnalytic (t : EMLTree) {N : Nat} (chain : PfaffianChain N) (S : RealSet)
    (hchain : ∀ i, IsAnalyticOnReals (fun x => chain.evals i x) S)
    (hpos : LogArgPosOn t S) (r : MultiPoly (len t N)) :
    IsAnalyticOnReals (pfaffianChainFn (enc t chain).1 r).eval S :=
  pfaffianChainFn_eval_analytic (enc t chain).1 S (enc_evals_analytic t chain S hchain hpos) r

/-! ## Reconciling the two positivity predicates

`enc_isCoherentOn` takes `LogArgPos t a b` (curried open interval — natural for
`IsCoherentOn`, which is about interior derivatives) while `enc_hAnalytic` takes
`LogArgPosOn t (Icc a b)` (a RealSet — natural for `IsAnalyticOnReals`). Both
say "every log-argument stays positive"; the closed-interval form is the stronger
one and implies the open-interval form (`Ioo a b ⊆ Icc a b`), so a single
`LogArgPosOn t (Icc a b)` hypothesis feeds both. (`LogArgPos` stays in the pure
`EMLEncoder` file, free of the analytic imports; `LogArgPosOn` lives here — the
bridge is the price of that separation.) -/

/-- **Closed-interval positivity ⇒ open-interval positivity.** At every `eml`
node, log-arg positivity on the closed `Icc a b` restricts to the open `(a,b)`. -/
theorem LogArgPos_of_LogArgPosOn_Icc (a b : Real) :
    ∀ (t : EMLTree), LogArgPosOn t (Icc a b) → LogArgPos t a b := by
  intro t
  induction t with
  | const c => intro _; trivial
  | var => intro _; trivial
  | eml t1 t2 ih1 ih2 =>
      intro h
      obtain ⟨h1, h2, hlog⟩ := h
      exact ⟨ih1 h1, ih2 h2,
        fun x hxa hxb => hlog x ⟨Real.le_of_lt hxa, Real.le_of_lt hxb⟩⟩

/-- **The encoder's full contract, behind one positivity hypothesis.** On a
closed interval `Icc a b` where every log-argument is positive
(`LogArgPosOn t (Icc a b)`), over a context chain itself coherent on `(a,b)` and
analytic on `Icc a b`, the encoder's chain is BOTH coherent on `(a,b)` and
supplies the descent's `hAnalytic`. This is the single-hypothesis interface a
`combined_descent` integration consumes. -/
theorem enc_coherent_and_hAnalytic (t : EMLTree) {N : Nat} (chain : PfaffianChain N)
    (a b : Real)
    (hcoh : chain.IsCoherentOn a b)
    (han : ∀ i, IsAnalyticOnReals (fun x => chain.evals i x) (Icc a b))
    (hpos : LogArgPosOn t (Icc a b)) :
    (enc t chain).1.IsCoherentOn a b ∧
      ∀ r, IsAnalyticOnReals (pfaffianChainFn (enc t chain).1 r).eval (Icc a b) :=
  ⟨enc_isCoherentOn t chain a b hcoh (LogArgPos_of_LogArgPosOn_Icc a b t hpos),
   fun r => enc_hAnalytic t chain (Icc a b) han hpos r⟩

end MachLib
