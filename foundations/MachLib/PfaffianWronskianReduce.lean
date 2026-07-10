import MachLib.PfaffianGeneralWF
import MachLib.FieldLemmas

/-!
# One Wronskian-reduce lemma for both the exp and log arms

The exp arm (`PfaffianExpWronskian.expEliminate_reduce_full`) and the log arm
(`PfaffianLogWronskian.log_wronskian_reduce_full`) were built independently, yet their proofs are the same
`zero_count_bound_by_deriv_with_bad` skeleton with a reciprocal vehicle. This file extracts that common core
as **one lemma parametrized by the derivation rule**, and both arms become thin instantiations.

The single count:

> On `(a,b)`, `#zeros(pfaffianChainFn c p) ≤ #zeros(pf c E) + #zeros(c_D) + 1`,   `c_D := leadingCoeffY top p`,

whenever there is a vehicle denominator `V`, an elimination polynomial `E`, and a nowhere-zero cofactor `W`
tied by the **Wronskian numerator identity**

> `V·(cTD p) − (cTD V)·p  =  W·E`     (as polynomials, at every point),

with `V` nonzero wherever `c_D` is. The mechanism: the reciprocal vehicle `f·(1/V)` has
`(f/V)' = (f'·V − f·V')/V² = (W·E)/V²`, so off the bad set `{c_D = 0}` its critical points are exactly the
zeros of `E` (divide out `W ≠ 0`); the bad set is bounded by `c_D`'s zeros.

The two arms differ ONLY in `(V, W)`, keyed on `δ = degreeY_top(relations top) − degreeY_top(varY top)`:

* **exp** (`relations top = G·y_top`, δ = 0): `V = y_top^D·c_D`, `W = y_top^D` — the exp reproduces `y_top`
  multiplicatively, so the integrating factor carries a `y_top^D`; `hnum` is `expEliminate_wronskian_numerator`.
* **log** (`degreeY_top(relations top) = 0`, δ = −1): `V = c_D`, `W = 1` — no `y_top` factor; `hnum` is the
  bare Wronskian, an `eval_sub`/`eval_mul` rewrite.

(The **reciprocal** arm, δ = +1, is not a Wronskian reduce at all — `y_top = 1/w` is algebraic, cleared
directly to the restricted chain by `recip_top_combined`, so it needs none of this.)

Grounded in `rolle` (via `zero_count_bound_by_deriv_with_bad`); no `zero_count_bound_classical`.
-/

namespace MachLib.PfaffianWronskianReduce

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce

/-- Sign-agnostic Wronskian field step: from the reciprocal-vehicle derivative-zero equation, recover
`cDv·A − cDp·B = 0`. -/
private theorem wronskian_field_ne (A B cDv cDp : Real) (hcDne : cDv ≠ 0)
    (h : A * (1 / cDv) + B * (-cDp / (cDv * cDv)) = 0) : cDv * A - cDp * B = 0 := by
  have hsq : cDv * cDv ≠ 0 := MachLib.Real.mul_ne_zero hcDne hcDne
  have h2 : (cDv * cDv) * (A * (1 / cDv)) + (cDv * cDv) * (B * (-cDp / (cDv * cDv))) = 0 := by
    rw [← Real.mul_distrib, h, Real.mul_zero]
  rw [show (cDv * cDv) * (A * (1 / cDv)) = (cDv * A) * (cDv * (1 / cDv)) from by mach_ring,
      MachLib.Real.mul_div_cancel_left hcDne,
      show (cDv * cDv) * (B * (-cDp / (cDv * cDv))) = B * ((cDv * cDv) * (-cDp / (cDv * cDv))) from by mach_ring,
      MachLib.Real.mul_div_cancel_left hsq] at h2
  have h3 : (cDv * A) * 1 + B * (-cDp) = cDv * A - cDp * B := by mach_ring
  rw [h3] at h2; exact h2

/-- `(filter ¬p) + (filter p)` lengths sum to the whole (partition by a decidable predicate). -/
private theorem length_filter_partition {α : Type _} (l : List α) (q : α → Bool) :
    (l.filter (fun x => !q x)).length + (l.filter q).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases h : q a
    · rw [List.filter_cons_of_pos (by simp [h]), List.filter_cons_of_neg (by simp [h])]
      simp only [List.length_cons]; omega
    · rw [List.filter_cons_of_neg (by simp [h]), List.filter_cons_of_pos (by simp [h])]
      simp only [List.length_cons]; omega

/-- **The unified Wronskian reduce (exp + log).** Given a vehicle denominator `V`, elimination polynomial
`E`, and cofactor `W` with `W ≠ 0` on `(a,b)`, `V ≠ 0` wherever `c_D = leadingCoeffY top p ≠ 0`, and the
numerator identity `V·(cTD p) − (cTD V)·p = W·E`, the zeros of `pfaffianChainFn c p` are bounded by those of
`pf c E` plus TWICE those of `c_D` plus one (`Ne + 2K + 1`): off-bad zeros go through the sound
`zero_count_bound_by_deriv_with_bad` (Rolle endpoints are off-bad, so `rolle_ct` applies), and the bad zeros
`{c_D = 0}` are counted directly. Both `expEliminate_reduce_full` and `log_wronskian_reduce_full` are
instantiations. -/
theorem pfaffian_wronskian_reduce_full {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (p V E W : MultiPoly N) (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hWne : ∀ z, a < z → z < b → MultiPoly.eval W z (c.chainValues z) ≠ 0)
    (hVbad : ∀ z, a < z → z < b →
        MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) ≠ 0 →
        MultiPoly.eval V z (c.chainValues z) ≠ 0)
    (hnum : ∀ (x : Real) (env : Fin N → Real),
        MultiPoly.eval V x env * MultiPoly.eval (chainTotalDeriv c p) x env
          - MultiPoly.eval (chainTotalDeriv c V) x env * MultiPoly.eval p x env
        = MultiPoly.eval W x env * MultiPoly.eval E x env)
    (Ne : Nat)
    (heN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧ (pfaffianChainFn c E).eval z = 0) → zeros'.length ≤ Ne)
    (K : Nat)
    (hcDzero : ∀ zs : List Real, zs.Nodup →
        (∀ z ∈ zs, a < z ∧ z < b ∧
          MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0) → zs.length ≤ K) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros_f.length ≤ Ne + 2 * K + 1 := by
  intro zeros_f hnd hz
  classical
  -- differentiability off the bad set (extracted): c_D ≠ 0 ⇒ V ≠ 0 ⇒ f·(1/V) differentiable
  have hdiff_ob : ∀ w, a < w → w < b →
      ¬ MultiPoly.eval (MultiPoly.leadingCoeffY top p) w (c.chainValues w) = 0 →
      ∃ f' : Real, HasDerivAt
        (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval V z (c.chainValues z))) f' w := by
    intro w hwa hwb hbad
    exact ⟨_, HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval V y (c.chainValues y)) _ _ w
      (hasDerivAt_eval_natural (pfaffianChainFn c p) w (hcoh w hwa hwb))
      (HasDerivAt_inv (fun y => MultiPoly.eval V y (c.chainValues y))
        (MultiPoly.eval (chainTotalDeriv c V) w (c.chainValues w)) w
        (hVbad w hwa hwb hbad) (multiPolyHasDerivAt_eval_with_chain c V w (hcoh w hwa hwb)))⟩
  -- critical points off the bad set ⇒ zeros of pf c E (extracted)
  have hcrit_ob : ∀ zs : List Real, zs.Nodup →
      (∀ z ∈ zs, a < z ∧ z < b ∧
        ¬ MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0 ∧
        ∃ f'' : Real, HasDerivAt
          (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval V z (c.chainValues z))) f'' z
            ∧ f'' = 0) →
      zs.length ≤ Ne := by
    intro zs hnd' hz'
    apply heN zs hnd'
    intro z hzmem
    obtain ⟨hza, hzb, hnbad, f'', hvd, hf''0⟩ := hz' z hzmem
    refine ⟨hza, hzb, ?_⟩
    have hVne_z := hVbad z hza hzb hnbad
    have hinv := HasDerivAt_inv (fun y => MultiPoly.eval V y (c.chainValues y))
      (MultiPoly.eval (chainTotalDeriv c V) z (c.chainValues z)) z
      hVne_z (multiPolyHasDerivAt_eval_with_chain c V z (hcoh z hza hzb))
    have hvehd := HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval V y (c.chainValues y)) _ _ z
      (hasDerivAt_eval_natural (pfaffianChainFn c p) z (hcoh z hza hzb)) hinv
    have huniq := HasDerivAt_unique _ _ _ z hvd hvehd
    rw [hf''0] at huniq
    have hwron : MultiPoly.eval V z (c.chainValues z)
            * MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
          - MultiPoly.eval (chainTotalDeriv c V) z (c.chainValues z)
            * MultiPoly.eval p z (c.chainValues z) = 0 :=
      wronskian_field_ne
        (MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z))
        (MultiPoly.eval p z (c.chainValues z))
        (MultiPoly.eval V z (c.chainValues z))
        (MultiPoly.eval (chainTotalDeriv c V) z (c.chainValues z))
        hVne_z huniq.symm
    rw [hnum z (c.chainValues z)] at hwron
    show (pfaffianChainFn c E).eval z = 0
    exact mul_eq_zero_of_factor_ne_zero (hWne z hza hzb) hwron
  -- the bad zeros (c_D = 0) are ⊆ {c_D = 0}, bounded by K
  have hbad : (zeros_f.filter
      (fun z => decide (MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0))).length ≤ K := by
    refine hcDzero _ (hnd.filter _) ?_
    intro z hzm
    rw [List.mem_filter] at hzm
    obtain ⟨hzz, hdec⟩ := hzm
    obtain ⟨hza, hzb, _⟩ := hz z hzz
    exact ⟨hza, hzb, of_decide_eq_true hdec⟩
  -- the off-bad zeros are counted by the (now off-bad-requiring) transfer
  have hoff : (zeros_f.filter
      (fun z => !decide (MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0))).length
      ≤ Ne + K + 1 := by
    refine zero_count_bound_by_deriv_with_bad
      (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval V z (c.chainValues z)))
      (fun z => MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0)
      a b hab hdiff_ob Ne K hcrit_ob hcDzero _ (hnd.filter _) ?_
    intro z hzm
    rw [List.mem_filter] at hzm
    obtain ⟨hzz, hdec⟩ := hzm
    obtain ⟨hza, hzb, hpz⟩ := hz z hzz
    have hnb : ¬ MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0 := by
      simpa using hdec
    refine ⟨hza, hzb, hnb, ?_⟩
    show (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval V z (c.chainValues z)) = 0
    rw [hpz]; exact Real.zero_mul _
  have hpart := length_filter_partition zeros_f
      (fun z => decide (MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0))
  omega

end MachLib.PfaffianWronskianReduce
