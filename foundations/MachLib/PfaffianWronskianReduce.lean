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

/-- **The unified Wronskian reduce (exp + log).** Given a vehicle denominator `V`, elimination polynomial
`E`, and cofactor `W` with `W ≠ 0` on `(a,b)`, `V ≠ 0` wherever `c_D = leadingCoeffY top p ≠ 0`, and the
numerator identity `V·(cTD p) − (cTD V)·p = W·E`, the zeros of `pfaffianChainFn c p` are bounded by those of
`pf c E` plus those of `c_D` plus one. Reciprocal vehicle `f·(1/V)`, bad set `{c_D = 0}`,
`zero_count_bound_by_deriv_with_bad`. Both `expEliminate_reduce_full` and `log_wronskian_reduce_full` are
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
      zeros_f.length ≤ Ne + K + 1 := by
  intro zeros_f hnd hz
  refine zero_count_bound_by_deriv_with_bad
    (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval V z (c.chainValues z)))
    (fun z => MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0)
    a b hab ?_ Ne K ?_ hcDzero zeros_f hnd ?_
  · -- differentiability off the bad set: c_D ≠ 0 ⇒ V ≠ 0 ⇒ f·(1/V) differentiable
    intro w hwa hwb hbad
    exact ⟨_, HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval V y (c.chainValues y)) _ _ w
      (hasDerivAt_eval_natural (pfaffianChainFn c p) w (hcoh w hwa hwb))
      (HasDerivAt_inv (fun y => MultiPoly.eval V y (c.chainValues y))
        (MultiPoly.eval (chainTotalDeriv c V) w (c.chainValues w)) w
        (hVbad w hwa hwb hbad) (multiPolyHasDerivAt_eval_with_chain c V w (hcoh w hwa hwb)))⟩
  · -- critical points off the bad set ⇒ zeros of pf c E (divide out W ≠ 0)
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
  · -- the original zeros of f satisfy the vehicle-zero property
    intro z hzmem
    obtain ⟨hza, hzb, hpz⟩ := hz z hzmem
    refine ⟨hza, hzb, ?_⟩
    show (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval V z (c.chainValues z)) = 0
    rw [hpz]; exact Real.zero_mul _

end MachLib.PfaffianWronskianReduce
