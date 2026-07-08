import MachLib.PfaffianGeneralWF
import MachLib.PfaffianLogLeadId
import MachLib.FieldLemmas
/-!
# Single-subinterval Wronskian reduce (log descent, analytic core)

The log Wronskian reducer's per-subinterval Rolle transfer. On a subinterval of
`(a,b)` where the leading coefficient `c_D = leadingCoeffY top p` is POSITIVE, the
zeros of `pfaffianChainFn c p` are ≤ (zeros of the Wronskian
`g = c_D·cTD(p) − cTD(c_D)·p`) + 1.

Mechanism: `zero_count_vehicleGen_transfer_raw` (arbitrary vehicle) with vehicle
`f·exp(E)`, `E = −log(c_D)`. Then `E' = −(c_D)'/c_D` (log chain rule,
`HasDerivAt_log_pos` ∘ `multiPolyHasDerivAt_eval_with_chain`), and
`(f·exp E)' = exp(E)·(f' + E'·f) = exp(E)·pf(g)/c_D²` — whose zeros, since `exp>0`
and `c_D>0`, are exactly the zeros of `g` (`wronskian_field` recovers `pf(g)=0` from
the vehicle-derivative-zero equation). The `c_D>0` hypothesis is why the outer
descent must PARTITION `(a,b)` by the (finitely many, top-free ⇒ restriction-IH
bounded) zeros of `c_D` and apply this per sign-constant piece.

Grounded in the `rolle` axiom (via `zero_count_bound_by_deriv`); no
`zero_count_bound_classical`.
-/
namespace MachLib
namespace PfaffianLogLead
open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce MachLib.IterExpDepthN

/-- Pure-real field step for the Wronskian reduce: from the vehicle-derivative-zero
equation, recover the Wronskian value `cDv·A − cDp·B = 0`. -/
private theorem wronskian_field (A B cDv cDp ex : Real) (hexne : ex ≠ 0) (hcDne : cDv ≠ 0)
    (h : A * ex + B * (ex * (-((1 / cDv) * cDp))) = 0) : cDv * A - cDp * B = 0 := by
  have hf : A * ex + B * (ex * (-((1 / cDv) * cDp))) = ex * (A - B * ((1 / cDv) * cDp)) := by mach_ring
  rw [hf] at h
  have hin : A - B * ((1 / cDv) * cDp) = 0 := mul_eq_zero_of_factor_ne_zero hexne h
  have h2 : cDv * (A - B * ((1 / cDv) * cDp)) = 0 := by rw [hin]; exact mul_zero _
  have hc : cDv * (B * ((1 / cDv) * cDp)) = cDp * B := by
    rw [show B * ((1 / cDv) * cDp) = (B * cDp) * (1 / cDv) from by mach_ring,
        show cDv * ((B * cDp) * (1 / cDv)) = (B * cDp) * (cDv * (1 / cDv)) from by mach_ring,
        MachLib.Real.mul_div_cancel_left hcDne]
    mach_ring
  have h3 : cDv * (A - B * ((1 / cDv) * cDp)) = cDv * A - cDv * (B * ((1 / cDv) * cDp)) := by mach_ring
  rw [h3, hc] at h2
  exact h2

theorem log_wronskian_reduce_subinterval {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (p : MultiPoly N) (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hcDpos : ∀ z, a < z → z < b → 0 < MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z))
    (Nn : Nat)
    (hgN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          (pfaffianChainFn c (MultiPoly.sub
            (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
            (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))).eval z = 0) →
        zeros'.length ≤ Nn) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros_f.length ≤ Nn + 1 := by
  refine zero_count_vehicleGen_transfer_raw (pfaffianChainFn c p)
    (fun y => -Real.log (MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y)))
    (fun y => -((1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y))
                * MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) y (c.chainValues y)))
    a b hab hcoh ?_ Nn ?_
  · intro z hza hzb
    have hpos := hcDpos z hza hzb
    have hcDd := multiPolyHasDerivAt_eval_with_chain c (MultiPoly.leadingCoeffY top p) z (hcoh z hza hzb)
    have hlogd := HasDerivAt_comp Real.log (fun y => MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y))
        (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) z (c.chainValues z))
        (1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z)) z
        hcDd (HasDerivAt_log_pos _ hpos)
    exact HasDerivAt_neg _ _ z hlogd
  · intro zeros' hnd' hz'
    apply hgN zeros' hnd'
    intro z hzmem
    obtain ⟨hza, hzb, f'', hvd, hf''0⟩ := hz' z hzmem
    refine ⟨hza, hzb, ?_⟩
    have hpos := hcDpos z hza hzb
    have hcDne : MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) ≠ 0 := ne_of_gt hpos
    have hcDd := multiPolyHasDerivAt_eval_with_chain c (MultiPoly.leadingCoeffY top p) z (hcoh z hza hzb)
    have hlogd := HasDerivAt_comp Real.log (fun y => MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y))
        (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) z (c.chainValues z))
        (1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z)) z
        hcDd (HasDerivAt_log_pos _ hpos)
    have hEz := HasDerivAt_neg _ _ z hlogd
    have hfd := hasDerivAt_eval_natural (pfaffianChainFn c p) z (hcoh z hza hzb)
    have hvehd := hasDerivAt_vehicleGen (pfaffianChainFn c p)
      (fun y => -Real.log (MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y)))
      (-((1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z))
          * MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) z (c.chainValues z))) z hfd hEz
    have huniq := HasDerivAt_unique _ _ _ z hvd hvehd
    rw [hf''0] at huniq
    show MultiPoly.eval (MultiPoly.sub (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p)) (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p)) z (c.chainValues z) = 0
    rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul]
    exact wronskian_field
      (MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z))
      (MultiPoly.eval p z (c.chainValues z))
      (MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z))
      (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) z (c.chainValues z))
      (Real.exp (-Real.log (MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z))))
      (exp_ne_zero _) hcDne huniq.symm

/-! ## Sign-agnostic variant — the one the partition actually uses -/

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

/-- **Single-subinterval Wronskian reduce (log, SIGN-AGNOSTIC).** On `(a,b)` where the
leading coefficient `c_D = leadingCoeffY top p` is NONZERO (either sign), the zeros of
`pfaffianChainFn c p` are ≤ (zeros of the Wronskian `g = c_D·cTD(p) − cTD(c_D)·p`) + 1.
Rolle (`zero_count_bound_by_deriv`) via the RECIPROCAL vehicle `f·(1/c_D)` — smooth and
nonzero wherever `c_D ≠ 0` — with `(f/c_D)' = pf(g)/c_D²` (`HasDerivAt_inv` + product
rule). Cleaner than the `exp(−log c_D)` version above: no `exp`/`log`, and only `c_D ≠ 0`
is required, so the outer partition needs merely `c_D ≠ 0` between its zeros (automatic)
— NO sign-constancy / IVT argument, and no separate `c_D < 0` twin. This is the building
block the partition uses. -/
theorem log_wronskian_reduce_subinterval_ne {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (p : MultiPoly N) (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hcDne : ∀ z, a < z → z < b → MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) ≠ 0)
    (Nn : Nat)
    (hgN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          (pfaffianChainFn c (MultiPoly.sub
            (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
            (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))).eval z = 0) →
        zeros'.length ≤ Nn) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros_f.length ≤ Nn + 1 := by
  intro zeros_f hnd hz
  refine zero_count_bound_by_deriv
    (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z)))
    a b hab ?_ Nn ?_ zeros_f hnd ?_
  · intro w hwa hwb
    have hinv := HasDerivAt_inv (fun y => MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y))
      (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) w (c.chainValues w)) w
      (hcDne w hwa hwb) (multiPolyHasDerivAt_eval_with_chain c (MultiPoly.leadingCoeffY top p) w (hcoh w hwa hwb))
    exact ⟨_, HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y)) _ _ w
      (hasDerivAt_eval_natural (pfaffianChainFn c p) w (hcoh w hwa hwb)) hinv⟩
  · intro zeros' hnd' hz'
    apply hgN zeros' hnd'
    intro z hzmem
    obtain ⟨hza, hzb, f'', hvd, hf''0⟩ := hz' z hzmem
    refine ⟨hza, hzb, ?_⟩
    have hcDne_z := hcDne z hza hzb
    have hinv := HasDerivAt_inv (fun y => MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y))
      (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) z (c.chainValues z)) z
      hcDne_z (multiPolyHasDerivAt_eval_with_chain c (MultiPoly.leadingCoeffY top p) z (hcoh z hza hzb))
    have hvehd := HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y)) _ _ z
      (hasDerivAt_eval_natural (pfaffianChainFn c p) z (hcoh z hza hzb)) hinv
    have huniq := HasDerivAt_unique _ _ _ z hvd hvehd
    rw [hf''0] at huniq
    show MultiPoly.eval (MultiPoly.sub (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p)) (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p)) z (c.chainValues z) = 0
    rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul]
    exact wronskian_field_ne
      (MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z))
      (MultiPoly.eval p z (c.chainValues z))
      (MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z))
      (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) z (c.chainValues z))
      hcDne_z huniq.symm
  · intro z hzmem
    obtain ⟨hza, hzb, hpz⟩ := hz z hzmem
    refine ⟨hza, hzb, ?_⟩
    show (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z)) = 0
    rw [hpz]; exact Real.zero_mul _

end PfaffianLogLead
end MachLib
