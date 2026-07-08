import MachLib.PfaffianGeneralWF
import MachLib.PfaffianLogLeadId
import MachLib.FieldLemmas
import MachLib.ChainExp2Trim
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

/-! ## The full log Wronskian reduce (partition assembled) -/

/-- **Log Wronskian reduce — FULL (partition assembled).** Combines the reciprocal-
vehicle Rolle transfer with the `c_D`-partition (`zero_count_bound_by_deriv_with_bad`):
`#zeros(pfaffianChainFn c p) ≤ Ng + K + 1`, where `Ng` bounds the zeros of the Wronskian
`g = c_D·cTD(p) − cTD(c_D)·p` (from the WF recursion, since `g` has strictly smaller
canonical top degree by `wronskian_leadY_eval_zero`) and `K` bounds the zeros of
`c_D = leadingCoeffY top p` (top-free ⇒ a lower-chain function, bounded by the restriction
IH). The `bad set` is `{c_D = 0}`: on it the vehicle `pf(p)/c_D` is not differentiable;
off it, each Rolle critical point is a zero of `g` (via `wronskian_field_ne`, since
`¬bad ⇒ c_D ≠ 0`). This is the reduce arm of the log WF descent. -/
theorem log_wronskian_reduce_full {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (p : MultiPoly N) (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (Ng : Nat)
    (hgN : ∀ zeros' : List Real, zeros'.Nodup →
        (∀ z ∈ zeros', a < z ∧ z < b ∧
          (pfaffianChainFn c (MultiPoly.sub
            (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
            (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))).eval z = 0) →
        zeros'.length ≤ Ng)
    (K : Nat)
    (hcDzero : ∀ zs : List Real, zs.Nodup →
        (∀ z ∈ zs, a < z ∧ z < b ∧ MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0) →
        zs.length ≤ K) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) →
      zeros_f.length ≤ Ng + K + 1 := by
  intro zeros_f hnd hz
  refine zero_count_bound_by_deriv_with_bad
    (fun z => (pfaffianChainFn c p).eval z * (1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z)))
    (fun z => MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) = 0)
    a b hab ?_ Ng K ?_ hcDzero zeros_f hnd ?_
  · intro w hwa hwb hne
    exact ⟨_, HasDerivAt_mul (pfaffianChainFn c p).eval
      (fun y => 1 / MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y)) _ _ w
      (hasDerivAt_eval_natural (pfaffianChainFn c p) w (hcoh w hwa hwb))
      (HasDerivAt_inv (fun y => MultiPoly.eval (MultiPoly.leadingCoeffY top p) y (c.chainValues y))
        (MultiPoly.eval (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) w (c.chainValues w)) w
        hne (multiPolyHasDerivAt_eval_with_chain c (MultiPoly.leadingCoeffY top p) w (hcoh w hwa hwb)))⟩
  · intro zs hnd' hz'
    apply hgN zs hnd'
    intro z hzmem
    obtain ⟨hza, hzb, hnbad, f'', hvd, hf''0⟩ := hz' z hzmem
    refine ⟨hza, hzb, ?_⟩
    have hcDne_z : MultiPoly.eval (MultiPoly.leadingCoeffY top p) z (c.chainValues z) ≠ 0 := hnbad
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

/-! ## g≡0 degeneracy — rolle-only for the constant-c_D fragment -/

/-- **g≡0 for constant leading coefficient → 0 zeros (rolle-only).** If `pf(cTD p) ≡ 0`
on `(a,b)` — which is the Wronskian-vanishing case `g≡0` precisely when
`c_D = leadingCoeffY top p` is a numeric constant (then `g = c_D·cTD(p)`) — and `pf(p)` is
non-vanishing somewhere, then `pf(p)` has NO zeros on `(a,b)`: the `m=0` linear ODE `f'=0`
has the constant solution `f = f(z₀) ≠ 0`. Instance of `pfaffianChainFn_no_zeros_of_reduct_zero_gen`
with `m = const 0`, `E = const`. rolle-grounded; NO analyticity, NO zero_count_bound_classical.

This cleanly discharges the `g≡0` degeneracy for the constant-`c_D` EML-barrier fragment
(the outermost log generator has `c_D = const(±1)`; the general nested case where a deeper
log top has non-constant `c_D` remains the genuine analyticity/transcendence gap). -/
theorem log_cTD_zero_bounded {N : Nat} (c : PfaffianChain N) (p : MultiPoly N) (a b : Real)
    (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (hred0 : ∀ z, a < z → z < b → (pfaffianChainFn c (chainTotalDeriv c p)).eval z = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  obtain ⟨z₀, hz₀a, hz₀b, hne₀⟩ := hne
  have hE : ∀ z, a < z → z < b →
      HasDerivAt (fun _ => (0:Real)) (-(pfaffianChainFn c (MultiPoly.const 0)).eval z) z := by
    intro z _ _
    show HasDerivAt (fun _ => (0:Real)) (-(MultiPoly.eval (MultiPoly.const 0) z (c.chainValues z))) z
    show HasDerivAt (fun _ => (0:Real)) (-(0:Real)) z
    rw [neg_zero]; exact HasDerivAt_const 0 z
  have hreduct : ∀ z, a < z → z < b →
      (pfaffianChainFn c (chainReduce c (MultiPoly.const 0) p)).eval z = 0 := by
    intro z hza hzb
    have heq : (pfaffianChainFn c (chainReduce c (MultiPoly.const 0) p)).eval z
        = (pfaffianChainFn c (chainTotalDeriv c p)).eval z := by
      show MultiPoly.eval (chainReduce c (MultiPoly.const 0) p) z (c.chainValues z)
          = MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z)
      show MultiPoly.eval (MultiPoly.sub (chainTotalDeriv c p) (MultiPoly.mul (MultiPoly.const 0) p)) z (c.chainValues z) = _
      rw [MultiPoly.eval_sub, MultiPoly.eval_mul]
      show MultiPoly.eval (chainTotalDeriv c p) z (c.chainValues z) - (0:Real) * MultiPoly.eval p z (c.chainValues z) = _
      rw [Real.zero_mul, Real.sub_zero]
    rw [heq]; exact hred0 z hza hzb
  have hnoz := pfaffianChainFn_no_zeros_of_reduct_zero_gen c (MultiPoly.const 0) p a b hab
    (fun _ => 0) hcoh hE hreduct z₀ hz₀a hz₀b hne₀
  refine ⟨0, fun zeros _ hz => ?_⟩
  cases zeros with
  | nil => exact Nat.le_refl 0
  | cons z zs =>
    obtain ⟨ha, hb', hzero⟩ := hz z (List.mem_cons_self _ _)
    exact absurd hzero (hnoz z ha hb')

/-! ## Trim bridges for the constant-c_D fragment log_step -/

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct in
/-- **General-depth degree-trim eval identity.** If the leading `y_top` coefficient
(`getLast` of `yCoeffsAt top q`) is eval-zero at every chain point, dropping the leading
`y_top` term doesn't change the value along the chain. General index/depth version of
`pfaffianChainFn_degreeYtop_trim_eval` (stated only for depth `M+3`); direct wrapper of the
chain-agnostic `eval_dropLeadingYAt_of_last_canonically_zero`. -/
theorem pfaffianChainFn_trim_eval_gen {N : Nat} (c : PfaffianChain N) (top : Fin N) (q : MultiPoly N)
    (h_ne : yCoeffsAt top q ≠ [])
    (h_phantom : ∀ (x : Real) (env : Fin N → Real),
      MultiPoly.eval ((yCoeffsAt top q).getLast h_ne) x env = 0) (z : Real) :
    (pfaffianChainFn c (dropLeadingYAt top q)).eval z = (pfaffianChainFn c q).eval z :=
  eval_dropLeadingYAt_of_last_canonically_zero top q h_ne h_phantom z (c.chainValues z)

/-- **Leading `y_top` coefficient of `cTD p` is eval-zero when `c_D` is constant.** For a
LOG top with `degreeY_top p = 1` and `leadingCoeffY top p = const c₁`, `idN_log_lead` gives
`coeffY_1(cTD p) = cTD(const c₁) = 0` at eval. So the degree-1 coefficient of `cTD p` is
eval-zero — the trim condition. This is why constant `c_D` (multilinear EML barriers) makes
`cTD p` reduce to a top-free polynomial (→ depth IH), fully rolle-only, with NO
Wronskian/partition/g≡0-analyticity. -/
theorem leadingCoeffY_cTD_eval_zero_of_const {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (h_top : MultiPoly.degreeY top (c.relations top) = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (hd1 : MultiPoly.degreeY top p = 1)
    (c₁ : Real) (hconst : MultiPoly.leadingCoeffY top p = MultiPoly.const c₁)
    (x : Real) (env : Fin N → Real) :
    MultiPoly.eval ((yCoeffsAt top (chainTotalDeriv c p)).getD 1 (MultiPoly.const 0)) x env = 0 := by
  have h := idN_log_lead c top h_top h_tri x env p
  unfold IdNLogLead at h
  rw [hconst, MachLib.IterExpTopIdentity.cTD_const c c₁, hd1] at h
  rw [h]
  rfl

end PfaffianLogLead
end MachLib
