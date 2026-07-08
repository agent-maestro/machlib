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


/-! ## Fragment log_step — constant-c_D (multilinear) EML barriers, fully rolle-only -/

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct MachLib.ChainExp2NoZeros in
/-- **Fragment log_step (constant c_D / multilinear barriers) — fully rolle-only.**
For a LOG-type (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)), if the barrier `p` has `degreeY_top p ≤ 1` and (when degree 1) a
CONSTANT leading coefficient `c_D = const c₁`, then `pf(c,p)` has finitely many zeros —
grounded in `rolle` alone, NO Wronskian/partition/analyticity. Mechanism: `degreeY_top=0`
→ depth IH; `degreeY_top=1, c_D const` → `chainTotalDeriv_rolle` (m=0) reduces to `cTD p`,
which (const `c_D` ⇒ degree-1 coeff eval-zero) trims to a TOP-FREE poly bounded by the
depth IH; the degenerate `pf(cTD p)≡0` case is `log_cTD_zero_bounded`. This is the EML
barrier family at its (outermost, constant-coefficient) log tops. -/
theorem log_step_const {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (h_top : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
    (h_tri : ∀ j : Fin (N+1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (c.relations j) = 0)
    (IH_depth : ∀ q : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z = 0) → zeros.length ≤ M)
    (p : MultiPoly (N + 1))
    (hd_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p ≤ 1)
    (hconst : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p = 1 →
        ∃ c₁ : Real, MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p = MultiPoly.const c₁)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  by_cases hd0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c p hd0 a b hab hne IH_depth
  · have hd1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 1 := by omega
    obtain ⟨c₁, hc1⟩ := hconst hd1
    by_cases hz0 : ∀ z, a < z → z < b → (pfaffianChainFn c (chainTotalDeriv c p)).eval z = 0
    · exact log_cTD_zero_bounded c p a b hab hcoh hz0 hne
    · have hne_cTD : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (chainTotalDeriv c p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hz0 (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
      have hle : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) ≤ 1 := by
        have := degreeYtop_cTD_le_log c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p; omega
      -- Bound #zeros(cTD p): either it's (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))-free (deg 0), or trims to (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))-free (deg 1, eval-zero leading).
      have hbound_cTD : ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c (chainTotalDeriv c p)).eval z = 0) → zeros.length ≤ M := by
        by_cases hcd0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) = 0
        · exact pfaffianChainFn_bound_of_degreeYtop_zero c (chainTotalDeriv c p) hcd0 a b hab hne_cTD IH_depth
        · have hcd1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) = 1 := by omega
          -- leadingCoeffY(cTD p) = getLast(yCoeffs(cTD p)) eval-zero via leadingCoeffY_cTD_eval_zero_of_const
          have h_ne_list : yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) ≠ [] := by
            intro h; have := yCoeffsAt_length_eq (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p); rw [h] at this; simp at this
          have h_phantom : ∀ (x : Real) (env : Fin (N+1) → Real),
              MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p)).getLast h_ne_list) x env = 0 := by
            intro x env
            have hlen : (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p)).length - 1 = 1 := by
              rw [yCoeffsAt_length_eq, hcd1]
            have hgl := list_getD_pred_eq_getLast (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p)) (MultiPoly.const 0) h_ne_list
            rw [hlen] at hgl
            rw [← hgl]
            exact leadingCoeffY_cTD_eval_zero_of_const c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p hd1 c₁ hc1 x env
          -- trim: pf(dropLeadingYAt (cTD p)) = pf(cTD p), and dropLeadingYAt is (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))-free
          have htrim_deg : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p)) = 0 := by
            have := degreeY_dropLeadingYAt_lt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) (by rw [hcd1]; exact Nat.zero_lt_one)
            omega
          have hne_trim : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p))).eval z ≠ 0 := by
            obtain ⟨z, hza, hzb, hzne⟩ := hne_cTD
            exact ⟨z, hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) h_ne_list h_phantom z]; exact hzne⟩
          obtain ⟨M, hM⟩ := pfaffianChainFn_bound_of_degreeYtop_zero c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p)) htrim_deg a b hab hne_trim IH_depth
          refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z hzmem => ?_)⟩
          obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
          exact ⟨hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (chainTotalDeriv c p) h_ne_list h_phantom z]; exact hzero⟩
      obtain ⟨M, hM⟩ := hbound_cTD
      exact ⟨M + 1, chainTotalDeriv_rolle c p a b hab hcoh M hM⟩


/-! ## Reusable helper: bound a degree-≤1 top-eval-zero-leading poly via depth IH -/

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct in
/-- **Bound a degree-≤1 top-eval-zero-leading polynomial via the depth IH.** If
`degreeY_top q ≤ 1` and (when `= 1`) the degree-1 coefficient is eval-zero, then `q` reduces
to a TOP-FREE polynomial (directly, or by trimming the eval-zero leading term) and the depth
IH bounds its zeros. The shared engine of both the `cTD p` bound (constant `c_D`) and the
Wronskian `g` bound (any `c_D`, via `wronskian_leadY_eval_zero`). -/
theorem bound_via_trim {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (IH_depth : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z = 0) → zeros.length ≤ M)
    (q : MultiPoly (N + 1))
    (hq_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q ≤ 1)
    (h_lead : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 1 →
        ∀ (x : Real) (env : Fin (N+1) → Real),
          MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).getD 1 (MultiPoly.const 0)) x env = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ M := by
  by_cases hq0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c q hq0 a b hab hne IH_depth
  · have hq1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 1 := by omega
    have h_ne_list : yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q ≠ [] := by
      intro h; have := yCoeffsAt_length_eq (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q; rw [h] at this; simp at this
    have h_phantom : ∀ (x : Real) (env : Fin (N+1) → Real),
        MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).getLast h_ne_list) x env = 0 := by
      intro x env
      have hlen : (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).length - 1 = 1 := by
        rw [yCoeffsAt_length_eq, hq1]
      have hgl := list_getD_pred_eq_getLast (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) (MultiPoly.const 0) h_ne_list
      rw [hlen] at hgl
      rw [← hgl]
      exact h_lead hq1 x env
    have htrim_deg : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) = 0 := by
      have := degreeY_dropLeadingYAt_lt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q (by rw [hq1]; exact Nat.zero_lt_one)
      omega
    have hne_trim : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q)).eval z ≠ 0 := by
      obtain ⟨z, hza, hzb, hzne⟩ := hne
      exact ⟨z, hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q h_ne_list h_phantom z]; exact hzne⟩
    obtain ⟨M, hM⟩ := pfaffianChainFn_bound_of_degreeYtop_zero c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) htrim_deg a b hab hne_trim IH_depth
    refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z hzmem => ?_)⟩
    obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
    exact ⟨hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q h_ne_list h_phantom z]; exact hzero⟩


/-! ## Reduce arm for arbitrary c_D at degree 1 (deeper nested log tops) -/

open MachLib.MultiPolyReconstruct in
/-- **Wronskian reduce arm for arbitrary c_D at degree 1 (deeper nested log tops).**
For a LOG top with `degreeY_top p = 1`, if the leading coefficient `c_D = leadingCoeffY
top p` is eval-nonzero somewhere and the Wronskian `g = c_D·cTD(p) − cTD(c_D)·p` is not
identically zero, then `pf(c,p)` has finitely many zeros. Wires `log_wronskian_reduce_full`:
K = #zeros(c_D) from the depth IH (c_D top-free), Ng = #zeros(g) from `bound_via_trim` (g
has `degreeY_top ≤ 1` by `degreeYtop_wronskian_le` and eval-zero degree-1 coefficient by
`wronskian_leadY_eval_zero`, so it trims to top-free). rolle-only; the residual
non-fragment gaps are exactly the two hypotheses `hcd_nz` (else c_D≡0, a separate
degree-1 reconstruction) and `hg_nz` (else g≡0, the analyticity/transcendence gap). -/
theorem log_reduce_multilinear {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (h_top : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
    (h_tri : ∀ j : Fin (N+1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (c.relations j) = 0)
    (IH_depth : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z = 0) → zeros.length ≤ M)
    (p : MultiPoly (N + 1))
    (hd1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p = 1)
    (hcd_nz : ∃ z, a < z ∧ z < b ∧
        (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)).eval z ≠ 0)
    (hg_nz : ∃ z, a < z ∧ z < b ∧
        (pfaffianChainFn c (MultiPoly.sub
          (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) (chainTotalDeriv c p))
          (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)) p))).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  -- K: c_D top-free, eval-nonzero somewhere → depth IH
  obtain ⟨K, hK⟩ := pfaffianChainFn_bound_of_degreeYtop_zero c
    (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)
    (MultiPoly.degreeY_leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) a b hab hcd_nz IH_depth
  -- Ng: g via bound_via_trim
  have hg_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (MultiPoly.sub
      (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) (chainTotalDeriv c p))
      (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)) p)) ≤ 1 := by
    have := degreeYtop_wronskian_le c (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) h_top h_tri p; omega
  have hg_lead : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (MultiPoly.sub
        (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) (chainTotalDeriv c p))
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)) p)) = 1 →
      ∀ (x : Real) (env : Fin (N+1) → Real),
        MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (MultiPoly.sub
          (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) (chainTotalDeriv c p))
          (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)) p))).getD 1 (MultiPoly.const 0)) x env = 0 := by
    intro _ x env
    have := wronskian_leadY_eval_zero c (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) h_top h_tri p x env
    rwa [hd1] at this
  obtain ⟨Ng, hNg⟩ := bound_via_trim c a b hab IH_depth _ hg_le hg_lead hg_nz
  exact ⟨Ng + K + 1, log_wronskian_reduce_full c (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p a b hab hcoh Ng hNg K hK⟩


/-! ## Pointwise / interval trim — the c_D ≡ 0 case of multilinear log_step -/

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct in
/-- **Pointwise degree-trim eval identity.** At a SINGLE point `z` where the leading
`y_top` coefficient evals to `0` (along the chain), `pf(dropLeadingYAt top q) = pf(q)`.
Pointwise version of `pfaffianChainFn_trim_eval_gen` (the underlying
`listEvalAuxN_dropLast_eq_of_last_eval_zero` only needs the eval-zero at that point). -/
theorem pfaffianChainFn_trim_eval_pt {N : Nat} (c : PfaffianChain N) (top : Fin N) (q : MultiPoly N)
    (h_ne : yCoeffsAt top q ≠ []) (z : Real)
    (h_last : MultiPoly.eval ((yCoeffsAt top q).getLast h_ne) z (c.chainValues z) = 0) :
    (pfaffianChainFn c (dropLeadingYAt top q)).eval z = (pfaffianChainFn c q).eval z := by
  show MultiPoly.eval (dropLeadingYAt top q) z (c.chainValues z) = MultiPoly.eval q z (c.chainValues z)
  unfold dropLeadingYAt
  rw [eval_reconstructY, ← eval_yCoeffsAt top q z (c.chainValues z)]
  exact listEvalAuxN_dropLast_eq_of_last_eval_zero top (yCoeffsAt top q) h_ne z (c.chainValues z) h_last 0

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct in
/-- **Bound a degree-≤1 poly whose leading coefficient vanishes on the interval, via the
depth IH.** Like `bound_via_trim` but with the WEAKER (interval, pointwise) condition
`eval(leading) z (chainValues z) = 0` on `(a,b)` — which is what `c_D ≡ 0 on (a,b)` gives.
`q` is eval-equal to its trim on `(a,b)` (pointwise trim), and the trim is top-free ⇒ depth
IH. This closes the `c_D ≡ 0` case of the multilinear log_step, fully rolle-only. -/
theorem bound_via_trim_interval {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (IH_depth : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z = 0) → zeros.length ≤ M)
    (q : MultiPoly (N + 1))
    (hq_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q ≤ 1)
    (h_lead : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 1 →
        ∀ z, a < z → z < b →
          MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).getD 1 (MultiPoly.const 0)) z (c.chainValues z) = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ M := by
  by_cases hq0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c q hq0 a b hab hne IH_depth
  · have hq1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 1 := by omega
    have h_ne_list : yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q ≠ [] := by
      intro h; have := yCoeffsAt_length_eq (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q; rw [h] at this; simp at this
    -- getLast = getD_1 (poly), so eval(getLast) z cv = eval(getD_1) z cv = 0 on (a,b)
    have hgl_eq : (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).getLast h_ne_list
        = (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).getD 1 (MultiPoly.const 0) := by
      have hlen : (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q).length - 1 = 1 := by
        rw [yCoeffsAt_length_eq, hq1]
      have hgl := list_getD_pred_eq_getLast (yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) (MultiPoly.const 0) h_ne_list
      rw [hlen] at hgl; exact hgl.symm
    have htrim_deg : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) = 0 := by
      have := degreeY_dropLeadingYAt_lt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q (by rw [hq1]; exact Nat.zero_lt_one); omega
    have hpf_eq : ∀ z, a < z → z < b →
        (pfaffianChainFn c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q)).eval z = (pfaffianChainFn c q).eval z := by
      intro z hza hzb
      refine pfaffianChainFn_trim_eval_pt c (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q h_ne_list z ?_
      rw [hgl_eq]; exact h_lead hq1 z hza hzb
    have hne_trim : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q)).eval z ≠ 0 := by
      obtain ⟨z, hza, hzb, hzne⟩ := hne; exact ⟨z, hza, hzb, by rw [hpf_eq z hza hzb]; exact hzne⟩
    obtain ⟨M, hM⟩ := pfaffianChainFn_bound_of_degreeYtop_zero c (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) htrim_deg a b hab hne_trim IH_depth
    refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z hzmem => ?_)⟩
    obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
    exact ⟨hza, hzb, by rw [hpf_eq z hza hzb]; exact hzero⟩


/-! ## Full multilinear log_step — rolle-only modulo the single g≡0 degeneracy -/

open MachLib.MultiPolyReconstruct in
/-- **Full multilinear log_step (degree ≤ 1, any c_D) — rolle-only modulo the single g≡0
degeneracy.** For a LOG-type top, ANY barrier `p` with `degreeY_top p ≤ 1` has finitely
many zeros, GIVEN a handler `hDegen` for the sole non-rolle-derivable case: a degree-1
barrier whose Wronskian `g` vanishes identically. Every other case is discharged from
`rolle` alone:
  degreeY_top = 0                → depth IH.
  degreeY_top = 1, c_D ≡ 0       → bound_via_trim_interval (pointwise trim; barrier
                                    eval-equal to a top-free poly on (a,b)).
  degreeY_top = 1, c_D ≢ 0, g ≢ 0 → log_reduce_multilinear (Wronskian reduce arm).
  degreeY_top = 1, c_D ≢ 0, g ≡ 0 → hDegen (the isolated analyticity/transcendence gap).
This is the EML-barrier family at every log top (multilinear ⇒ degree ≤ 1), so the whole
log side of retiring `zero_count_bound_classical` is rolle-only up to `hDegen`. -/
theorem log_step_multilinear {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (h_top : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
    (h_tri : ∀ j : Fin (N+1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) (c.relations j) = 0)
    (IH_depth : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z = 0) → zeros.length ≤ M)
    (hDegen : ∀ q : MultiPoly (N + 1),
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q = 1 →
        (∀ z, a < z → z < b → (pfaffianChainFn c (MultiPoly.sub
          (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q) (chainTotalDeriv c q))
          (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) q)) q))).eval z = 0) →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ M)
    (p : MultiPoly (N + 1))
    (hd_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p ≤ 1)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  by_cases hd0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p = 0
  · exact pfaffianChainFn_bound_of_degreeYtop_zero c p hd0 a b hab hne IH_depth
  · have hd1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p = 1 := by omega
    by_cases hcd_zero : ∀ z, a < z → z < b → (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)).eval z = 0
    · refine bound_via_trim_interval c a b hab IH_depth p hd_le ?_ hne
      intro _ z hza hzb
      have h := getD_at_degreeY_eq_lcY_eval (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p z (c.chainValues z)
      rw [hd1] at h
      rw [h]; exact hcd_zero z hza hzb
    · have hcd_nz : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hcd_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
      by_cases hg_zero : ∀ z, a < z → z < b → (pfaffianChainFn c (MultiPoly.sub
          (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) (chainTotalDeriv c p))
          (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)) p))).eval z = 0
      · exact hDegen p hd1 hg_zero hne
      · have hg_nz : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (MultiPoly.sub
            (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p) (chainTotalDeriv c p))
            (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N+1)) p)) p))).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hg_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
        exact log_reduce_multilinear c a b hab hcoh h_top h_tri IH_depth p hd1 hcd_nz hg_nz


/-! ## Exp arm — exp-reduce degree-drop for constant c_D (foundation of exp_step_const) -/

/-- **Exp-reduce degree-drop for constant c_D.** For an EXP-type top (relation `G·y_top`,
`G` top-free), if `leadingCoeffY top p = const c₁` then the reduce
`chainReduce c (deg·G) p` (`deg = degreeY_top p`) has eval-zero leading `y_top` coefficient:
`chainReduce_lcY_top_cancel` gives it = `cTD(const c₁) − 0·(const c₁) = 0`. So the exp
reduce with multiplier `deg·G` DROPS the degree for constant `c_D` — the exp analog of the
log `leadingCoeffY_cTD_eval_zero_of_const`, enabling a fully rolle-only exp_step on the
constant-c_D (multilinear) fragment, with integrating factor `y_top^{-deg}` (needs only
`y_top > 0`, no partition). -/
theorem exp_reduce_lead_eval_zero_of_const {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (G : MultiPoly N) (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (c₁ : Real) (hconst : MultiPoly.leadingCoeffY top p = MultiPoly.const c₁)
    (x : Real) (env : Fin N → Real) :
    MultiPoly.eval (MultiPoly.leadingCoeffY top
        (chainReduce c (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) G) p)) x env = 0 := by
  have hm : MultiPoly.degreeY top (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) G) = 0 := by
    have h1 : MultiPoly.degreeY top (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p)) : MultiPoly N) = 0 := rfl
    show MultiPoly.degreeY top (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) + MultiPoly.degreeY top G = 0
    omega
  have hcancel : MultiPoly.eval (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) G) x env
      = MachLib.Real.natCast (MultiPoly.degreeY top p) * MultiPoly.eval G x env + MultiPoly.eval (MultiPoly.const 0) x env := by
    show MultiPoly.eval (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) x env * MultiPoly.eval G x env = _
    show MachLib.Real.natCast (MultiPoly.degreeY top p) * MultiPoly.eval G x env
        = MachLib.Real.natCast (MultiPoly.degreeY top p) * MultiPoly.eval G x env + (0:Real)
    rw [Real.add_zero]
  have h := chainReduce_lcY_top_cancel c G top h_reltop h_Gtop h_tri
    (MultiPoly.mul (MultiPoly.const (MachLib.Real.natCast (MultiPoly.degreeY top p))) G) (MultiPoly.const 0) p hm x env hcancel
  rw [h, hconst]
  show MultiPoly.eval (chainTotalDeriv c (MultiPoly.const c₁)) x env
      - MultiPoly.eval (MultiPoly.const 0) x env * MultiPoly.eval (MultiPoly.const c₁) x env = 0
  rw [MachLib.IterExpTopIdentity.cTD_const c c₁]
  show (0:Real) - (0:Real) * c₁ = 0
  mach_ring

end PfaffianLogLead
end MachLib
