import MachLib.EMLExplicitBoundExpArm
import MachLib.PfaffianLogDegenerate
import MachLib.PfaffianLogWronskian

/-!
# Explicit-K log arm — the `degreeY_top` fuel recursion, MIXED chain (explicit form)

The log-arm analog of `EMLExplicitBoundExpArm.exp_step_general_explicit`. Mirrors
`PfaffianLogGeneralDegree.log_step_general` (already the mixed-chain shape: a TOP-level
LOG relation `degreeY_top (relations top) = 0`, an arbitrary chain below handled by a
depth-IH bound function `Kih`), replacing every `∃M` with a named `Nat` via
`EMLExplicitBound.BoundedZerosBy`.

Structural difference from the exp arm: the log descent has no degree-preserving
integrating-factor step, so its base case covers degree `≤ 1` (`log_step_multilinear`,
here `log_step_multilinear_analytic_explicit`) rather than just degree `0`; degree `≥ 2`
reduces via the Wronskian `g = c_D·cTD(p) − cTD(c_D)·p` (strictly lower degree, by
`degreeYtop_wronskian_le`/`wronskian_leadY_eval_zero`) to a `g ≡ 0` analytic leaf
(`log_hDegen_via_analytic`) or a recursion on `g` (`log_wronskian_reduce_full`). The
generic trim-and-recurse lemmas (`bound_via_trim_rec_explicit` /
`bound_via_trim_interval_rec_explicit`) built for the exp arm are chain/top-agnostic and
are reused here verbatim — for the log arm's `D = 0` case AND its `D ≥ 2` recursion.
-/

namespace MachLib.EMLExplicitBound

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianLogLead
open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct

/-- The log Wronskian `g = c_D · cTD(p) − cTD(c_D) · p`, `c_D = leadingCoeffY top p`. Named for
reuse across the base (degree ≤ 1) and general (degree ≥ 2) cases. -/
noncomputable def logWronskianPoly {N : Nat} (c : PfaffianChain (N + 1)) (top : Fin (N + 1))
    (p : MultiPoly (N + 1)) : MultiPoly (N + 1) :=
  MultiPoly.sub (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
    (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p)

/-- **The explicit degree-`≤1` (multilinear) log base bound.** Non-recursive: `p` bottoms out at
`Kih (dropLastY p)` (degree 0), `Kih (dropLastY (dropLeadingYAt top p))` (degree 1, `c_D ≡ 0`,
trimmed to degree 0), `Kih (dropLastY (leadingCoeffY top p))` (degree 1, `c_D ≢ 0`, `g ≡ 0` leaf —
bound is exactly `K`, no growth), or the `g ≢ 0` Wronskian-reduce arm (degree 1, `c_D ≢ 0`, `g ≢ 0`):
`Kih (dropLastY (dropLeadingYAt top g)) + 2 * Kih (dropLastY (leadingCoeffY top p)) + 1`. -/
noncomputable def logBaseE {N : Nat} (c : PfaffianChain (N + 1)) (top : Fin (N + 1))
    (Kih : MultiPoly N → Nat) (p : MultiPoly (N + 1)) : Nat :=
  max (Kih (MultiPoly.dropLastY p))
    (max (Kih (MultiPoly.dropLastY (dropLeadingYAt top p)))
      (max (Kih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY top p)))
        (max (Kih (MultiPoly.dropLastY (logWronskianPoly c top p)))
             (Kih (MultiPoly.dropLastY (dropLeadingYAt top (logWronskianPoly c top p))))
          + 2 * Kih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY top p)) + 1)))

/-- **The explicit log-arm bound.** Structural recursion on the fuel `D`, mirroring
`EMLExplicitBoundExpArm.expBoundE`'s shape: `logBaseE` (the degree-`≤1` case), `logBoundE … D p`
(`p` already fits under the smaller fuel), `logBoundE … D (dropLeadingYAt top p)` (the `c_D ≡ 0`
trim-and-recurse), and the Wronskian-reduce arm
`max (logBoundE … D g) (logBoundE … D (dropLeadingYAt top g)) + 2 * Kih (dropLastY (leadingCoeffY top p)) + 1`
where `g = logWronskianPoly c top p`. -/
noncomputable def logBoundE {N : Nat} (c : PfaffianChain (N + 1)) (top : Fin (N + 1))
    (Kih : MultiPoly N → Nat) : Nat → MultiPoly (N + 1) → Nat
  | 0, p => logBaseE c top Kih p
  | D + 1, p =>
      max (logBaseE c top Kih p)
        (max (logBoundE c top Kih D p)
          (max (logBoundE c top Kih D (dropLeadingYAt top p))
            (max (logBoundE c top Kih D (logWronskianPoly c top p))
                 (logBoundE c top Kih D (dropLeadingYAt top (logWronskianPoly c top p)))
              + 2 * Kih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY top p)) + 1)))

/-! ## Explicit-bound log-specific leaves -/

/-- **Explicit-bound `g ≡ 0` analytic leaf.** Explicit-`K` analog of `log_hDegen_via_analytic`: when
the log Wronskian `g = c_D · cTD(q) − cTD(c_D) · q` vanishes identically on `(a,b)`, `q`'s zero count
is bounded by `c_D`'s (no growth) — `Fp·G − F·Gp = 0` off `q ≡ c_D`-proportionality
(`wronskian_zero_zeros_subset`), directly via `wronskian_arm_explicit`. -/
theorem log_hDegen_via_analytic_explicit {N : Nat} (c : PfaffianChain (N + 1))
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (q : MultiPoly (N + 1))
    (hFan : IsAnalyticOnReals (pfaffianChainFn c q).eval (Icc a b))
    (hGan : IsAnalyticOnReals
      (pfaffianChainFn c (MultiPoly.leadingCoeffY
        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval (Icc a b))
    (hg_zero : ∀ z, a < z → z < b → (pfaffianChainFn c (MultiPoly.sub
      (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)
        (chainTotalDeriv c q))
      (MultiPoly.mul (chainTotalDeriv c
        (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)) q))).eval z = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0)
    (Nb : Nat)
    (hGbound : BoundedZerosBy (pfaffianChainFn c
      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)) a b Nb) :
    BoundedZerosBy (pfaffianChainFn c q) a b Nb := by
  have hFderiv : ∀ x, a < x → x < b →
      HasDerivAt (pfaffianChainFn c q).eval
        ((pfaffianChainFn c (chainTotalDeriv c q)).eval x) x :=
    fun x h1 h2 => multiPolyHasDerivAt_eval_with_chain c q x (hcoh x h1 h2)
  have hGderiv : ∀ x, a < x → x < b →
      HasDerivAt (pfaffianChainFn c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval
        ((pfaffianChainFn c (chainTotalDeriv c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x) x :=
    fun x h1 h2 => multiPolyHasDerivAt_eval_with_chain c
      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q) x (hcoh x h1 h2)
  have hW : ∀ x, a < x → x < b →
      (pfaffianChainFn c (chainTotalDeriv c q)).eval x
        * (pfaffianChainFn c
            (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval x
      - (pfaffianChainFn c q).eval x
        * (pfaffianChainFn c (chainTotalDeriv c
            (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x = 0 := by
    intro x h1 h2
    show (pfaffianChainFn c (chainTotalDeriv c q)).eval x
        * (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval x
      - (pfaffianChainFn c q).eval x
        * (pfaffianChainFn c (chainTotalDeriv c
            (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x = 0
    have hrw : (pfaffianChainFn c (chainTotalDeriv c q)).eval x
          * (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval x
        - (pfaffianChainFn c q).eval x
          * (pfaffianChainFn c (chainTotalDeriv c
              (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x
        = (pfaffianChainFn c (MultiPoly.sub
            (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)
              (chainTotalDeriv c q))
            (MultiPoly.mul (chainTotalDeriv c
              (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)) q))).eval x := by
      show _ = MultiPoly.eval (MultiPoly.sub
            (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)
              (chainTotalDeriv c q))
            (MultiPoly.mul (chainTotalDeriv c
              (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)) q)) x (c.chainValues x)
      rw [MultiPoly.eval_sub, MultiPoly.eval_mul, MultiPoly.eval_mul]
      mach_ring
    rw [hrw]; exact hg_zero x h1 h2
  have hFne : ∃ x : Real, Ioo a b x ∧ (pfaffianChainFn c q).eval x ≠ 0 := by
    obtain ⟨z, hz1, hz2, hzne⟩ := hne
    exact ⟨z, ⟨hz1, hz2⟩, hzne⟩
  exact wronskian_arm_explicit
    (pfaffianChainFn c q).eval
    (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q)).eval
    (fun x => (pfaffianChainFn c (chainTotalDeriv c q)).eval x)
    (fun x => (pfaffianChainFn c (chainTotalDeriv c
      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) q))).eval x)
    a b hab hFan hGan hFderiv hGderiv hW hFne Nb hGbound

/-- **Explicit-bound log Wronskian reduce.** Explicit-`K` analog of `log_wronskian_reduce_full`:
`Ng + 2K + 1`, where `Ng` bounds the Wronskian `g`'s zeros and `K` bounds `c_D`'s. -/
theorem log_wronskian_arm_explicit {N : Nat} (c : PfaffianChain N) (top : Fin N)
    (p : MultiPoly N) (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (Ng : Nat)
    (hgN : BoundedZerosBy (pfaffianChainFn c (MultiPoly.sub
        (MultiPoly.mul (MultiPoly.leadingCoeffY top p) (chainTotalDeriv c p))
        (MultiPoly.mul (chainTotalDeriv c (MultiPoly.leadingCoeffY top p)) p))) a b Ng)
    (K : Nat)
    (hcD : BoundedZerosBy (pfaffianChainFn c (MultiPoly.leadingCoeffY top p)) a b K) :
    BoundedZerosBy (pfaffianChainFn c p) a b (Ng + 2 * K + 1) :=
  log_wronskian_reduce_full c top p a b hab hcoh Ng hgN K hcD

/-! ## The degree-`≤1` (multilinear) log base case, explicit -/

/-- **Explicit-bound multilinear log step.** Explicit-`K` analog of
`log_step_multilinear_analytic` (via `PfaffianLogLead.log_step_multilinear`): degree `0` is the
depth IH directly; degree `1` splits on `c_D ≡ 0` (trim to degree `0` via
`bound_via_trim_interval_rec_explicit` at fuel `0`) vs `c_D ≢ 0` (Wronskian `g`: `g ≡ 0` is the
analytic leaf `log_hDegen_via_analytic_explicit`, `g ≢ 0` recurses `g` to degree `0` via
`bound_via_trim_rec_explicit` at fuel `0` then `log_wronskian_arm_explicit`). -/
theorem log_step_multilinear_analytic_explicit {N : Nat} (c : PfaffianChain (N + 1))
    (a b : Real) (hab : a < b) (hcoh : c.IsCoherentOn a b)
    (h_top : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
        (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
    (h_tri : ∀ j : Fin (N + 1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (c.relations j) = 0)
    (Kih : MultiPoly N → Nat)
    (IH_ex : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn (chainRestrict c) r) a b (Kih r))
    (hAnalytic : ∀ r : MultiPoly (N + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b))
    (p : MultiPoly (N + 1))
    (hd_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ 1)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn c p) a b
      (logBaseE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih p) := by
  by_cases hd0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0
  · exact (degreeYtop_zero_explicit c p hd0 a b Kih IH_ex hne).mono (Nat.le_max_left _ _)
  · have hd1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 1 := by omega
    by_cases hcd_zero : ∀ z, a < z → z < b →
        (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
    · -- degree 1, c_D ≡ 0: trim to degree 0.
      have htrim := bound_via_trim_interval_rec_explicit c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) a b 0
        (fun r => Kih (MultiPoly.dropLastY r))
        (fun r hr hner => degreeYtop_zero_explicit c r (Nat.le_zero.mp hr) a b Kih IH_ex hner)
        p (by omega)
        (fun _ z hza hzb => by
          have h := getD_at_degreeY_eq_lcY_eval (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p z (c.chainValues z)
          rw [hd1] at h
          rw [h]; exact hcd_zero z hza hzb)
        hne
      have htrim' : BoundedZerosBy (pfaffianChainFn c p) a b
          (max (Kih (MultiPoly.dropLastY p))
            (Kih (MultiPoly.dropLastY (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))) := htrim
      refine htrim'.mono ?_
      unfold logBaseE
      omega
    · have hcd_nz : ∃ z, a < z ∧ z < b ∧
          (pfaffianChainFn c
            (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
        Classical.byContradiction fun hcon =>
          hcd_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
      have hK := degreeYtop_zero_explicit c
        (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
        (MultiPoly.degreeY_leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) a b Kih IH_ex hcd_nz
      by_cases hg_zero : ∀ z, a < z → z < b →
          (pfaffianChainFn c (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
      · -- g ≡ 0: the analytic leaf.
        refine (log_hDegen_via_analytic_explicit c a b hab hcoh p (hAnalytic p)
          (hAnalytic (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
          hg_zero hne _ hK).mono ?_
        unfold logBaseE
        omega
      · -- g ≢ 0: recurse g to degree 0, then the Wronskian-reduce arm.
        have hg_nz : ∃ z, a < z ∧ z < b ∧
            (pfaffianChainFn c
              (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hg_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
        have hg_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
            (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) ≤ 0 + 1 := by
          unfold logWronskianPoly
          have := degreeYtop_wronskian_le c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p
          omega
        have hg_lead : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
              (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) = 0 + 1 →
            ∀ (x : Real) (env : Fin (N + 1) → Real),
              MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).getD (0 + 1)
                (MultiPoly.const 0)) x env = 0 := by
          intro _ x env
          have hw := wronskian_leadY_eval_zero c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p x env
          rwa [hd1] at hw
        have hNg := bound_via_trim_rec_explicit c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) a b 0
          (fun r => Kih (MultiPoly.dropLastY r))
          (fun r hr hner => degreeYtop_zero_explicit c r (Nat.le_zero.mp hr) a b Kih IH_ex hner)
          (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) hg_le hg_lead hg_nz
        have hNg' : BoundedZerosBy
            (pfaffianChainFn c (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) a b
            (max (Kih (MultiPoly.dropLastY (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))
              (Kih (MultiPoly.dropLastY (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))))) := hNg
        refine (log_wronskian_arm_explicit c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p a b hab hcoh
          _ hNg' _ hK).mono ?_
        unfold logBaseE
        omega

/-! ## The mixed-chain log step, explicit form -/

set_option maxHeartbeats 4000000 in
/-- **The `degreeY_top` fuel induction (log arm), EXPLICIT.** Explicit-`K` analog of
`PfaffianLogGeneralDegree.log_step_general`: same MIXED-chain hypotheses (only a TOP-level log
relation is assumed; the rest of the chain is handled entirely through the depth-IH bound function
`Kih`), same case split (degree `≤ 1` multilinear base, degree `≥ 2` Wronskian dispatch), but the
conclusion is a named `Nat` (`logBoundE c top Kih D p`) instead of `∃M`. -/
theorem log_step_general_explicit {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (h_top : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
        (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
    (h_tri : ∀ j : Fin (N + 1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (c.relations j) = 0)
    (Kih : MultiPoly N → Nat)
    (IH_ex : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn (chainRestrict c) r) a b (Kih r))
    (hAnalytic : ∀ r : MultiPoly (N + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) :
    ∀ (D : Nat) (p : MultiPoly (N + 1)),
      MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ D →
      (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      BoundedZerosBy (pfaffianChainFn c p) a b
        (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D p) := by
  intro D
  induction D with
  | zero =>
    intro p hpD hne
    exact log_step_multilinear_analytic_explicit c a b hab hcoh h_top h_tri Kih IH_ex hAnalytic p
      (by omega) hne
  | succ D ih =>
    intro p hpD hne
    have hunfold : logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih (D + 1) p
        = max (logBaseE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih p)
            (max (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D p)
              (max (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                      (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
                (max (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                        (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
                     (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                        (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                          (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))
                  + 2 * Kih (MultiPoly.dropLastY
                      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) + 1))) := rfl
    by_cases hle1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ 1
    · refine (log_step_multilinear_analytic_explicit c a b hab hcoh h_top h_tri Kih IH_ex hAnalytic p
        hle1 hne).mono ?_
      rw [hunfold]
      omega
    · -- degreeY_top p ≥ 2, ≤ D + 1
      by_cases hcd_zero : ∀ z, a < z → z < b →
          (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
      · -- c_D ≡ 0: trim p pointwise, recurse via `ih`.
        have htrim := bound_via_trim_interval_rec_explicit c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) a b D
          (fun r => logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D r)
          (fun r hr hner => ih r hr hner) p hpD
          (fun hpEq z hza hzb => by
            have h := getD_at_degreeY_eq_lcY_eval (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p z
              (c.chainValues z)
            rw [hpEq] at h
            rw [h]; exact hcd_zero z hza hzb)
          hne
        have htrim' : BoundedZerosBy (pfaffianChainFn c p) a b
            (max (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D p)
              (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))) := htrim
        refine htrim'.mono ?_
        rw [hunfold]
        omega
      · -- c_D ≢ 0.
        have hcd_nz : ∃ z, a < z ∧ z < b ∧
            (pfaffianChainFn c (MultiPoly.leadingCoeffY
              (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hcd_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
        have hK := degreeYtop_zero_explicit c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) a b Kih IH_ex hcd_nz
        by_cases hg_zero : ∀ z, a < z → z < b →
            (pfaffianChainFn c
              (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
        · -- g ≡ 0: the analytic leaf.
          refine (log_hDegen_via_analytic_explicit c a b hab hcoh p (hAnalytic p)
            (hAnalytic (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
            hg_zero hne _ hK).mono ?_
          rw [hunfold]
          omega
        · -- g ≢ 0: Wronskian reduce, recursing on the (strictly lower degree) g.
          have hg_nz : ∃ z, a < z ∧ z < b ∧
              (pfaffianChainFn c
                (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hg_zero (fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩)
          have hg_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
              (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) ≤ D + 1 := by
            unfold logWronskianPoly
            have := degreeYtop_wronskian_le c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p
            omega
          have hg_lead : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) = D + 1 →
              ∀ (x : Real) (env : Fin (N + 1) → Real),
                MultiPoly.eval ((yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                  (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).getD (D + 1)
                  (MultiPoly.const 0)) x env = 0 := by
            intro hgeq x env
            have hg_wle : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
                ≤ MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p := by
              unfold logWronskianPoly
              exact degreeYtop_wronskian_le c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p
            have hDp : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = D + 1 := by omega
            have hw := wronskian_leadY_eval_zero c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p x env
            rw [hDp] at hw
            exact hw
          have hNg := bound_via_trim_rec_explicit c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) a b D
            (fun r => logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D r)
            (fun r hr hner => ih r hr hner)
            (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) hg_le hg_lead hg_nz
          have hNg' : BoundedZerosBy
              (pfaffianChainFn c (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) a b
              (max (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                      (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
                (logBoundE c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                  (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                    (logWronskianPoly c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))) := hNg
          refine (log_wronskian_arm_explicit c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p a b hab hcoh
            _ hNg' _ hK).mono ?_
          rw [hunfold]
          omega

end MachLib.EMLExplicitBound
