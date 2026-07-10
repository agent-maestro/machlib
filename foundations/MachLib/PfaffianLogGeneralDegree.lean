import MachLib.PfaffianLogDegenerate
import MachLib.PfaffianExpLogStepReduce

/-!
# General-degree log step — closing `log_hard`

`log_step_multilinear_analytic` (`PfaffianLogDegenerate`) closes the log arm for
`degreeY_top p ≤ 1`. This file lifts it to **arbitrary degree**, discharging the
degree>0 core `log_hard` in full (`log_hard_proof`).

The move is a **fuel induction on `degreeY_top p`** (no custom well-founded order
needed — unlike the exp tower, whose canonical `chainNMeasureEI` order is required
because its reduct preserves the syntactic top degree). For a LOG-type top, the
Wronskian `g = c_D·cTD(p) − cTD(c_D)·p` has its degree-`D` coefficient eval-zero
(`wronskian_leadY_eval_zero`) and `degreeY_top g ≤ D` (`degreeYtop_wronskian_le`),
so after trimming the phantom leading term `g` has honest top-degree `< D` — a
strict drop the fuel measures directly.

Dispatch at `degreeY_top p = D ≥ 2` (mirrors `log_step_multilinear`, but every
"reduce to lower degree" target goes to the **recursion** instead of the depth IH):

* `c_D ≡ 0` on `(a,b)`  → trim `p` (pointwise) to degree `< D`, recurse.
* `c_D ≢ 0`, `g ≡ 0`     → `log_hDegen_via_analytic` (the isolated analytic leaf).
* `c_D ≢ 0`, `g ≢ 0`     → `log_wronskian_reduce_full`: `K = #zeros(c_D)` from the
  depth IH (top-free), `Ng = #zeros(g)` from the recursion (`g` trims to degree `< D`).

The two `bound_via_trim_*_rec` helpers generalize `bound_via_trim` /
`bound_via_trim_interval` from "trim to top-free ⇒ depth IH" to "trim one degree ⇒
recursion". No new axioms; the analytic content stays confined to the `g ≡ 0` leaf.
-/

namespace MachLib
namespace PfaffianLogLead

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce MachLib.IterExpDepthN

/-! ## Recursing trim helpers (generalize `bound_via_trim` to arbitrary degree) -/

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct in
/-- **Trim-and-recurse (everywhere-eval-zero leading term).** If `degreeY_top q ≤ D+1`
and — when `= D+1` — its degree-`D+1` coefficient is eval-zero at every point, then `q`
reduces to a polynomial of top-degree `≤ D` with the same value along the chain, and the
recursion `rec` (valid at top-degree `≤ D`) bounds its zeros. General-degree version of
`bound_via_trim` (there the reduct is top-free and `rec` is the depth IH). -/
theorem bound_via_trim_rec {N : Nat} (c : PfaffianChain N) (top : Fin N) (a b : Real) (D : Nat)
    (rec : ∀ r : MultiPoly N, MultiPoly.degreeY top r ≤ D →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z = 0) → zeros.length ≤ M)
    (q : MultiPoly N)
    (hq_le : MultiPoly.degreeY top q ≤ D + 1)
    (h_lead : MultiPoly.degreeY top q = D + 1 →
        ∀ (x : Real) (env : Fin N → Real),
          MultiPoly.eval ((yCoeffsAt top q).getD (D + 1) (MultiPoly.const 0)) x env = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ M := by
  by_cases hqD : MultiPoly.degreeY top q ≤ D
  · exact rec q hqD hne
  · have hq1 : MultiPoly.degreeY top q = D + 1 := by omega
    have h_ne_list : yCoeffsAt top q ≠ [] := by
      intro h; have := yCoeffsAt_length_eq top q; rw [h] at this; simp at this
    have h_phantom : ∀ (x : Real) (env : Fin N → Real),
        MultiPoly.eval ((yCoeffsAt top q).getLast h_ne_list) x env = 0 := by
      intro x env
      have hlen : (yCoeffsAt top q).length - 1 = D + 1 := by
        have h := yCoeffsAt_length_eq top q; omega
      have hgl := list_getD_pred_eq_getLast (yCoeffsAt top q) (MultiPoly.const 0) h_ne_list
      rw [hlen] at hgl
      rw [← hgl]; exact h_lead hq1 x env
    have htrim_deg : MultiPoly.degreeY top (dropLeadingYAt top q) ≤ D := by
      have := degreeY_dropLeadingYAt_lt top q (by omega); omega
    have hne_trim : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (dropLeadingYAt top q)).eval z ≠ 0 := by
      obtain ⟨z, hza, hzb, hzne⟩ := hne
      exact ⟨z, hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c top q h_ne_list h_phantom z]; exact hzne⟩
    obtain ⟨M, hM⟩ := rec (dropLeadingYAt top q) htrim_deg hne_trim
    refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z hzmem => ?_)⟩
    obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
    exact ⟨hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c top q h_ne_list h_phantom z]; exact hzero⟩

open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct in
/-- **Trim-and-recurse (leading term eval-zero on the interval).** Interval/pointwise
version of `bound_via_trim_rec`: only the WEAKER condition "degree-`D+1` coefficient
eval-zero along the chain on `(a,b)`" is required (what `c_D ≡ 0` on `(a,b)` supplies).
General-degree version of `bound_via_trim_interval`. -/
theorem bound_via_trim_interval_rec {N : Nat} (c : PfaffianChain N) (top : Fin N) (a b : Real) (D : Nat)
    (rec : ∀ r : MultiPoly N, MultiPoly.degreeY top r ≤ D →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z = 0) → zeros.length ≤ M)
    (q : MultiPoly N)
    (hq_le : MultiPoly.degreeY top q ≤ D + 1)
    (h_lead : MultiPoly.degreeY top q = D + 1 →
        ∀ z, a < z → z < b →
          MultiPoly.eval ((yCoeffsAt top q).getD (D + 1) (MultiPoly.const 0)) z (c.chainValues z) = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) :
    ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z = 0) → zeros.length ≤ M := by
  by_cases hqD : MultiPoly.degreeY top q ≤ D
  · exact rec q hqD hne
  · have hq1 : MultiPoly.degreeY top q = D + 1 := by omega
    have h_ne_list : yCoeffsAt top q ≠ [] := by
      intro h; have := yCoeffsAt_length_eq top q; rw [h] at this; simp at this
    have hgl_eq : (yCoeffsAt top q).getLast h_ne_list
        = (yCoeffsAt top q).getD (D + 1) (MultiPoly.const 0) := by
      have hlen : (yCoeffsAt top q).length - 1 = D + 1 := by
        have h := yCoeffsAt_length_eq top q; omega
      have hgl := list_getD_pred_eq_getLast (yCoeffsAt top q) (MultiPoly.const 0) h_ne_list
      rw [hlen] at hgl; exact hgl.symm
    have htrim_deg : MultiPoly.degreeY top (dropLeadingYAt top q) ≤ D := by
      have := degreeY_dropLeadingYAt_lt top q (by omega); omega
    have hpf_eq : ∀ z, a < z → z < b →
        (pfaffianChainFn c (dropLeadingYAt top q)).eval z = (pfaffianChainFn c q).eval z := by
      intro z hza hzb
      refine pfaffianChainFn_trim_eval_pt c top q h_ne_list z ?_
      rw [hgl_eq]; exact h_lead hq1 z hza hzb
    have hne_trim : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (dropLeadingYAt top q)).eval z ≠ 0 := by
      obtain ⟨z, hza, hzb, hzne⟩ := hne; exact ⟨z, hza, hzb, by rw [hpf_eq z hza hzb]; exact hzne⟩
    obtain ⟨M, hM⟩ := rec (dropLeadingYAt top q) htrim_deg hne_trim
    refine ⟨M, fun zeros hnd hz => hM zeros hnd (fun z hzmem => ?_)⟩
    obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
    exact ⟨hza, hzb, by rw [hpf_eq z hza hzb]; exact hzero⟩

end PfaffianLogLead

/-! ## The general-degree log step -/

open MachLib.Real MultiPolyMod MultiPolyMod.MultiPoly PfaffianChainMod
  PfaffianChainMod.PfaffianFn PfaffianGeneralReduce

/-- **General-degree log step.** For a LOG-type top, ANY barrier `p` (any degree) has
finitely many zeros on `(a,b)` where it is somewhere non-vanishing — given coherence,
triangularity, the depth IH, and analyticity of every sub-barrier (`hAnalytic`, supplied
by the encoder). Proven by fuel induction on `degreeY_top p`: `≤ 1` is
`log_step_multilinear_analytic`; `≥ 2` reduces via the Wronskian to strictly lower
top-degree (recursion), the depth IH (leading coefficient), and the single `g ≡ 0`
analytic leaf. This closes `log_hard` for arbitrary degree. -/
theorem log_step_general {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (h_top : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
        (c.relations ⟨N, Nat.lt_succ_self N⟩) = 0)
    (h_tri : ∀ j : Fin (N + 1), j ≠ ⟨N, Nat.lt_succ_self N⟩ →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (c.relations j) = 0)
    (IH_depth : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧
            (pfaffianChainFn (chainRestrict c) r).eval z = 0) → zeros.length ≤ M)
    (hAnalytic : ∀ r : MultiPoly (N + 1),
        IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) :
    ∀ (D : Nat) (p : MultiPoly (N + 1)),
      MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ D →
      (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  intro D
  induction D with
  | zero =>
    intro p hpD hne
    exact log_step_multilinear_analytic c a b hab hcoh h_top h_tri IH_depth hAnalytic p (by omega) hne
  | succ D ih =>
    intro p hpD hne
    by_cases hle1 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ 1
    · exact log_step_multilinear_analytic c a b hab hcoh h_top h_tri IH_depth hAnalytic p hle1 hne
    · -- degreeY_top p ≥ 2, ≤ D + 1
      by_cases hcd_zero : ∀ z, a < z → z < b →
          (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
      · -- c_D ≡ 0 on (a,b): trim p pointwise, recurse.
        refine PfaffianLogLead.bound_via_trim_interval_rec c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
          a b D ih p hpD ?_ hne
        intro hpEq z hza hzb
        have h := getD_at_degreeY_eq_lcY_eval (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p z (c.chainValues z)
        rw [hpEq] at h
        rw [h]; exact hcd_zero z hza hzb
      · -- c_D ≢ 0.
        have hcd_nz : ∃ z, a < z ∧ z < b ∧
            (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hcd_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
        obtain ⟨K, hK⟩ := pfaffianChainFn_bound_of_degreeYtop_zero c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) a b hab hcd_nz IH_depth
        by_cases hg_zero : ∀ z, a < z → z < b →
            (pfaffianChainFn c (MultiPoly.sub
              (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) (chainTotalDeriv c p))
              (MultiPoly.mul (chainTotalDeriv c
                (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) p))).eval z = 0
        · -- g ≡ 0: the analytic leaf.
          exact log_hDegen_via_analytic c a b hab hcoh p (hAnalytic p)
            (hAnalytic (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
            hg_zero hne K hK
        · -- g ≢ 0: Wronskian reduce, recursing on the (strictly lower degree) g.
          have hg_nz : ∃ z, a < z ∧ z < b ∧
              (pfaffianChainFn c (MultiPoly.sub
                (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) (chainTotalDeriv c p))
                (MultiPoly.mul (chainTotalDeriv c
                  (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) p))).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hg_zero (fun z hza hzb => Classical.byContradiction fun hz0 => hcon ⟨z, hza, hzb, hz0⟩)
          have hg_le : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (MultiPoly.sub
              (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) (chainTotalDeriv c p))
              (MultiPoly.mul (chainTotalDeriv c
                (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) p)) ≤ D + 1 := by
            have := PfaffianLogLead.degreeYtop_wronskian_le c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p
            omega
          have hg_lead : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (MultiPoly.sub
                (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) (chainTotalDeriv c p))
                (MultiPoly.mul (chainTotalDeriv c
                  (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) p)) = D + 1 →
              ∀ (x : Real) (env : Fin (N + 1) → Real),
                MultiPoly.eval ((MultiPoly.yCoeffsAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (MultiPoly.sub
                  (MultiPoly.mul (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) (chainTotalDeriv c p))
                  (MultiPoly.mul (chainTotalDeriv c
                    (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) p))).getD (D + 1) (MultiPoly.const 0)) x env = 0 := by
            intro hgeq x env
            have hg_wle := PfaffianLogLead.degreeYtop_wronskian_le c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p
            have hDp : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = D + 1 := by omega
            have hw := PfaffianLogLead.wronskian_leadY_eval_zero c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_top h_tri p x env
            rw [hDp] at hw
            exact hw
          obtain ⟨Ng, hNg⟩ := PfaffianLogLead.bound_via_trim_rec c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
            a b D ih _ hg_le hg_lead hg_nz
          exact ⟨Ng + 2 * K + 1, PfaffianLogLead.log_wronskian_reduce_full c
            (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p a b hab hcoh Ng hNg K hK⟩

/-! ## `log_hard` discharged -/

/-- **`log_hard` — the general-degree log core, PROVEN.** Exactly the `log_hard`
hypothesis of `combined_descent_3_of_hard`, discharged: instantiate `log_step_general`
at `D := degreeY_top p`. Retires the log side of the classical descent — the whole EML
barrier bound now rests on `exp_hard` alone. -/
theorem log_hard_proof (a b : Real) (hab : a < b) :
    ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        PfaffianExpLogRecip.IsExpLogRecipW c a b → c.IsCoherentOn a b →
        PfaffianExpLogRecip.PosExceptLog c a b →
        (∀ r : MultiPoly (k + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) →
        (MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations ⟨k, Nat.lt_succ_self k⟩) = 0) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            PfaffianExpRecipW.BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          0 < MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ p →
          PfaffianExpRecipW.BoundedZeros (pfaffianChainFn c p) a b := by
  intro k c _hW hcoh _hpos hAn h_top h_tri IH_depth p hne _hdpos
  exact log_step_general c a b hab hcoh h_top h_tri IH_depth hAn
    (MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ p) p (Nat.le_refl _) hne

end MachLib

/-! ## The 3-type descent, now resting on `exp_hard` ALONE -/

namespace MachLib.PfaffianExpLogRecip
open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PfaffianChainMod
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpRecipW

/-- **The whole EML/3-type barrier bound, conditional on `exp_hard` ONLY.**
`combined_descent_3_of_hard` with its `log_hard` argument discharged by the now-proven
`log_hard_proof`. Everything on the log side — base, reciprocal arm, dispatch, recursion,
the degree-0 discharge, positivity/analyticity threading, AND the general-degree WF
reduction — is proven; the sole remaining classical obligation is `exp_hard`
(the `degreeY_top > 0` exp arm). -/
theorem combined_descent_3_of_exp_hard (a b : Real) (hab : a < b)
    (exp_hard : ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        IsExpLogRecipW c a b → c.IsCoherentOn a b →
        PosExceptLog c a b →
        (∀ r : MultiPoly (k + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) →
        (∃ G : MultiPoly (k + 1), MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ G = 0
            ∧ c.relations ⟨k, Nat.lt_succ_self k⟩
                = MultiPoly.mul G (MultiPoly.varY ⟨k, Nat.lt_succ_self k⟩)) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          0 < MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ p →
          BoundedZeros (pfaffianChainFn c p) a b) :
    ∀ (N : Nat) (c : PfaffianChain N), IsExpLogRecipW c a b → c.IsCoherentOn a b →
      PosExceptLog c a b →
      (∀ r : MultiPoly N, IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) →
      ∀ (p : MultiPoly N),
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
        BoundedZeros (pfaffianChainFn c p) a b :=
  combined_descent_3_of_hard a b hab exp_hard (MachLib.log_hard_proof a b hab)

end MachLib.PfaffianExpLogRecip
