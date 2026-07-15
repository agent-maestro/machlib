import MachLib.EMLExplicitBound
import MachLib.PfaffianLogGeneralDegree
import MachLib.PfaffianExpTrim
import MachLib.PfaffianExpHard
import MachLib.PfaffianExpWronskian
import MachLib.WronskianProportional

/-!
# Explicit-K exp arm — the `degreeY_top` fuel recursion, MIXED chain (B4, explicit form)

`PfaffianExpHard.exp_step_general` is already the "mixed" exp step: it needs only a TOP-level exp
relation (`h_reltop : c.relations top = G · varY top`) and a black-box existential depth IH
(`IH_depth`) over `chainRestrict c` — unlike `PfaffianGeneralStepExplicit.pfaffian_bound_step_explicit`,
it never assumes the rest of the chain is exp-type. Its induction is a plain fuel recursion on
`degreeY_top p : Nat` (not the general chain's `chainNOrder5p_wf`), because the exp-elimination
(`expEliminate`) genuinely drops `degreeY_top` by one step at a time.

This file is the EXPLICIT-K form the axiom-deletion needs (AXIOM_AUDIT_V2.md §2c(2)): same case
structure as `exp_step_general`, but every `∃M` is replaced by a named `Nat` via
`EMLExplicitBound.BoundedZerosBy`, threaded through a depth-IH bound FUNCTION `Kih` (in place of the
existential `IH_depth`). `expBoundE` is the resulting bound, defined by structural recursion on `D`
(the fuel), taking the `max` over all four arms unconditionally — the proof then shows each arm's
actual requirement is one of the four disjuncts, promoted to the max via `BoundedZerosBy.mono`.
-/

namespace MachLib.EMLExplicitBound

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpEliminate
open MachLib.PfaffianLogLead
open MachLib.PfaffianExpWronskian
open MachLib.ChainExp2Trim MachLib.MultiPolyReconstruct

/-- **The explicit exp-arm bound.** Structural recursion on the fuel `D`; `p` is a plain argument (no
degree assumption baked into the def — every case is taken unconditionally via `max`, so this is
total). The four disjuncts mirror `exp_step_general`'s four arms:
`Kih (dropLastY p)` (degreeY_top p = 0), `expBoundE … D p` (p already fits under the smaller fuel),
`expBoundE … D (dropLeadingYAt top p)` (the `c_D ≡ 0` trim-and-recurse), and
`expBoundE … D (dropLeadingYAt top (expEliminate c G top p)) + 2 * Kih (dropLastY (leadingCoeffY top p)) + 1`
(the integrating-factor step, `Ne + 2K + 1`). -/
noncomputable def expBoundE {N : Nat} (c : PfaffianChain (N + 1)) (G : MultiPoly (N + 1))
    (top : Fin (N + 1)) (Kih : MultiPoly N → Nat) : Nat → MultiPoly (N + 1) → Nat
  | 0, p => Kih (MultiPoly.dropLastY p)
  | D + 1, p =>
      max (Kih (MultiPoly.dropLastY p))
        (max (expBoundE c G top Kih D p)
          (max (expBoundE c G top Kih D (dropLeadingYAt top p))
            (max (expBoundE c G top Kih D (expEliminate c G top p))
                 (expBoundE c G top Kih D (dropLeadingYAt top (expEliminate c G top p)))
              + 2 * Kih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY top p)) + 1)))

/-! ## Explicit-bound trim-and-recurse (generalize `EMLExplicitBound`'s arms to arbitrary degree) -/

/-- **Explicit-bound trim-and-recurse (everywhere-eval-zero leading term).** Explicit-`K` analog of
`PfaffianLogLead.bound_via_trim_rec`: given a family of explicit bounds `K r` valid whenever
`degreeY_top r ≤ D`, and — when `degreeY_top q = D + 1` — the degree-`(D+1)` coefficient eval-zero at
EVERY point, `q` is bounded by `max (K q) (K (dropLeadingYAt top q))` (covering both the
"already fits under `D`" and the "needs trimming" sub-cases uniformly, so the conclusion type does not
need to know in advance which one applies). -/
theorem bound_via_trim_rec_explicit {N : Nat} (c : PfaffianChain N) (top : Fin N) (a b : Real) (D : Nat)
    (K : MultiPoly N → Nat)
    (rec : ∀ r : MultiPoly N, MultiPoly.degreeY top r ≤ D →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn c r) a b (K r))
    (q : MultiPoly N)
    (hq_le : MultiPoly.degreeY top q ≤ D + 1)
    (h_lead : MultiPoly.degreeY top q = D + 1 →
        ∀ (x : Real) (env : Fin N → Real),
          MultiPoly.eval ((yCoeffsAt top q).getD (D + 1) (MultiPoly.const 0)) x env = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn c q) a b (max (K q) (K (dropLeadingYAt top q))) := by
  by_cases hqD : MultiPoly.degreeY top q ≤ D
  · exact (rec q hqD hne).mono (Nat.le_max_left _ _)
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
    have hMbound := rec (dropLeadingYAt top q) htrim_deg hne_trim
    have hqbound : BoundedZerosBy (pfaffianChainFn c q) a b (K (dropLeadingYAt top q)) := by
      intro zeros hnd hz
      apply hMbound zeros hnd
      intro z hzmem
      obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
      exact ⟨hza, hzb, by rw [pfaffianChainFn_trim_eval_gen c top q h_ne_list h_phantom z]; exact hzero⟩
    exact hqbound.mono (Nat.le_max_right _ _)

/-- **Explicit-bound trim-and-recurse (interval eval-zero).** Interval/pointwise version of
`bound_via_trim_rec_explicit`: only the WEAKER condition "degree-`(D+1)` coefficient eval-zero along the
chain on `(a,b)`" is required — what `c_D ≡ 0` on `(a,b)` supplies. Explicit-`K` analog of
`PfaffianLogLead.bound_via_trim_interval_rec`. -/
theorem bound_via_trim_interval_rec_explicit {N : Nat} (c : PfaffianChain N) (top : Fin N) (a b : Real)
    (D : Nat) (K : MultiPoly N → Nat)
    (rec : ∀ r : MultiPoly N, MultiPoly.degreeY top r ≤ D →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn c r) a b (K r))
    (q : MultiPoly N)
    (hq_le : MultiPoly.degreeY top q ≤ D + 1)
    (h_lead : MultiPoly.degreeY top q = D + 1 →
        ∀ z, a < z → z < b →
          MultiPoly.eval ((yCoeffsAt top q).getD (D + 1) (MultiPoly.const 0)) z (c.chainValues z) = 0)
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c q).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn c q) a b (max (K q) (K (dropLeadingYAt top q))) := by
  by_cases hqD : MultiPoly.degreeY top q ≤ D
  · exact (rec q hqD hne).mono (Nat.le_max_left _ _)
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
    have hMbound := rec (dropLeadingYAt top q) htrim_deg hne_trim
    have hqbound : BoundedZerosBy (pfaffianChainFn c q) a b (K (dropLeadingYAt top q)) := by
      intro zeros hnd hz
      apply hMbound zeros hnd
      intro z hzmem
      obtain ⟨hza, hzb, hzero⟩ := hz z hzmem
      exact ⟨hza, hzb, by rw [hpf_eq z hza hzb]; exact hzero⟩
    exact hqbound.mono (Nat.le_max_right _ _)

/-- **Explicit-bound exp-elimination trim.** Explicit-`K` analog of `PfaffianExpTrim.expEliminate_zeros_bound`:
for an exp top (`relations top = G·y_top`) and a barrier `p` with `degreeY_top p = D + 1`, the elimination
polynomial `expEliminate c G top p` — whose formal top degree is `D + 1` but whose leading coefficient
evaluates to 0 everywhere (`expEliminate_lcY_top_eval_zero`) — is bounded by
`max (K (expEliminate c G top p)) (K (dropLeadingYAt top (expEliminate c G top p)))`, given `K` is an
explicit bound family valid at top-degree `≤ D`. -/
theorem expEliminate_zeros_bound_explicit {N : Nat} (c : PfaffianChain N) (G : MultiPoly N) (top : Fin N)
    (h_reltop : c.relations top = MultiPoly.mul G (MultiPoly.varY top))
    (h_Gtop : MultiPoly.degreeY top G = 0)
    (h_tri : ∀ j : Fin N, j ≠ top → MultiPoly.degreeY top (c.relations j) = 0)
    (p : MultiPoly N) (D : Nat) (hDp : MultiPoly.degreeY top p = D + 1)
    (a b : Real) (K : MultiPoly N → Nat)
    (rec : ∀ r : MultiPoly N, MultiPoly.degreeY top r ≤ D →
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn c r) a b (K r))
    (hne : ∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c (expEliminate c G top p)).eval z ≠ 0) :
    BoundedZerosBy (pfaffianChainFn c (expEliminate c G top p)) a b
      (max (K (expEliminate c G top p)) (K (dropLeadingYAt top (expEliminate c G top p)))) := by
  have hEEdeg : MultiPoly.degreeY top (expEliminate c G top p) = D + 1 := by
    rw [expEliminate_degreeY_top_eq c G top h_reltop h_Gtop h_tri p, hDp]
  refine bound_via_trim_rec_explicit c top a b D K rec (expEliminate c G top p) (Nat.le_of_eq hEEdeg) ?_ hne
  intro _hq1 x env
  rw [← hEEdeg, getD_at_degreeY_eq_lcY_eval top (expEliminate c G top p) x env]
  exact expEliminate_lcY_top_eval_zero c G top h_reltop h_Gtop h_tri p x env

/-! ## The mixed-chain exp step, explicit form -/

set_option maxHeartbeats 4000000 in
/-- **The `degreeY_top` fuel induction (exp arm), EXPLICIT.** Explicit-`K` analog of
`PfaffianExpHard.exp_step_general`: same MIXED-chain hypotheses (only a TOP-level exp relation is
assumed; the rest of the chain is handled entirely through the depth-IH bound function `Kih`, never
through `IsExpChain`), same four-way case split, but the conclusion is a named `Nat`
(`expBoundE c G top Kih D p`) instead of `∃M`. -/
theorem exp_step_general_explicit {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (G : MultiPoly (N + 1))
    (h_reltop : c.relations (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
        = MultiPoly.mul G (MultiPoly.varY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))))
    (hG : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) G = 0)
    (h_tri : ∀ j : Fin (N + 1), j ≠ (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (c.relations j) = 0)
    (hyt : ∀ z, a < z → z < b →
        MultiPoly.eval (MultiPoly.varY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) z (c.chainValues z) ≠ 0)
    (Kih : MultiPoly N → Nat)
    (IH_ex : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        BoundedZerosBy (pfaffianChainFn (chainRestrict c) r) a b (Kih r))
    (hAnalytic : ∀ r : MultiPoly (N + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) :
    ∀ (D : Nat) (p : MultiPoly (N + 1)),
      MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ D →
      (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      BoundedZerosBy (pfaffianChainFn c p) a b
        (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D p) := by
  intro D
  induction D with
  | zero =>
    intro p hpD hne
    exact degreeYtop_zero_explicit c p (Nat.le_zero.mp hpD) a b Kih IH_ex hne
  | succ D ih =>
    intro p hpD hne
    have hunfold : expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih (D + 1) p
        = max (Kih (MultiPoly.dropLastY p))
            (max (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D p)
              (max (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                      (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
                (max (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                        (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
                     (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                        (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                          (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))
                  + 2 * Kih (MultiPoly.dropLastY
                      (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) + 1))) := rfl
    by_cases hd0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0
    · exact (degreeYtop_zero_explicit c p hd0 a b Kih IH_ex hne).mono (Nat.le_max_left _ _)
    · -- degreeY_top p ≥ 1
      have hdpos : 0 < MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p :=
        Nat.pos_of_ne_zero hd0
      by_cases hcd_zero : ∀ z, a < z → z < b →
          (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
      · -- c_D ≡ 0 on (a,b): trim p pointwise, recurse via `ih`.
        have htrim := bound_via_trim_interval_rec_explicit c
          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) a b D
          (fun r => expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D r)
          (fun r hr hner => ih r hr hner) p hpD
          (fun hpEq z hza hzb => by
            have h := getD_at_degreeY_eq_lcY_eval (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p z
              (c.chainValues z)
            rw [hpEq] at h
            rw [h]; exact hcd_zero z hza hzb)
          hne
        have htrim' : BoundedZerosBy (pfaffianChainFn c p) a b
            (max (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D p)
              (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))) := htrim
        refine htrim'.mono ?_
        rw [hunfold]
        omega
      · -- c_D ≢ 0: bound c_D's zeros by K (top-free ⇒ Kih, via `degreeYtop_zero_explicit`).
        have hcd_nz : ∃ z, a < z ∧ z < b ∧
            (pfaffianChainFn c (MultiPoly.leadingCoeffY
              (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hcd_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
        have hK := degreeYtop_zero_explicit c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) a b Kih IH_ex hcd_nz
        by_cases hEE_zero : ∀ z, a < z → z < b →
            (pfaffianChainFn c (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
        · -- expEliminate ≡ 0: the degenerate leaf via Wronskian proportionality.
          have hleaf : BoundedZerosBy (pfaffianChainFn c p) a b
              (Kih (MultiPoly.dropLastY
                (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))) :=
            wronskian_arm_explicit
            (pfaffianChainFn c p).eval
            (pfaffianChainFn c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
              (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                  (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))).eval
            (fun x => (pfaffianChainFn c (chainTotalDeriv c p)).eval x)
            (fun x => (pfaffianChainFn c (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
              (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                  (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))).eval x)
            a b hab (hAnalytic p)
            (hAnalytic (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
              (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                  (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))
            (fun x h1 h2 => multiPolyHasDerivAt_eval_with_chain c p x (hcoh x h1 h2))
            (fun x h1 h2 => multiPolyHasDerivAt_eval_with_chain c (MultiPoly.mul (MultiPoly.pow
              (MultiPoly.varY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                  (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) x (hcoh x h1 h2))
            (by
              intro x h1 h2
              have hnum := expEliminate_wronskian_numerator c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                h_reltop p x (c.chainValues x)
              have hEE0 : MultiPoly.eval (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
                  x (c.chainValues x) = 0 := hEE_zero x h1 h2
              show MultiPoly.eval (chainTotalDeriv c p) x (c.chainValues x)
                    * MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                      (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) x (c.chainValues x)
                  - MultiPoly.eval p x (c.chainValues x)
                    * MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                      (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))) x (c.chainValues x) = 0
              rw [show MultiPoly.eval (chainTotalDeriv c p) x (c.chainValues x)
                    * MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                      (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) x (c.chainValues x)
                    - MultiPoly.eval p x (c.chainValues x)
                    * MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                      (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))) x (c.chainValues x)
                    = MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                            (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) x (c.chainValues x)
                      * MultiPoly.eval (chainTotalDeriv c p) x (c.chainValues x)
                    - MultiPoly.eval (chainTotalDeriv c (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                        (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                          (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                            (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))) x (c.chainValues x)
                      * MultiPoly.eval p x (c.chainValues x) from by mach_ring, hnum, hEE0, Real.mul_zero])
            (by obtain ⟨z, hz1, hz2, hzne⟩ := hne; exact ⟨z, ⟨hz1, hz2⟩, hzne⟩)
            (Kih (MultiPoly.dropLastY (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))
            (by
              intro zeros hnd hz
              apply hK zeros hnd
              intro z hzm
              obtain ⟨hza, hzb, hVz⟩ := hz z hzm
              refine ⟨hza, hzb, ?_⟩
              have hVz' : MultiPoly.eval (MultiPoly.mul (MultiPoly.pow (MultiPoly.varY
                  (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) (MultiPoly.degreeY
                    (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) (MultiPoly.leadingCoeffY
                      (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) z (c.chainValues z) = 0 := hVz
              rw [MultiPoly.eval_mul] at hVz'
              show MultiPoly.eval (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
                z (c.chainValues z) = 0
              exact mul_eq_zero_of_factor_ne_zero
                (eval_pow_ne_zero (MultiPoly.varY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)))
                  z (c.chainValues z) (hyt z hza hzb) _) hVz')
          refine hleaf.mono ?_
          rw [hunfold]
          omega
        · -- expEliminate ≢ 0: explicit exp-elimination trim (Ne), then the integrating-factor arm.
          have hEE_nz : ∃ z, a < z ∧ z < b ∧
              (pfaffianChainFn c (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hEE_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
          have hDpD : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p - 1 ≤ D := by omega
          have hDp : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p
              = (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p - 1) + 1 := by omega
          have hNe := expEliminate_zeros_bound_explicit c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
            h_reltop hG h_tri p
            (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p - 1) hDp a b
            (fun r => expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D r)
            (fun r hr hner => ih r (Nat.le_trans hr hDpD) hner) hEE_nz
          have hNe' : BoundedZerosBy
              (pfaffianChainFn c (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)) a b
              (max (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                      (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p))
                (expBoundE c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) Kih D
                  (dropLeadingYAt (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
                    (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)))) := hNe
          refine (integrating_arm_explicit c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) h_reltop p a b hab hcoh
            hyt _ hNe' _ hK).mono ?_
          rw [hunfold]
          omega

end MachLib.EMLExplicitBound
