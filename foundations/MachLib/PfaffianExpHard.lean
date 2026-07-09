import MachLib.PfaffianExpWronskian
import MachLib.PfaffianExpTrim
import MachLib.EMLBarrierBound

/-!
# `exp_hard` — the degreeY_top recursion, assembled (B4). exp arm CLOSED.

The capstone of the resolved `exp_hard` construction. B1–B3 built the pieces:

* **B1** `expEliminate` — top exponential eliminated at the polynomial level (leading coeff eval-zero).
* **B2** `expEliminate_zeros_bound` — the eval-zero trim: a depth-`≤D-1` recursor bounds `expEliminate`'s zeros.
* **B3** `expEliminate_reduce_full` — the exp-Wronskian count: `#zeros(pf c p) ≤ #zeros(pf c (expEliminate)) +
  #zeros(c_D) + 1`.

B4 assembles them into a **fuel induction on `degreeY_top p`** — the exact structure of the log arm's
`log_step_general`, with the log Wronskian swapped for the exp one:

* `degreeY_top p = 0` → top-free → the depth IH (`pfaffianChainFn_bound_of_degreeYtop_zero`).
* `c_D ≡ 0` on `(a,b)` → trim `p` (`bound_via_trim_interval_rec`), recurse at lower `degreeY_top`.
* `c_D ≢ 0`:
  * bound `c_D`'s zeros by `K` (top-free → depth IH);
  * `expEliminate ≡ 0` → the degenerate leaf: `f` and `V = y_top^D·c_D` are Wronskian-proportional, so
    (analyticity) `f`'s zeros are bounded by `c_D`'s (`wronskian_zero_bounded_zeros`);
  * `expEliminate ≢ 0` → B2 bounds `expEliminate`'s zeros via the `degreeY_top` IH, B3 lifts to `p`.

This discharges the `exp_hard` hypothesis of `combined_descent_3_of_exp_hard`, so — with the log arm already
proven (`log_hard_proof`) — the whole EML barrier bound (`eml_eval_boundedZeros`) becomes UNCONDITIONAL,
resting on `rolle` alone. `exp_step_general`/`exp_hard_proof` are `rolle`-grounded (the analytic core) and
sorryAx-free / `zero_count_bound_classical`-free.
-/

namespace MachLib.PfaffianExpHard

open MachLib.Real
open MachLib.MultiPolyMod MachLib.MultiPolyMod.MultiPoly
open MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianChain MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce
open MachLib.PfaffianExpEliminate
open MachLib.PfaffianExpTrim
open MachLib.PfaffianExpWronskian
open MachLib.PfaffianLogLead
open MachLib.IterExpTopIdentity

/-- **B4 — the `degreeY_top` fuel induction (exp arm).** For an exp top (`relations top = G·y_top`), any
barrier `p` with `degreeY_top p ≤ D` and somewhere non-vanishing has boundedly many zeros — given coherence,
triangularity, exp non-vanishing (`hyt`), the depth IH, and analyticity of every sub-barrier. Structural exp
analog of `log_step_general`. -/
theorem exp_step_general {N : Nat} (c : PfaffianChain (N + 1)) (a b : Real) (hab : a < b)
    (hcoh : c.IsCoherentOn a b)
    (G : MultiPoly (N + 1))
    (h_reltop : c.relations (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
        = MultiPoly.mul G (MultiPoly.varY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))))
    (hG : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) G = 0)
    (h_tri : ∀ j : Fin (N + 1), j ≠ (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) →
        MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) (c.relations j) = 0)
    (hyt : ∀ z, a < z → z < b →
        MultiPoly.eval (MultiPoly.varY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))) z (c.chainValues z) ≠ 0)
    (IH_depth : ∀ r : MultiPoly N,
        (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z ≠ 0) →
        ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
          (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) r).eval z = 0) → zeros.length ≤ M)
    (hAnalytic : ∀ r : MultiPoly (N + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) :
    ∀ (D : Nat) (p : MultiPoly (N + 1)),
      MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p ≤ D →
      (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
      ∃ M : Nat, ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z = 0) → zeros.length ≤ M := by
  intro D
  induction D with
  | zero =>
    intro p hpD hne
    exact pfaffianChainFn_bound_of_degreeYtop_zero c p (Nat.le_zero.mp hpD) a b hab hne IH_depth
  | succ D ih =>
    intro p hpD hne
    by_cases hd0 : MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p = 0
    · exact pfaffianChainFn_bound_of_degreeYtop_zero c p hd0 a b hab hne IH_depth
    · -- degreeY_top p ≥ 1
      have hdpos : 0 < MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p := by omega
      by_cases hcd_zero : ∀ z, a < z → z < b →
          (pfaffianChainFn c (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
      · -- c_D ≡ 0 on (a,b): trim p pointwise, recurse.
        refine bound_via_trim_interval_rec c (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) a b D ih p hpD ?_ hne
        intro hpEq z hza hzb
        have h := getD_at_degreeY_eq_lcY_eval (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p z (c.chainValues z)
        rw [hpEq] at h
        rw [h]; exact hcd_zero z hza hzb
      · -- c_D ≢ 0: bound c_D's zeros by K (top-free ⇒ depth IH).
        have hcd_nz : ∃ z, a < z ∧ z < b ∧
            (pfaffianChainFn c (MultiPoly.leadingCoeffY
              (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
          Classical.byContradiction fun hcon =>
            hcd_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
        obtain ⟨K, hK⟩ := pfaffianChainFn_bound_of_degreeYtop_zero c
          (MultiPoly.leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)
          (MultiPoly.degreeY_leadingCoeffY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p) a b hab hcd_nz IH_depth
        by_cases hEE_zero : ∀ z, a < z → z < b →
            (pfaffianChainFn c (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z = 0
        · -- expEliminate ≡ 0: the degenerate leaf via Wronskian proportionality.
          refine wronskian_zero_bounded_zeros
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
            ?hW ?hFne K ?hGbound
          · -- Wronskian numerator = y_top^D · expEliminate = 0
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
                  * MultiPoly.eval p x (c.chainValues x) from by mach_ring, hnum, hEE0, Real.mul_zero]
          · -- non-vanishing of f
            obtain ⟨z, hz1, hz2, hzne⟩ := hne
            exact ⟨z, ⟨hz1, hz2⟩, hzne⟩
          · -- zeros of V ⇒ zeros of c_D (y_top^D ≠ 0), bounded by K
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
                z (c.chainValues z) (hyt z hza hzb) _) hVz'
        · -- expEliminate ≢ 0: B2 bounds it (degreeY_top IH), B3 lifts to p.
          have hEE_nz : ∃ z, a < z ∧ z < b ∧
              (pfaffianChainFn c (expEliminate c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p)).eval z ≠ 0 :=
            Classical.byContradiction fun hcon =>
              hEE_zero (fun z hza hzb => Classical.byContradiction fun hzne => hcon ⟨z, hza, hzb, hzne⟩)
          obtain ⟨Ne, hNe⟩ := expEliminate_zeros_bound c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
            h_reltop hG h_tri p (MultiPoly.degreeY (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1)) p - 1)
            (by omega) a b (fun r hr hne_r => ih r (Nat.le_trans hr (by omega)) hne_r) hEE_nz
          exact ⟨Ne + K + 1, expEliminate_reduce_full c G (⟨N, Nat.lt_succ_self N⟩ : Fin (N + 1))
            h_reltop p a b hab hcoh hyt Ne hNe K hK⟩

/-- **`exp_hard` — the general-degree exp core, PROVEN.** Exactly the `exp_hard` hypothesis of
`combined_descent_3_of_exp_hard`, discharged: derive exp non-vanishing from `PosExceptLog` (the exp top has
`degreeY_top (relations top) = 1 ≠ 0`, forcing `0 < evals top`), then instantiate `exp_step_general` at
`D := degreeY_top p`. Retires the exp side of the classical descent. -/
theorem exp_hard_proof (a b : Real) (hab : a < b) :
    ∀ (k : Nat) (c : PfaffianChain (k + 1)),
        PfaffianExpLogRecip.IsExpLogRecipW c a b → c.IsCoherentOn a b →
        PfaffianExpLogRecip.PosExceptLog c a b →
        (∀ r : MultiPoly (k + 1), IsAnalyticOnReals (pfaffianChainFn c r).eval (Icc a b)) →
        (∃ G : MultiPoly (k + 1), MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ G = 0
            ∧ c.relations ⟨k, Nat.lt_succ_self k⟩
                = MultiPoly.mul G (MultiPoly.varY ⟨k, Nat.lt_succ_self k⟩)) →
        (∀ j : Fin (k + 1), j ≠ ⟨k, Nat.lt_succ_self k⟩ →
            MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ (c.relations j) = 0) →
        (∀ q : MultiPoly k,
            (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn (chainRestrict c) q).eval z ≠ 0) →
            PfaffianExpRecipW.BoundedZeros (pfaffianChainFn (chainRestrict c) q) a b) →
        ∀ p : MultiPoly (k + 1),
          (∃ z, a < z ∧ z < b ∧ (pfaffianChainFn c p).eval z ≠ 0) →
          0 < MultiPoly.degreeY ⟨k, Nat.lt_succ_self k⟩ p →
          PfaffianExpRecipW.BoundedZeros (pfaffianChainFn c p) a b := by
  intro k c _hW hcoh hpos hAn ⟨G, hG, h_reltop⟩ h_tri IH_depth p hne _hdpos
  have hyt : ∀ z, a < z → z < b →
      MultiPoly.eval (MultiPoly.varY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))) z (c.chainValues z) ≠ 0 := by
    intro z hza hzb
    rcases hpos z hza hzb (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) with hlog | hp
    · exfalso
      rw [h_reltop, degreeY_mul' (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) G
        (MultiPoly.varY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)))] at hlog
      have hv : MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))
          (MultiPoly.varY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))) = 1 := by
        show (if (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ then (1 : Nat) else 0) = 1
        simp
      omega
    · have hev : MultiPoly.eval (MultiPoly.varY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1))) z (c.chainValues z)
          = c.evals (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) z := by
        rw [MultiPoly.eval_varY]; rfl
      rw [hev]; exact ne_of_gt hp
  exact exp_step_general c a b hab hcoh G h_reltop hG h_tri hyt IH_depth hAn
    (MultiPoly.degreeY (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) p) p (Nat.le_refl _) hne

end MachLib.PfaffianExpHard

/-! ## The EML barrier bound, now UNCONDITIONAL (both classical arms proven) -/

namespace MachLib

open MachLib.Real
open MachLib.MultiPolyMod MachLib.PfaffianChainMod MachLib.PfaffianChainMod.PfaffianFn
open MachLib.PfaffianGeneralReduce MachLib.PfaffianExpLogRecip

/-- **The EML value function has boundedly many zeros — UNCONDITIONAL on the classical steps.**
`eml_eval_boundedZeros` with its descent hypothesis discharged: the exp arm by
`PfaffianExpHard.exp_hard_proof`, the log arm by `log_hard_proof`, assembled through
`combined_descent_3_of_exp_hard`. Given `LogArgPosOn t (Icc a b)`, any EML tree `t` somewhere non-vanishing
on `(a,b)` has at most `K` zeros there. The sole special axiom is `rolle`. -/
theorem eml_eval_boundedZeros_unconditional (t : EMLTree) (a b : Real) (hab : a < b)
    (hlog : LogArgPosOn t (Icc a b))
    (hne : ∃ z, a < z ∧ z < b ∧ t.eval z ≠ 0) :
    ∃ K : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ t.eval z = 0) → zeros.length ≤ K :=
  eml_eval_boundedZeros t a b
    (combined_descent_3_of_exp_hard a b hab (PfaffianExpHard.exp_hard_proof a b hab))
    hlog hne

end MachLib
