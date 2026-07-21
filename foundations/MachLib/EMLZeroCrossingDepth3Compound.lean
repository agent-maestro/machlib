import MachLib.EMLZeroCrossingBothCompoundDeeperGeneral

/-!
# The capstone reused: a genuinely depth-3 tree, closed almost entirely by wiring

Every result so far combined a depth-1 `t1` with a depth-1 `t2`. This file goes one level deeper
on `t1`: `T1 = eml (eml var var) (const c)` — `T1`'s own left child is ITSELF the compound
`eml var var` tree studied since the base case. Combined with `T2 = eml var (const c2')`
(depth-1, as before), the WHOLE tree `eml T1 T2` has depth 3.

**Why this is nearly free.** `T1.eval x = exp(t1'.eval x) - log c` where `t1' := eml var var`.
Its derivative is `T1deriv(x) = exp(t1'.eval x)·t1'deriv(x)` — this is LITERALLY `P(x)` from
`EMLZeroCrossingConvexT1.lean`, the exact function that file's `hasDerivAt_expMulDeriv`/
`expMulDeriv_pos_of_convex` already characterize completely: `T1`'s own convexity (`T1deriv`'s
derivative positive) is EXACTLY `expMulDeriv_pos_of_convex` applied to `t1'`'s already-established
facts (`hasDerivAt_exp_sub_log`, `hasDerivAt_exp_sub_inv`, `exp_sub_inv_deriv_pos`) — no new
positivity argument needed at all. The only genuinely new piece is `T1eval`'s own `HasDerivAt`
fact (`exp(t1'eval x) - log c`'s derivative is `P(x)` via chain rule then subtracting a
constant) — three lines, reusing the SAME `exp∘t1'eval` chain-rule step `hasDerivAt_expMulDeriv`'s
own proof uses internally.

Feeding both into `eml_convexT1_conditionT2_boundedZeros` directly gives the depth-3 bound with
essentially no new mathematical content — the capstone theorem's actual payoff: today's whole
toolkit composes.
-/

namespace MachLib
namespace Real

/-- `T1eval(x) := exp(exp x - log x) - log c`'s derivative is `exp(exp x - log x)·(exp x - 1/x)`
— chain rule around `t1' = eml var var`'s own derivative (`hasDerivAt_exp_sub_log`), then
subtracting the constant `log c` contributes nothing. -/
theorem hasDerivAt_expSubLogSubLogC (c z : Real) (hz : 0 < z) :
    HasDerivAt (fun x => Real.exp (Real.exp x - Real.log x) - Real.log c)
      (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)) z := by
  have ht1' : HasDerivAt (fun x => Real.exp x - Real.log x) (Real.exp z - 1 / z) z :=
    hasDerivAt_exp_sub_log z hz
  have hexp : HasDerivAt (fun x => Real.exp (Real.exp x - Real.log x))
      (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)) z :=
    HasDerivAt_comp Real.exp (fun x => Real.exp x - Real.log x) (Real.exp z - 1 / z)
      (Real.exp (Real.exp z - Real.log z)) z ht1' (HasDerivAt_exp _)
  have hd := HasDerivAt_sub (fun x => Real.exp (Real.exp x - Real.log x)) (fun _ => Real.log c)
    (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)) 0 z hexp (HasDerivAt_const _ z)
  have e : Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) - 0
      = Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) := sub_zero _
  rwa [e] at hd

/-- **The main result**: `eml (eml (eml var var) (const c)) (eml var (const c2'))` — a
GENUINELY depth-3 tree, `t1` itself depth-2 compound — has boundedly many zeros (`≤3`) on any
interval, for ANY `c` (unrestricted, same as `c1'` in every shallower instance) and `c2' > 1`
with `1 ≤ log c2'` (`c2' ≥ e`, the same structural requirement `eml var var` has always needed).
NO `EMLPfaffianValidOn` assumption anywhere. Closed almost entirely by REUSE: `T1`'s convexity is
literally `expMulDeriv_pos_of_convex` applied to already-proven facts, not a new argument. -/
theorem eml_evarvarConstC_evarConstC2_boundedZeros (c c2' : Real) (hc2' : 1 < c2')
    (hx0nonneg : 0 ≤ Real.log (Real.log c2')) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) (EMLTree.const c))
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  rcases lt_total (Real.log (Real.log c2')) b with hb | hb | hb
  · apply eml_convexT1_conditionT2_boundedZeros
      (fun x => Real.exp (Real.exp x - Real.log x) - Real.log c)
      (fun x => Real.exp (Real.exp x - Real.log x) * (Real.exp x - 1 / x))
      (fun x => Real.exp (Real.exp x - Real.log x) * (Real.exp x - 1 / x) * (Real.exp x - 1 / x)
        + Real.exp (Real.exp x - Real.log x) * (Real.exp x - (-1 / (x * x))))
      (fun x => Real.exp x - Real.log c2') Real.exp Real.exp
      (Real.log (Real.log c2')) a b hb
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact hasDerivAt_expSubLogSubLogC c x hxpos
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact hasDerivAt_expMulDeriv (fun w => Real.exp w - Real.log w) (fun w => Real.exp w - 1 / w)
        (fun w => Real.exp w - (-1 / (w * w))) x
        (hasDerivAt_exp_sub_log x hxpos) (hasDerivAt_exp_sub_inv x hxpos)
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact expMulDeriv_pos_of_convex (fun w => Real.exp w - Real.log w)
        (fun w => Real.exp w - 1 / w) (fun w => Real.exp w - (-1 / (w * w))) x
        (exp_sub_inv_deriv_pos x hxpos)
    · intro x hxlt
      have h := (exp_lt_log_c2_iff_lt_switch hc2').1 x hxlt
      have e := sub_lt_sub_right_of_lt (r := Real.log c2') h
      have e2 : Real.log c2' - Real.log c2' = 0 := by mach_ring
      rw [e2] at e
      exact le_of_lt e
    · intro x hxgt
      have h := (exp_lt_log_c2_iff_lt_switch hc2').2 x hxgt
      have e := sub_lt_sub_right_of_lt (r := Real.log c2') h
      have e2 : Real.log c2' - Real.log c2' = 0 := by mach_ring
      rwa [e2] at e
    · intro x _ _
      exact hasDerivAt_evarConstC c2' x
    · intro x _ _
      exact HasDerivAt_exp x
    · intro x _hx0 _hxb
      have hlog_pos : 0 < Real.log c2' := log_pos_of_gt_one hc2'
      have hlt : Real.exp x - Real.log c2' < Real.exp x := by
        have hneg : -Real.log c2' < 0 := neg_neg_of_pos hlog_pos
        have h := add_lt_add_left hneg (Real.exp x)
        have e1 : Real.exp x + -Real.log c2' = Real.exp x - Real.log c2' := by mach_ring
        have e2 : Real.exp x + 0 = Real.exp x := add_zero _
        rwa [e1, e2] at h
      have hmul := mul_lt_mul_of_pos_right hlt (Real.exp_pos x)
      have e3 : (Real.exp x - Real.log c2') * Real.exp x
          = Real.exp x * (Real.exp x - Real.log c2') := by mach_ring
      rwa [e3] at hmul
    · exact hnd
    · intro z hzmem
      obtain ⟨hza, hzb, hfz⟩ := hz z hzmem
      have heq : (EMLTree.eml (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.const c)) (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z
          = Real.exp (Real.exp (Real.exp z - Real.log z) - Real.log c)
            - Real.log (Real.exp z - Real.log c2') := rfl
      rw [heq] at hfz
      exact ⟨hza, hzb, hfz⟩
  · have hempty : zeros = [] := by
      match zeros, hnd, hz with
      | [], _, _ => rfl
      | y :: ys, _, hzf =>
          exfalso
          obtain ⟨_, hyb, hfy⟩ := hzf y (List.mem_cons_self _ _)
          have hylt : y < Real.log (Real.log c2') := by rw [hb]; exact hyb
          have ht2le : Real.exp y - Real.log c2' ≤ 0 := by
            have h := (exp_lt_log_c2_iff_lt_switch hc2').1 y hylt
            have e := sub_lt_sub_right_of_lt (r := Real.log c2') h
            have e2 : Real.log c2' - Real.log c2' = 0 := by mach_ring
            rw [e2] at e
            exact le_of_lt e
          have hcl : Real.log (Real.exp y - Real.log c2') = 0 := Real.log_nonpos ht2le
          have heq : (EMLTree.eml (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
              (EMLTree.const c)) (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval y
              = Real.exp (Real.exp (Real.exp y - Real.log y) - Real.log c)
                - Real.log (Real.exp y - Real.log c2') := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos (Real.exp (Real.exp y - Real.log y) - Real.log c))
    rw [hempty]; simp
  · have hempty : zeros = [] := by
      match zeros, hnd, hz with
      | [], _, _ => rfl
      | y :: ys, _, hzf =>
          exfalso
          obtain ⟨_, hyb, hfy⟩ := hzf y (List.mem_cons_self _ _)
          have hylt : y < Real.log (Real.log c2') := lt_trans_ax hyb hb
          have ht2le : Real.exp y - Real.log c2' ≤ 0 := by
            have h := (exp_lt_log_c2_iff_lt_switch hc2').1 y hylt
            have e := sub_lt_sub_right_of_lt (r := Real.log c2') h
            have e2 : Real.log c2' - Real.log c2' = 0 := by mach_ring
            rw [e2] at e
            exact le_of_lt e
          have hcl : Real.log (Real.exp y - Real.log c2') = 0 := Real.log_nonpos ht2le
          have heq : (EMLTree.eml (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
              (EMLTree.const c)) (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval y
              = Real.exp (Real.exp (Real.exp y - Real.log y) - Real.log c)
                - Real.log (Real.exp y - Real.log c2') := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos (Real.exp (Real.exp y - Real.log y) - Real.log c))
    rw [hempty]; simp

end Real
end MachLib
