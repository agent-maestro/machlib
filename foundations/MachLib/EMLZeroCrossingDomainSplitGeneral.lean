import MachLib.EMLZeroCrossingDomainSplit

/-!
# The domain-splitting pattern, generalized: any `t2` with one known sign crossing

Continuation of path (1). `EMLZeroCrossingDomainSplit.lean` closed ONE concrete instance
(`t2 = eml var (const c2)`) of the domain-splitting problem. This file distills what actually
made that instance work into a reusable theorem, parametrized by `t2`'s own evaluation,
derivative, and a bound on ITS derivative's zero count — rather than being hardcoded to one
specific `t2` shape.

**What generalizes cleanly.** For `t = eml (const c1) t2`, on the region where `t2 > 0`, `t`'s
derivative is `-t2'(x)/t2.eval(x)` — this is `0` EXACTLY when `t2'(x) = 0` (the `1/t2.eval(x)`
factor is never zero there). So bounding `t`'s zero count on that region reduces DIRECTLY to
bounding `t2`'s OWN derivative's zero count — exactly the "reuse a smaller/simpler fact" pattern
from `EMLZeroCrossingDepth2Compound.lean`, now applied to the domain-splitting case instead of
the compound-`t1` case. The `eml var (const c2)` instance is the special case where `t2' = exp`,
whose zero count is `0` trivially (`exp` is never `0`) — the general theorem takes that bound as
a parameter instead of assuming it.

**The result**: given `t2`'s sign either side of a switch point `x0`, its derivative on the
positive side, and a bound `K` on that derivative's OWN zero count, `eml (const c1) t2` has at
most `K+2` zeros on any interval — the `+2` covers the switch point itself and the (zero-count,
always-clamped) region before it. `T1_not_eq_log_c2_plus_sin_given_validon`-style specific
results become one-line corollaries of this once `t2`'s own facts are supplied.
-/

namespace MachLib
namespace Real

/-- **The domain-splitting pattern, general.** `t = eml (const c1) t2`'s zero count reduces to
`t2`'s own derivative's zero count (`K`), plus `2` for the switch point and the always-zero-free
region before it. -/
theorem eml_const_genericT2_boundedZeros
    (c1 : Real) (t2eval t2deriv : Real → Real) (x0 a b : Real) (hx0b : x0 < b)
    (hlt_side : ∀ x : Real, x < x0 → t2eval x ≤ 0)
    (hgt_side : ∀ x : Real, x0 < x → 0 < t2eval x)
    (hderiv : ∀ x : Real, x0 < x → x < b → HasDerivAt t2eval (t2deriv x) x)
    (K : Nat)
    (hderivBound : ∀ zeros_d : List Real, zeros_d.Nodup →
        (∀ z ∈ zeros_d, x0 < z ∧ z < b ∧ t2deriv z = 0) → zeros_d.length ≤ K) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Real.exp c1 - Real.log (t2eval z) = 0) →
      zeros.length ≤ K + 2 := by
  intro zeros hnd hz
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  have hlt_bound : (zeros.filter (fun z => decide (z < x0))).length ≤ 0 := by
    have hempty : zeros.filter (fun z => decide (z < x0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hzmem hzlt
      have hzlt' : z < x0 := of_decide_eq_true hzlt
      obtain ⟨_, _, hfz⟩ := hz z hzmem
      have hcl : Real.log (t2eval z) = 0 := Real.log_nonpos (hlt_side z hzlt')
      rw [hcl, sub_zero] at hfz
      exact lt_irrefl_ax 0 (hfz ▸ Real.exp_pos c1)
    rw [hempty]; simp
  have hnd_ge : (zeros.filter (fun z => !decide (z < x0))).Nodup := hnd.filter _
  have heq_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => decide (z = x0))).length ≤ 1 := by
    apply EMLExplicitBound.length_le_one_of_forall_eq _ (hnd_ge.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    exact of_decide_eq_true hzmem.2
  have hgt_general : ∀ zeros_f' : List Real, zeros_f'.Nodup →
      (∀ z ∈ zeros_f', x0 < z ∧ z < b ∧ Real.exp c1 - Real.log (t2eval z) = 0) →
      zeros_f'.length ≤ K + 1 :=
    zero_count_bound_by_deriv (fun y => Real.exp c1 - Real.log (t2eval y)) x0 b hx0b
      (fun z hz0 hzb => by
        have hzpos : 0 < t2eval z := hgt_side z hz0
        have hlog : HasDerivAt (fun y => Real.log (t2eval y))
            (1 / t2eval z * t2deriv z) z :=
          HasDerivAt_comp Real.log t2eval (t2deriv z) (1 / t2eval z) z
            (hderiv z hz0 hzb) (HasDerivAt_log_pos _ hzpos)
        exact ⟨_, HasDerivAt_sub (fun _ => Real.exp c1) (fun y => Real.log (t2eval y)) 0 _ z
          (HasDerivAt_const (Real.exp c1) z) hlog⟩)
      K
      (fun zeros_f' hnd' hzf' => by
        apply hderivBound zeros_f' hnd'
        intro z hzmem
        obtain ⟨hz0, hzb, f'', hderiv', hf''0⟩ := hzf' z hzmem
        have hzpos : 0 < t2eval z := hgt_side z hz0
        have hlog : HasDerivAt (fun y => Real.log (t2eval y))
            (1 / t2eval z * t2deriv z) z :=
          HasDerivAt_comp Real.log t2eval (t2deriv z) (1 / t2eval z) z
            (hderiv z hz0 hzb) (HasDerivAt_log_pos _ hzpos)
        have hderiv_eq : HasDerivAt (fun y => Real.exp c1 - Real.log (t2eval y))
            (0 - 1 / t2eval z * t2deriv z) z :=
          HasDerivAt_sub (fun _ => Real.exp c1) (fun y => Real.log (t2eval y)) 0 _ z
            (HasDerivAt_const (Real.exp c1) z) hlog
        rw [HasDerivAt_unique _ _ _ z hderiv' hderiv_eq] at hf''0
        have hrecip_pos : 0 < 1 / t2eval z := div_pos_of_pos_pos zero_lt_one_ax hzpos
        have hrecip_ne : (1 : Real) / t2eval z ≠ 0 := ne_of_gt hrecip_pos
        have hf''0' : (1 : Real) / t2eval z * t2deriv z = 0 := by
          generalize hXdef : (1 : Real) / t2eval z * t2deriv z = X at hf''0 ⊢
          have e : X = 0 - (0 - X) := by mach_ring
          rw [hf''0] at e
          have e2 : (0 : Real) - 0 = 0 := by mach_ring
          rwa [e2] at e
        exact ⟨hz0, hzb, PfaffianChainMod.mul_eq_zero_of_factor_ne_zero hrecip_ne hf''0'⟩)
  have hgt_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => !decide (z = x0))).length ≤ K + 1 := by
    apply hgt_general _ (hnd_ge.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    obtain ⟨hzmem', hzge⟩ := hzmem
    rw [List.mem_filter] at hzmem'
    obtain ⟨hzz, hzge'⟩ := hzmem'
    obtain ⟨_, hzb, hfz⟩ := hz z hzz
    have hzge0 : ¬ z < x0 := of_decide_eq_false (by simpa using hzge')
    have hzne0 : z ≠ x0 := of_decide_eq_false (by simpa using hzge)
    have hzgt0 : x0 < z := by
      rcases lt_total x0 z with h | h | h
      · exact h
      · exact absurd h.symm hzne0
      · exact absurd h hzge0
    exact ⟨hzgt0, hzb, hfz⟩
  have hpart1 : (zeros.filter (fun z => decide (z < x0))).length
      + (zeros.filter (fun z => !decide (z < x0))).length = zeros.length :=
    MultiVarMod.length_filter_partition (fun z => decide (z < x0)) zeros
  have hpart2 : ((zeros.filter (fun z => !decide (z < x0))).filter
        (fun z => decide (z = x0))).length
      + ((zeros.filter (fun z => !decide (z < x0))).filter (fun z => !decide (z = x0))).length
      = (zeros.filter (fun z => !decide (z < x0))).length :=
    MultiVarMod.length_filter_partition (fun z => decide (z = x0))
      (zeros.filter (fun z => !decide (z < x0)))
  omega

/-- **Sanity check**: `eml_const_evarConstC2_boundedZeros` (`EMLZeroCrossingDomainSplit.lean`,
the ONE concrete instance) re-derived as a corollary of the general theorem, confirming the
generalization is equivalent to — not just similar to — the original hand-built result.
`t2eval = fun x => exp x - log c2`, `t2deriv = Real.exp` (never `0`, so `K=0` and the derivative
bound is immediate), `x0 = log(log c2)`. -/
theorem eml_const_evarConstC2_boundedZeros_via_general (c1 c2 : Real) (hc2 : 1 < c2) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.const c1)
          (EMLTree.eml EMLTree.var (EMLTree.const c2))).eval z = 0) →
      zeros.length ≤ 4 := by
  intro zeros hnd hz
  have hlc2pos : 0 < Real.log c2 := log_pos_of_gt_one hc2
  rcases lt_total (Real.log (Real.log c2)) b with hb | hb | hb
  · apply eml_const_genericT2_boundedZeros c1 (fun x => Real.exp x - Real.log c2) Real.exp
      (Real.log (Real.log c2)) a b hb
    · intro x hxlt
      have h := (exp_lt_log_c2_iff_lt_switch hc2).1 x hxlt
      have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
      have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
      rw [e2] at e
      exact le_of_lt e
    · intro x hxgt
      have h := (exp_lt_log_c2_iff_lt_switch hc2).2 x hxgt
      have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
      have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
      rwa [e2] at e
    · intro x _ _
      have hd := HasDerivAt_sub Real.exp (fun _ => Real.log c2) (Real.exp x) 0 x
        (HasDerivAt_exp x) (HasDerivAt_const (Real.log c2) x)
      have e : Real.exp x - 0 = Real.exp x := sub_zero _
      rwa [e] at hd
    · intro zeros_d hnd' hzd
      match zeros_d, hzd with
      | [], _ => simp
      | w :: ws, hzd' => exact absurd (hzd' w (List.mem_cons_self _ _)).2.2 (ne_of_gt (Real.exp_pos w))
    · exact hnd
    · intro z hzmem
      obtain ⟨hza, hzb, hfz⟩ := hz z hzmem
      have heq : (EMLTree.eml (EMLTree.const c1)
          (EMLTree.eml EMLTree.var (EMLTree.const c2))).eval z
          = Real.exp c1 - Real.log (Real.exp z - Real.log c2) := rfl
      rw [heq] at hfz
      exact ⟨hza, hzb, hfz⟩
  · have hempty : zeros = [] := by
      match zeros, hnd, hz with
      | [], _, _ => rfl
      | y :: ys, _, hzf =>
          exfalso
          obtain ⟨_, hyb, hfy⟩ := hzf y (List.mem_cons_self _ _)
          have hylt : y < Real.log (Real.log c2) := by rw [hb]; exact hyb
          have ht2le : Real.exp y - Real.log c2 ≤ 0 := by
            have h := (exp_lt_log_c2_iff_lt_switch hc2).1 y hylt
            have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
            have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
            rw [e2] at e
            exact le_of_lt e
          have hcl : Real.log (Real.exp y - Real.log c2) = 0 := Real.log_nonpos ht2le
          have heq : (EMLTree.eml (EMLTree.const c1)
              (EMLTree.eml EMLTree.var (EMLTree.const c2))).eval y
              = Real.exp c1 - Real.log (Real.exp y - Real.log c2) := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos c1)
    rw [hempty]; simp
  · have hempty : zeros = [] := by
      match zeros, hnd, hz with
      | [], _, _ => rfl
      | y :: ys, _, hzf =>
          exfalso
          obtain ⟨_, hyb, hfy⟩ := hzf y (List.mem_cons_self _ _)
          have hylt : y < Real.log (Real.log c2) := lt_trans_ax hyb hb
          have ht2le : Real.exp y - Real.log c2 ≤ 0 := by
            have h := (exp_lt_log_c2_iff_lt_switch hc2).1 y hylt
            have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
            have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
            rw [e2] at e
            exact le_of_lt e
          have hcl : Real.log (Real.exp y - Real.log c2) = 0 := Real.log_nonpos ht2le
          have heq : (EMLTree.eml (EMLTree.const c1)
              (EMLTree.eml EMLTree.var (EMLTree.const c2))).eval y
              = Real.exp c1 - Real.log (Real.exp y - Real.log c2) := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos c1)
    rw [hempty]; simp

end Real
end MachLib
