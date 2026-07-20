import MachLib.EMLZeroCrossingBothCompound

/-!
# The both-compound pattern, generalized: any `t1` (with a known global derivative) + any
`t2` with a known sign crossing

`EMLZeroCrossingBothCompound.lean` closed ONE concrete instance (`t1 = eml var (const c1')`,
`t2 = eml var (const c2')`) of the "both children compound" problem. This file distills what
actually made that instance work into a reusable theorem, mirroring exactly how
`EMLZeroCrossingDomainSplitGeneral.lean` generalized the earlier const-`t1` domain-split result:
parametrize by `t1`'s own eval/derivative (assumed known everywhere — matching every instance
built so far, where `t1` is only ever exponentiated, never itself the argument of a `log`, so no
domain restriction on `t1eval` is needed) and `t2`'s eval/derivative/sign-crossing structure
exactly as before, PLUS a caller-supplied bound `M` on the zeros of the COMBINED raw derivative
expression `exp(t1eval z)·t1deriv z - (1/t2eval z)·t2deriv z` — the one piece that's genuinely
new to this combination and can't be reduced further in general (unlike the const-`t1` case,
where the `t1`-derivative term vanished entirely, leaving a bound on `t2deriv` alone sufficient).

**What stays the same**: the `0` (clamped region) `+ 1` (switch point) accounting is IDENTICAL to
every prior domain-split theorem — `t1` being compound never touched the left region even in the
concrete instance, and that argument was already fully general (`Real.exp_pos` needs nothing about
`t1eval`'s value). Only the right region's bound (`M` instead of a reduction to `t2deriv`'s zeros)
is new.

**Sanity check**: `eml_evarConstC1_evarConstC2_boundedZeros` re-derived as a corollary, supplying
`M := 1` via exactly the `g`/`cross_cancel_bridge` machinery already built.
-/

namespace MachLib
namespace Real

/-- **The both-compound pattern, general.** `t = eml T1 t2`'s zero count reduces to a
caller-supplied bound `M` on the combined derivative `exp(t1eval z)·t1deriv z - (1/t2eval
z)·t2deriv z`'s own zero count, plus `2` for the switch point and the always-zero-free clamped
region before it — same `+2` accounting as the const-`t1` general theorem, `t1`'s compoundness
only ever affecting the right-region bound. -/
theorem eml_genericT1_genericT2_boundedZeros
    (t1eval t1deriv t2eval t2deriv : Real → Real) (x0 a b : Real) (hx0b : x0 < b)
    (ht1deriv : ∀ x : Real, HasDerivAt t1eval (t1deriv x) x)
    (hlt_side : ∀ x : Real, x < x0 → t2eval x ≤ 0)
    (hgt_side : ∀ x : Real, x0 < x → 0 < t2eval x)
    (ht2deriv : ∀ x : Real, x0 < x → x < b → HasDerivAt t2eval (t2deriv x) x)
    (M : Nat)
    (hMbound : ∀ zeros_d : List Real, zeros_d.Nodup →
        (∀ z ∈ zeros_d, x0 < z ∧ z < b ∧
          Real.exp (t1eval z) * t1deriv z - 1 / t2eval z * t2deriv z = 0) →
        zeros_d.length ≤ M) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Real.exp (t1eval z) - Real.log (t2eval z) = 0) →
      zeros.length ≤ M + 2 := by
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
      exact lt_irrefl_ax 0 (hfz ▸ Real.exp_pos (t1eval z))
    rw [hempty]; simp
  have hnd_ge : (zeros.filter (fun z => !decide (z < x0))).Nodup := hnd.filter _
  have heq_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => decide (z = x0))).length ≤ 1 := by
    apply EMLExplicitBound.length_le_one_of_forall_eq _ (hnd_ge.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    exact of_decide_eq_true hzmem.2
  have hgt_general : ∀ zeros_f' : List Real, zeros_f'.Nodup →
      (∀ z ∈ zeros_f', x0 < z ∧ z < b ∧ Real.exp (t1eval z) - Real.log (t2eval z) = 0) →
      zeros_f'.length ≤ M + 1 :=
    zero_count_bound_by_deriv (fun y => Real.exp (t1eval y) - Real.log (t2eval y)) x0 b hx0b
      (fun z hz0 hzb => by
        have hzpos : 0 < t2eval z := hgt_side z hz0
        have hlog : HasDerivAt (fun y => Real.log (t2eval y))
            (1 / t2eval z * t2deriv z) z :=
          HasDerivAt_comp Real.log t2eval (t2deriv z) (1 / t2eval z) z
            (ht2deriv z hz0 hzb) (HasDerivAt_log_pos _ hzpos)
        have hexp : HasDerivAt (fun y => Real.exp (t1eval y))
            (Real.exp (t1eval z) * t1deriv z) z :=
          HasDerivAt_comp Real.exp t1eval (t1deriv z) (Real.exp (t1eval z)) z
            (ht1deriv z) (HasDerivAt_exp _)
        exact ⟨_, HasDerivAt_sub (fun y => Real.exp (t1eval y)) (fun y => Real.log (t2eval y))
          (Real.exp (t1eval z) * t1deriv z) (1 / t2eval z * t2deriv z) z hexp hlog⟩)
      M
      (fun zeros_f' hnd' hzf' => by
        apply hMbound zeros_f' hnd'
        intro z hzmem
        obtain ⟨hz0, hzb, f'', hderiv', hf''0⟩ := hzf' z hzmem
        have hzpos : 0 < t2eval z := hgt_side z hz0
        have hlog : HasDerivAt (fun y => Real.log (t2eval y))
            (1 / t2eval z * t2deriv z) z :=
          HasDerivAt_comp Real.log t2eval (t2deriv z) (1 / t2eval z) z
            (ht2deriv z hz0 hzb) (HasDerivAt_log_pos _ hzpos)
        have hexp : HasDerivAt (fun y => Real.exp (t1eval y))
            (Real.exp (t1eval z) * t1deriv z) z :=
          HasDerivAt_comp Real.exp t1eval (t1deriv z) (Real.exp (t1eval z)) z
            (ht1deriv z) (HasDerivAt_exp _)
        have hderiv_eq : HasDerivAt (fun y => Real.exp (t1eval y) - Real.log (t2eval y))
            (Real.exp (t1eval z) * t1deriv z - 1 / t2eval z * t2deriv z) z :=
          HasDerivAt_sub (fun y => Real.exp (t1eval y)) (fun y => Real.log (t2eval y))
            (Real.exp (t1eval z) * t1deriv z) (1 / t2eval z * t2deriv z) z hexp hlog
        rw [HasDerivAt_unique _ _ _ z hderiv' hderiv_eq] at hf''0
        exact ⟨hz0, hzb, hf''0⟩)
  have hgt_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => !decide (z = x0))).length ≤ M + 1 := by
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

/-- **Sanity check**: `eml_evarConstC1_evarConstC2_boundedZeros` re-derived as a corollary,
confirming the generalization is equivalent to — not just similar to — the original hand-built
result. `M := 1` via `g_atMostOneZero_right` + `cross_cancel_bridge`, exactly the machinery
already built for the concrete instance. -/
theorem eml_evarConstC1_evarConstC2_boundedZeros_via_general (c1' c2' : Real) (hc2' : 1 < c2')
    (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1'))
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  have hlc2pos : 0 < Real.log c2' := log_pos_of_gt_one hc2'
  rcases lt_total (Real.log (Real.log c2')) b with hb | hb | hb
  · apply eml_genericT1_genericT2_boundedZeros
      (fun x => Real.exp x - Real.log c1') Real.exp
      (fun x => Real.exp x - Real.log c2') Real.exp
      (Real.log (Real.log c2')) a b hb
    · intro x
      exact hasDerivAt_evarConstC c1' x
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
    · intro zeros_d hnd' hzd
      apply g_atMostOneZero_right c1' c2' hc2' b
      · exact hnd'
      · intro z hzmem
        obtain ⟨hz0, hzb, hDz⟩ := hzd z hzmem
        have hzpos : 0 < Real.exp z - Real.log c2' :=
          t2eval_pos_of_gt_x0 ((exp_lt_log_c2_iff_lt_switch hc2').2 z hz0)
        have hgz := cross_cancel_bridge (ne_of_gt (Real.exp_pos z)) (ne_of_gt hzpos) hDz
        exact ⟨hz0, hzb, hgz⟩
    · exact hnd
    · intro z hzmem
      obtain ⟨hza, hzb, hfz⟩ := hz z hzmem
      have heq : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1'))
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z
          = Real.exp (Real.exp z - Real.log c1') - Real.log (Real.exp z - Real.log c2') := rfl
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
          have heq : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1'))
              (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval y
              = Real.exp (Real.exp y - Real.log c1') - Real.log (Real.exp y - Real.log c2') := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos (Real.exp y - Real.log c1'))
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
          have heq : (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1'))
              (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval y
              = Real.exp (Real.exp y - Real.log c1') - Real.log (Real.exp y - Real.log c2') := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos (Real.exp y - Real.log c1'))
    rw [hempty]; simp

end Real
end MachLib
