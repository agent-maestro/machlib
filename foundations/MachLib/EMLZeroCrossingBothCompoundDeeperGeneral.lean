import MachLib.EMLZeroCrossingConvexT1

/-!
# The `R`-side finding, generalized — and the full both-compound-deeper theorem completed

`EMLZeroCrossingConvexT1.lean` generalized the `P`-side of `EMLZeroCrossingBothCompoundDeeper
.lean`'s finding (convexity alone makes `exp(t1eval)·t1deriv` increasing). This file completes
the other half: what made `R(z) := (1/t2eval z)·t2deriv z` strictly decreasing for the concrete
`t2 = eml var (const c2')` instance, distilled into a condition on ANY `t2`.

**The condition, derived on paper.** Quotient/product rule gives `R'(z) = -t2deriv(z)²/t2eval(z)²
+ t2deriv2(z)/t2eval(z)` (`t2deriv2` is `t2deriv`'s own derivative). On `t2eval(z) > 0`, this is
negative EXACTLY when `t2deriv2(z)·t2eval(z) < t2deriv(z)²`. Checked against the concrete
instance: `t2deriv = t2deriv2 = exp` there, so the condition becomes `exp(z)·(exp z - log c2') <
exp(z)²`, i.e. `-log c2' < 0`, i.e. `c2' > 1` — EXACTLY the sign-crossing hypothesis already
required, recovered for free rather than assumed anew.

**The capstone**: `eml_convexT1_conditionT2_boundedZeros` combines this with the `P`-side result
via `eml_genericT1_genericT2_boundedZeros` (`M := 1` discharged automatically, not supplied by the
caller) — the fully general "both children compound" theorem this whole sub-arc was building
toward: `t1` convex, `t2` sign-crossing with the quadratic-type condition ⟹ `eml T1 t2` has `≤ 3`
zeros, no validity assumption, `t1`/`t2` both abstract. `eml_evarvar_evarConstC2_boundedZeros`
becomes a corollary.
-/

namespace MachLib
namespace Real

/-- `R(x) := (1/t2eval x)·t2deriv x`'s raw derivative, via `HasDerivAt_inv` (reciprocal rule)
then the product rule with `t2deriv`'s own derivative `t2deriv2`. -/
theorem hasDerivAt_invMulDeriv (t2eval t2deriv t2deriv2 : Real → Real) (z : Real)
    (hzne : t2eval z ≠ 0)
    (ht2 : HasDerivAt t2eval (t2deriv z) z) (ht2' : HasDerivAt t2deriv (t2deriv2 z) z) :
    HasDerivAt (fun x => 1 / t2eval x * t2deriv x)
      ((-t2deriv z / (t2eval z * t2eval z)) * t2deriv z + 1 / t2eval z * t2deriv2 z) z := by
  have hinv : HasDerivAt (fun x => 1 / t2eval x) (-t2deriv z / (t2eval z * t2eval z)) z :=
    HasDerivAt_inv t2eval (t2deriv z) z hzne ht2
  exact HasDerivAt_mul (fun x => 1 / t2eval x) t2deriv
    (-t2deriv z / (t2eval z * t2eval z)) (t2deriv2 z) z hinv ht2'

/-- `a < 0 → 0 < b → a·b < 0`. Not reachable transitively from this file's imports (it lives in
`SturmNonOscillation.lean`, an unrelated branch of the codebase), so re-derived locally rather
than pulling in a whole new import for one small fact. -/
theorem mul_neg_of_neg_of_pos {a b : Real} (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  have hnab : 0 < (-a) * b := mul_pos (neg_pos_of_neg ha) hb
  have e : (-a) * b = -(a * b) := neg_mul a b
  rw [e] at hnab
  have h := neg_neg_of_pos hnab
  rwa [neg_neg_helper (a * b)] at h

/-- **`R`'s raw derivative value is strictly negative whenever `t2deriv2 z · t2eval z <
t2deriv z · t2deriv z`** (`t2eval z > 0`) — the general condition recovered from the concrete
instance. Same `generalize`-then-manual-commute pattern as `R_deriv_neg`'s proof, since `mach_ring`
alone does not close the final 2-3 atom reordering once a division has been generalized. -/
theorem invMulDeriv_neg_of_condition (t2eval t2deriv t2deriv2 : Real → Real) (z : Real)
    (hzpos : 0 < t2eval z) (hcond : t2deriv2 z * t2eval z < t2deriv z * t2deriv z) :
    (-t2deriv z / (t2eval z * t2eval z)) * t2deriv z + 1 / t2eval z * t2deriv2 z < 0 := by
  have hzne : t2eval z ≠ 0 := ne_of_gt hzpos
  have hTTpos : 0 < t2eval z * t2eval z := mul_pos hzpos hzpos
  have hTTne : t2eval z * t2eval z ≠ 0 := ne_of_gt hTTpos
  have hkey : t2eval z * (1 / (t2eval z * t2eval z)) = 1 / t2eval z := by
    apply mul_left_cancel hzne
    have e1 : t2eval z * (t2eval z * (1 / (t2eval z * t2eval z)))
        = (t2eval z * t2eval z) * (1 / (t2eval z * t2eval z)) := by mach_ring
    rw [e1, mul_inv _ hTTne, mul_inv _ hzne]
  have estep : (-t2deriv z / (t2eval z * t2eval z)) * t2deriv z + 1 / t2eval z * t2deriv2 z
      = (t2deriv2 z * t2eval z - t2deriv z * t2deriv z) * (1 / (t2eval z * t2eval z)) := by
    rw [div_def (-t2deriv z) _ hTTne, ← hkey]
    generalize (1 : Real) / (t2eval z * t2eval z) = X
    mach_ring
  rw [estep]
  have hnum_neg : t2deriv2 z * t2eval z - t2deriv z * t2deriv z < 0 := by
    have h := add_lt_add_left hcond (-(t2deriv z * t2deriv z))
    have e1 : -(t2deriv z * t2deriv z) + t2deriv2 z * t2eval z
        = t2deriv2 z * t2eval z - t2deriv z * t2deriv z := by mach_ring
    have e2 : -(t2deriv z * t2deriv z) + t2deriv z * t2deriv z = 0 := by mach_ring
    rwa [e1, e2] at h
  have hXpos : 0 < 1 / (t2eval z * t2eval z) := one_div_pos_of_pos hTTpos
  exact mul_neg_of_neg_of_pos hnum_neg hXpos

/-- `D(x) := exp(t1eval x)·t1deriv x - (1/t2eval x)·t2deriv x`'s raw derivative, combining the
`P`- and `R`-side facts via the subtraction rule — the fully general version of
`hasDerivAt_D`. -/
theorem hasDerivAt_D_general (t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 : Real → Real)
    (z : Real) (ht1 : HasDerivAt t1eval (t1deriv z) z)
    (ht1' : HasDerivAt t1deriv (t1deriv2 z) z) (hzne : t2eval z ≠ 0)
    (ht2 : HasDerivAt t2eval (t2deriv z) z) (ht2' : HasDerivAt t2deriv (t2deriv2 z) z) :
    HasDerivAt
      (fun x => Real.exp (t1eval x) * t1deriv x - 1 / t2eval x * t2deriv x)
      ((Real.exp (t1eval z) * t1deriv z * t1deriv z + Real.exp (t1eval z) * t1deriv2 z)
        - ((-t2deriv z / (t2eval z * t2eval z)) * t2deriv z + 1 / t2eval z * t2deriv2 z)) z :=
  HasDerivAt_sub _ _ _ _ z (hasDerivAt_expMulDeriv t1eval t1deriv t1deriv2 z ht1 ht1')
    (hasDerivAt_invMulDeriv t2eval t2deriv t2deriv2 z hzne ht2 ht2')

/-- `D`'s raw derivative is strictly positive: `P`'s positive derivative (from convexity) minus
`R`'s negative derivative (from the quadratic-type condition). -/
theorem D_deriv_pos_general (t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 : Real → Real)
    (z : Real) (hconvex : 0 < t1deriv2 z) (hzpos : 0 < t2eval z)
    (hcond : t2deriv2 z * t2eval z < t2deriv z * t2deriv z) :
    0 < (Real.exp (t1eval z) * t1deriv z * t1deriv z + Real.exp (t1eval z) * t1deriv2 z)
        - ((-t2deriv z / (t2eval z * t2eval z)) * t2deriv z + 1 / t2eval z * t2deriv2 z) :=
  sub_pos_of_pos_of_neg (expMulDeriv_pos_of_convex t1eval t1deriv t1deriv2 z hconvex)
    (invMulDeriv_neg_of_condition t2eval t2deriv t2deriv2 z hzpos hcond)

/-- **`D` has at most one zero on `(x0, b)`**, given `t1` convex and `t2` satisfying the
quadratic-type condition throughout — strict monotonicity from `D_deriv_pos_general`, the fully
general version of `D_atMostOneZero`. -/
theorem D_atMostOneZero_general
    (t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 : Real → Real) (x0 b : Real)
    (ht1 : ∀ x : Real, x0 < x → x < b → HasDerivAt t1eval (t1deriv x) x)
    (ht1' : ∀ x : Real, x0 < x → x < b → HasDerivAt t1deriv (t1deriv2 x) x)
    (hconvex : ∀ x : Real, x0 < x → x < b → 0 < t1deriv2 x)
    (hgt_side : ∀ x : Real, x0 < x → 0 < t2eval x)
    (ht2 : ∀ x : Real, x0 < x → x < b → HasDerivAt t2eval (t2deriv x) x)
    (ht2' : ∀ x : Real, x0 < x → x < b → HasDerivAt t2deriv (t2deriv2 x) x)
    (hcond : ∀ x : Real, x0 < x → x < b → t2deriv2 x * t2eval x < t2deriv x * t2deriv x) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, x0 < z ∧ z < b ∧
        Real.exp (t1eval z) * t1deriv z - 1 / t2eval z * t2deriv z = 0) →
      zeros.length ≤ 1 := by
  apply atMostOneZero_of_strictMono
  intro x y hxc hxd hyc hyd hxy
  apply strictMono_of_deriv_pos
    (fun w => Real.exp (t1eval w) * t1deriv w - 1 / t2eval w * t2deriv w) x y hxy
  · intro w hxw hwy
    have hwc : x0 < w := lt_of_lt_of_le hxc hxw
    have hwd : w < b := lt_of_le_of_lt hwy hyd
    have hwzpos : 0 < t2eval w := hgt_side w hwc
    exact ⟨_, hasDerivAt_D_general t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 w
      (ht1 w hwc hwd) (ht1' w hwc hwd) (ne_of_gt hwzpos) (ht2 w hwc hwd) (ht2' w hwc hwd)⟩
  · intro w f' hxw hwy hderiv
    have hwc : x0 < w := lt_of_lt_of_le hxc hxw
    have hwd : w < b := lt_of_le_of_lt hwy hyd
    have hwzpos : 0 < t2eval w := hgt_side w hwc
    rw [HasDerivAt_unique _ _ _ w hderiv
      (hasDerivAt_D_general t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 w
        (ht1 w hwc hwd) (ht1' w hwc hwd) (ne_of_gt hwzpos) (ht2 w hwc hwd) (ht2' w hwc hwd))]
    exact D_deriv_pos_general t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 w
      (hconvex w hwc hwd) hwzpos (hcond w hwc hwd)

/-- **The capstone: the fully general "both children compound" theorem.** `t1` convex (known
eval/derivative/second-derivative, positive second derivative), `t2` with a sign crossing at `x0`
and the quadratic-type condition throughout `(x0,b)` — `eml T1 t2` has at most `3` zeros on any
interval, `M := 1` discharged automatically via `D_atMostOneZero_general` rather than supplied by
the caller (unlike `eml_genericT1_genericT2_boundedZeros`, which leaves `M` abstract). No
`EMLPfaffianValidOn` assumption anywhere. -/
theorem eml_convexT1_conditionT2_boundedZeros
    (t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 : Real → Real) (x0 a b : Real) (hx0b : x0 < b)
    (ht1 : ∀ x : Real, x0 < x → x < b → HasDerivAt t1eval (t1deriv x) x)
    (ht1' : ∀ x : Real, x0 < x → x < b → HasDerivAt t1deriv (t1deriv2 x) x)
    (hconvex : ∀ x : Real, x0 < x → x < b → 0 < t1deriv2 x)
    (hlt_side : ∀ x : Real, x < x0 → t2eval x ≤ 0)
    (hgt_side : ∀ x : Real, x0 < x → 0 < t2eval x)
    (ht2 : ∀ x : Real, x0 < x → x < b → HasDerivAt t2eval (t2deriv x) x)
    (ht2' : ∀ x : Real, x0 < x → x < b → HasDerivAt t2deriv (t2deriv2 x) x)
    (hcond : ∀ x : Real, x0 < x → x < b → t2deriv2 x * t2eval x < t2deriv x * t2deriv x) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Real.exp (t1eval z) - Real.log (t2eval z) = 0) →
      zeros.length ≤ 3 := by
  have h := eml_genericT1_genericT2_boundedZeros t1eval t1deriv t2eval t2deriv x0 a b hx0b
    ht1 hlt_side hgt_side ht2 1
    (D_atMostOneZero_general t1eval t1deriv t1deriv2 t2eval t2deriv t2deriv2 x0 b
      ht1 ht1' hconvex hgt_side ht2 ht2' hcond)
  intro zeros hnd hz
  exact h zeros hnd hz

/-- **Sanity check**: `eml_evarvar_evarConstC2_boundedZeros` re-derived as a corollary,
instantiating `t1deriv2 = fun x => exp x - (-1/(x*x))` (convexity from `exp_sub_inv_deriv_pos`)
and `t2deriv2 = Real.exp` (`t2deriv = Real.exp` is its own derivative, `hasDerivAt_evarConstC`
applied to `t2deriv` itself), with the quadratic condition reducing exactly to `c2' > 1` — the
same reduction worked out by hand in `EMLZeroCrossingBothCompoundDeeper.lean`. -/
theorem eml_evarvar_evarConstC2_boundedZeros_via_general (c2' : Real) (hc2' : 1 < c2')
    (hx0nonneg : 0 ≤ Real.log (Real.log c2')) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  rcases lt_total (Real.log (Real.log c2')) b with hb | hb | hb
  · apply eml_convexT1_conditionT2_boundedZeros
      (fun x => Real.exp x - Real.log x) (fun x => Real.exp x - 1 / x)
      (fun x => Real.exp x - (-1 / (x * x)))
      (fun x => Real.exp x - Real.log c2') Real.exp Real.exp
      (Real.log (Real.log c2')) a b hb
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact hasDerivAt_exp_sub_log x hxpos
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact hasDerivAt_exp_sub_inv x hxpos
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact exp_sub_inv_deriv_pos x hxpos
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
      have heq : (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z
          = Real.exp (Real.exp z - Real.log z) - Real.log (Real.exp z - Real.log c2') := rfl
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
          have heq : (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
              (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval y
              = Real.exp (Real.exp y - Real.log y) - Real.log (Real.exp y - Real.log c2') := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos (Real.exp y - Real.log y))
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
          have heq : (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
              (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval y
              = Real.exp (Real.exp y - Real.log y) - Real.log (Real.exp y - Real.log c2') := rfl
          rw [heq, hcl, sub_zero] at hfy
          exact lt_irrefl_ax 0 (hfy ▸ Real.exp_pos (Real.exp y - Real.log y))
    rw [hempty]; simp

end Real
end MachLib
