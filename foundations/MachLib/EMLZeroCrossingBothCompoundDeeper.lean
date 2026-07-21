import MachLib.EMLZeroCrossingBothCompoundGeneral

/-!
# `eml var var` combined with `eml var (const c2')`: the first genuinely deeper `t1`

The prior file's `ht1deriv`-localization removed a STRUCTURAL obstacle to using `t1 = eml var var`
in `eml_genericT1_genericT2_boundedZeros`, but didn't yet combine it with a compound `t2` — the
combined derivative `D(z) = exp(t1eval z)·t1deriv z - (1/t2eval z)·t2deriv z` becomes genuinely
new once `t1deriv` is no longer the constant-sign `exp` seen in every instance so far (`t1deriv z
= exp z - 1/z` for `t1 = eml var var`, itself only zero ONCE, at the transcendental "Omega
constant"). This file closes that combination.

**The key finding, on paper first.** Split `D = P - R` where `P(z) := exp(t1eval z)·t1deriv z`
and `R(z) := (1/t2eval z)·t2deriv z`. Both turn out to be MONOTONIC, in opposite directions, which
alone forces `D` monotonic — no case-split on `t1deriv`'s own sign change is needed at all:

- `P'(z) = exp(t1eval z)·[(t1deriv z)² + (exp z + 1/z²)]` (product + chain rule; the bracket's
  second summand is `t1deriv`'s OWN derivative, already established positive as
  `exp_sub_inv_deriv_pos` in `EMLZeroCrossingDepth1.lean`). The bracket is a SQUARE plus an
  ALREADY-KNOWN-POSITIVE term — positive regardless of `t1deriv z`'s sign. So `P` is strictly
  increasing on `z > 0`, full stop.
- `R'(z) = -log(c2')·exp(z) / (exp z - log c2')²` (quotient rule, `t2eval = exp - log c2'`,
  `t2deriv = exp`). Since `c2' > 1` gives `log c2' > 0`, and the rest of the expression is
  manifestly positive, `R'(z) < 0` on `z > x0` — `R` is strictly decreasing.

`D = P - R`, a sum of two strictly increasing functions (`P` and `-R`), hence strictly increasing
itself — injective, hence at most ONE zero. `M := 1` suffices, EXACTLY the same bound the simpler
`eml var (const c1')` instance needed, despite `t1deriv` no longer being sign-constant.

**The one genuinely new side condition.** `t1eval = exp x - log x` is not differentiable at `x =
0` (established two entries ago). Since `t1deriv` is only required on `(x0, b)`, this is fine as
long as `x0 ≥ 0` — i.e. `1 ≤ log c2'` (`c2' ≥ e`), the SAME numeric threshold that appeared (for a
different reason) in an early draft of the concrete both-compound instance, now needed for a
genuinely structural reason rather than a proof-simplification convenience.
-/

namespace MachLib
namespace Real

/-- `P(z) := exp(t1eval z)·t1deriv z`'s raw derivative, via chain rule (for `exp∘t1eval`) then
product rule (with `t1deriv`'s own derivative, `hasDerivAt_exp_sub_inv`) — reusing both
`EMLZeroCrossingDepth1.lean` facts directly, the actual "induction" mechanism at work. -/
theorem hasDerivAt_P (z : Real) (hz : 0 < z) :
    HasDerivAt (fun x => Real.exp (Real.exp x - Real.log x) * (Real.exp x - 1 / x))
      (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
        + Real.exp (Real.exp z - Real.log z) * (Real.exp z - (-1 / (z * z)))) z := by
  have ht1 : HasDerivAt (fun x => Real.exp x - Real.log x) (Real.exp z - 1 / z) z :=
    hasDerivAt_exp_sub_log z hz
  have hexp_t1 : HasDerivAt (fun x => Real.exp (Real.exp x - Real.log x))
      (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)) z :=
    HasDerivAt_comp Real.exp (fun x => Real.exp x - Real.log x) (Real.exp z - 1 / z)
      (Real.exp (Real.exp z - Real.log z)) z ht1 (HasDerivAt_exp _)
  have ht1deriv' : HasDerivAt (fun x => Real.exp x - 1 / x) (Real.exp z - (-1 / (z * z))) z :=
    hasDerivAt_exp_sub_inv z hz
  exact HasDerivAt_mul (fun x => Real.exp (Real.exp x - Real.log x)) (fun x => Real.exp x - 1 / x)
    (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)) (Real.exp z - (-1 / (z * z))) z
    hexp_t1 ht1deriv'

/-- `P`'s raw derivative value is strictly positive throughout `z > 0`: it factors as
`exp(t1eval z) · [(t1deriv z)² + (exp z + 1/z²)]`, a sum of a SQUARE (`mul_self_nonneg`) and the
already-established-positive `exp_sub_inv_deriv_pos` — positive regardless of `t1deriv z`'s own
sign, no case-split on `t1deriv`'s zero needed. -/
theorem P_deriv_pos (z : Real) (hz : 0 < z) :
    0 < Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
        + Real.exp (Real.exp z - Real.log z) * (Real.exp z - (-1 / (z * z))) := by
  have hexp_pos : 0 < Real.exp (Real.exp z - Real.log z) := Real.exp_pos _
  have hsq : 0 ≤ (Real.exp z - 1 / z) * (Real.exp z - 1 / z) := mul_self_nonneg _
  have hd2pos : 0 < Real.exp z - (-1 / (z * z)) := exp_sub_inv_deriv_pos z hz
  have hbracket : 0 < (Real.exp z - 1 / z) * (Real.exp z - 1 / z) + (Real.exp z - (-1 / (z * z))) := by
    have hle : Real.exp z - (-1 / (z * z))
        ≤ (Real.exp z - 1 / z) * (Real.exp z - 1 / z) + (Real.exp z - (-1 / (z * z))) := by
      have h := add_le_add_left hsq (Real.exp z - (-1 / (z * z)))
      have e1 : Real.exp z - (-1 / (z * z)) + 0 = Real.exp z - (-1 / (z * z)) := add_zero _
      have e2 : Real.exp z - (-1 / (z * z)) + (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
          = (Real.exp z - 1 / z) * (Real.exp z - 1 / z) + (Real.exp z - (-1 / (z * z))) := by
        mach_ring
      rw [e1, e2] at h
      exact h
    exact lt_of_lt_of_le hd2pos hle
  have e : Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
        + Real.exp (Real.exp z - Real.log z) * (Real.exp z - (-1 / (z * z)))
      = Real.exp (Real.exp z - Real.log z) *
        ((Real.exp z - 1 / z) * (Real.exp z - 1 / z) + (Real.exp z - (-1 / (z * z)))) := by
    mach_ring
  rw [e]
  exact mul_pos hexp_pos hbracket

/-- `R(z) := (1/t2eval z)·t2deriv z`'s raw derivative, via `HasDerivAt_inv` (reciprocal rule) then
the product rule with `t2deriv = exp`. -/
theorem hasDerivAt_R (c2' z : Real) (hzpos : 0 < Real.exp z - Real.log c2') :
    HasDerivAt (fun x => 1 / (Real.exp x - Real.log c2') * Real.exp x)
      ((-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
          * Real.exp z
        + 1 / (Real.exp z - Real.log c2') * Real.exp z) z := by
  have hne : Real.exp z - Real.log c2' ≠ 0 := ne_of_gt hzpos
  have hinv : HasDerivAt (fun x => 1 / (Real.exp x - Real.log c2'))
      (-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2'))) z :=
    HasDerivAt_inv (fun x => Real.exp x - Real.log c2') (Real.exp z) z hne
      (hasDerivAt_evarConstC c2' z)
  exact HasDerivAt_mul (fun x => 1 / (Real.exp x - Real.log c2')) Real.exp
    (-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
    (Real.exp z) z hinv (HasDerivAt_exp z)

/-- `R`'s raw derivative value is strictly negative whenever `c2' > 1`. Established via the
identity `T · (1/(T·T)) = 1/T` (proved once, by cancellation against `mul_inv` on both `T` and
`T·T`), which collapses the raw sum to `exp(z) · (1/(T·T)) · (-log c2')` — a positive quantity
times a strictly negative one. -/
theorem R_deriv_neg (c2' z : Real) (hc2' : 1 < c2') (hzpos : 0 < Real.exp z - Real.log c2') :
    (-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
        * Real.exp z + 1 / (Real.exp z - Real.log c2') * Real.exp z < 0 := by
  have hTne : Real.exp z - Real.log c2' ≠ 0 := ne_of_gt hzpos
  have hTTpos : 0 < (Real.exp z - Real.log c2') * (Real.exp z - Real.log c2') :=
    mul_pos hzpos hzpos
  have hTTne : (Real.exp z - Real.log c2') * (Real.exp z - Real.log c2') ≠ 0 := ne_of_gt hTTpos
  have hkey : (Real.exp z - Real.log c2')
      * (1 / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
      = 1 / (Real.exp z - Real.log c2') := by
    apply mul_left_cancel hTne
    have e1 : (Real.exp z - Real.log c2') * ((Real.exp z - Real.log c2')
        * (1 / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2'))))
        = ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2'))
        * (1 / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2'))) := by mach_ring
    rw [e1, mul_inv _ hTTne, mul_inv _ hTne]
  have estep : (-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
        * Real.exp z + 1 / (Real.exp z - Real.log c2') * Real.exp z
      = -(Real.exp z * Real.log c2'
          * (1 / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))) := by
    rw [div_def (-Real.exp z) _ hTTne, ← hkey]
    generalize (1 : Real) / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')) = X
    have e5 : Real.exp z * (X * Real.log c2') = X * (Real.exp z * Real.log c2') := by
      rw [← mul_assoc, mul_comm (Real.exp z) X, mul_assoc]
    mach_ring
    rw [e5]
  rw [estep]
  have hlog_pos : 0 < Real.log c2' := log_pos_of_gt_one hc2'
  have hBpos : 0 < Real.exp z * Real.log c2' := mul_pos (Real.exp_pos z) hlog_pos
  have hCpos : 0 < Real.exp z * Real.log c2'
      * (1 / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2'))) :=
    mul_pos hBpos (one_div_pos_of_pos hTTpos)
  exact neg_neg_of_pos hCpos

/-- `0 < a → b < 0 → 0 < a - b`, a small abstract helper kept fully atomic (no embedded
divisions) so `mach_ring`'s final `a + -b = a - b` step is a plain two-atom identity, avoiding
the multi-atom reordering `mach_ring` doesn't close on its own (seen above). -/
theorem sub_pos_of_pos_of_neg {a b : Real} (ha : 0 < a) (hb : b < 0) : 0 < a - b := by
  have hnegb : 0 < -b := neg_pos_of_neg hb
  have hsum := add_pos ha hnegb
  have e : a + -b = a - b := by mach_ring
  rwa [e] at hsum

/-- `D(z) := P(z) - R(z)`'s raw derivative, via the subtraction rule on `hasDerivAt_P`/
`hasDerivAt_R` — matches exactly the raw derivative `eml_genericT1_genericT2_boundedZeros`
itself produces for `t`'s derivative on the right region. -/
theorem hasDerivAt_D (c2' z : Real) (hz : 0 < z) (hzpos : 0 < Real.exp z - Real.log c2') :
    HasDerivAt
      (fun x => Real.exp (Real.exp x - Real.log x) * (Real.exp x - 1 / x)
        - 1 / (Real.exp x - Real.log c2') * Real.exp x)
      ((Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
          + Real.exp (Real.exp z - Real.log z) * (Real.exp z - (-1 / (z * z))))
        - ((-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
            * Real.exp z + 1 / (Real.exp z - Real.log c2') * Real.exp z)) z :=
  HasDerivAt_sub _ _ _ _ z (hasDerivAt_P z hz) (hasDerivAt_R c2' z hzpos)

/-- `D`'s raw derivative is strictly positive: `P`'s positive derivative minus `R`'s negative
derivative. -/
theorem D_deriv_pos (c2' z : Real) (hc2' : 1 < c2') (hz : 0 < z)
    (hzpos : 0 < Real.exp z - Real.log c2') :
    0 < (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) * (Real.exp z - 1 / z)
          + Real.exp (Real.exp z - Real.log z) * (Real.exp z - (-1 / (z * z))))
        - ((-Real.exp z / ((Real.exp z - Real.log c2') * (Real.exp z - Real.log c2')))
            * Real.exp z + 1 / (Real.exp z - Real.log c2') * Real.exp z) :=
  sub_pos_of_pos_of_neg (P_deriv_pos z hz) (R_deriv_neg c2' z hc2' hzpos)

/-- **`D` has at most one zero on `(x0, b)`**, given `x0 = log(log c2') ≥ 0` (keeping `t1eval`
smooth throughout) and `c2' > 1` (the sign-crossing condition). Strict monotonicity from
`D_deriv_pos`, via `strictMono_of_deriv_pos` + `atMostOneZero_of_strictMono` — the SAME shape as
`g_atMostOneZero_right`, one level harder underneath. -/
theorem D_atMostOneZero (c2' : Real) (hc2' : 1 < c2') (hx0nonneg : 0 ≤ Real.log (Real.log c2'))
    (d : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, Real.log (Real.log c2') < z ∧ z < d ∧
        Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)
          - 1 / (Real.exp z - Real.log c2') * Real.exp z = 0) →
      zeros.length ≤ 1 := by
  apply atMostOneZero_of_strictMono
  intro x y hxc _hxd _hyc _hyd hxy
  apply strictMono_of_deriv_pos
    (fun w => Real.exp (Real.exp w - Real.log w) * (Real.exp w - 1 / w)
      - 1 / (Real.exp w - Real.log c2') * Real.exp w) x y hxy
  · intro w hxw _hwy
    have hw0 : Real.log (Real.log c2') < w := lt_of_lt_of_le hxc hxw
    have hwpos : 0 < w := lt_of_le_of_lt hx0nonneg hw0
    have hwzpos : 0 < Real.exp w - Real.log c2' :=
      t2eval_pos_of_gt_x0 ((exp_lt_log_c2_iff_lt_switch hc2').2 w hw0)
    exact ⟨_, hasDerivAt_D c2' w hwpos hwzpos⟩
  · intro w f' hxw _hwy hderiv
    have hw0 : Real.log (Real.log c2') < w := lt_of_lt_of_le hxc hxw
    have hwpos : 0 < w := lt_of_le_of_lt hx0nonneg hw0
    have hwzpos : 0 < Real.exp w - Real.log c2' :=
      t2eval_pos_of_gt_x0 ((exp_lt_log_c2_iff_lt_switch hc2').2 w hw0)
    rw [HasDerivAt_unique _ _ _ w hderiv (hasDerivAt_D c2' w hwpos hwzpos)]
    exact D_deriv_pos c2' w hc2' hwpos hwzpos

/-- **The main result**: `eml (eml var var) (eml var (const c2'))` — `t1` genuinely deeper than
every prior instance (its own derivative `exp x - 1/x` changes sign once) combined with a
sign-crossing `t2` — has boundedly many zeros (`≤ 3`) on any interval, given `c2' > 1` and `1 ≤
log c2'` (`c2' ≥ e`, keeping `t1`'s domain smooth throughout the region used). NO
`EMLPfaffianValidOn` assumption anywhere; this is the first result in the whole arc combining a
depth-1-compound `t1` whose OWN derivative is non-monotone-sign with a depth-1-compound
sign-crossing `t2`. -/
theorem eml_evarvar_evarConstC2_boundedZeros (c2' : Real) (hc2' : 1 < c2')
    (hx0nonneg : 0 ≤ Real.log (Real.log c2')) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  rcases lt_total (Real.log (Real.log c2')) b with hb | hb | hb
  · apply eml_genericT1_genericT2_boundedZeros
      (fun x => Real.exp x - Real.log x) (fun x => Real.exp x - 1 / x)
      (fun x => Real.exp x - Real.log c2') Real.exp
      (Real.log (Real.log c2')) a b hb
    · intro x hx0 _hxb
      have hxpos : 0 < x := lt_of_le_of_lt hx0nonneg hx0
      exact hasDerivAt_exp_sub_log x hxpos
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
      apply D_atMostOneZero c2' hc2' hx0nonneg b
      · exact hnd'
      · intro z hzmem
        exact hzd z hzmem
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
