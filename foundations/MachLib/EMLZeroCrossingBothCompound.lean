import MachLib.EMLZeroCrossingDomainSplitGeneral

/-!
# Both children compound, simultaneously: combining the two previously-separate mechanisms

Every prior result in this arc kept ONE child simple to isolate a single mechanism:
`EMLZeroCrossingDepth2Compound.lean` allowed `t1` compound but forced `t2 = const c`;
`EMLZeroCrossingDomainSplit(General).lean` allowed `t2` compound (with a sign crossing) but
forced `t1 = const c1`. This file combines them for the first time: `t1` AND `t2` are BOTH
depth-1 compound trees at once.

**The instance.** `t1 = eml var (const c1')`, `t2 = eml var (const c2')`, `c2' > 1` (so `t2` has
a sign crossing, same shape as the domain-split file). `t1eval x = exp x - log c1'`, `t2eval x =
exp x - log c2'` — note `t1` needs NO positivity restriction on `c1'` at all: it is only ever fed
into the outer `exp`, never `log`'d, so `log c1'` is just some fixed real regardless of `c1'`'s
sign.

**Why this stays tractable.** The left region (`x < x0`, `t2 ≤ 0`) collapses exactly as before —
`t.eval x = exp(t1eval x) - log(t2eval x) = exp(t1eval x) - 0 = exp(t1eval x)`, POSITIVE
unconditionally (`Real.exp_pos`, regardless of `t1eval x`'s own value) — so `t1` being compound
doesn't complicate the left side even slightly; the same "clamp forces positivity" argument goes
through verbatim.

The right region (`x > x0`) is the genuinely new content. `t`'s derivative there (chain + product
+ sub rules) is `D(x) := exp(t1eval x)·exp(x) - (1/t2eval x)·exp(x)` — a genuine DIFFERENCE of two
terms, not reducible to a single scaled factor the way the const-`t1` case's derivative was.
Bounding `D`'s zeros needs a second layer: `D(x) = 0 ↔ g(x) := exp(t1eval x)·t2eval x - 1 = 0`
(clearing denominators, valid since `exp x ≠ 0` and `t2eval x ≠ 0` there), and `g`'s own
derivative (product rule) factors as `g'(x) = [exp(t1eval x)·exp x] · (exp x - (log c2' - 1))` —
a product of a manifestly positive term and a term that is POSITIVE WHENEVER `log c2' ≤ 1` (i.e.
`c2' ≤ e`): `exp x > 0 ≥ log c2' - 1`. So under that side condition, `g` is strictly monotonic
globally (no domain restriction needed), hence injective, hence has at most one zero anywhere —
transferring (via the `D=0 → g=0` bridge) to `D` having at most one zero on `(x0,b)`, hence (via
`zero_count_bound_by_deriv`) `t` itself having at most two zeros there.

**Honest scope.** This closes ONE concrete `t1`/`t2` shape (both `eml var (const _)`), under the
side condition `1 < c2' ≤ exp 1` — chosen specifically because it makes `g`'s derivative-sign
argument a SINGLE monotonicity check, not two (the `c2' > e` case would need `g` itself bounded
via a "valley" argument — decreasing then increasing — a second Rolle layer not attempted here).
`c1'` is completely unrestricted. Matches this arc's established pattern: concrete tractable
instance first, generalization (if any) later.
-/

namespace MachLib
namespace Real

/-- `t1eval x = exp x - log c1'` has derivative `exp x` at every point, no domain restriction —
`c1'` never appears under a `log` of `x`, only as an additive constant. -/
theorem hasDerivAt_evarConstC (c' z : Real) :
    HasDerivAt (fun x => Real.exp x - Real.log c') (Real.exp z) z := by
  have hd := HasDerivAt_sub Real.exp (fun _ => Real.log c') (Real.exp z) 0 z
    (HasDerivAt_exp z) (HasDerivAt_const (Real.log c') z)
  have e : Real.exp z - 0 = Real.exp z := sub_zero _
  rwa [e] at hd

/-- `g(x) := exp(exp x - log c1') · (exp x - log c2') - 1`'s derivative at any point, via the
product rule (`f = exp∘t1eval`, `g = t2eval`) then the constant-subtraction rule. Raw combinator
form, not yet simplified. -/
theorem hasDerivAt_g (c1' c2' z : Real) :
    HasDerivAt (fun x => Real.exp (Real.exp x - Real.log c1') * (Real.exp x - Real.log c2') - 1)
      (Real.exp (Real.exp z - Real.log c1') * Real.exp z * (Real.exp z - Real.log c2')
        + Real.exp (Real.exp z - Real.log c1') * Real.exp z) z := by
  have hf : HasDerivAt (fun x => Real.exp (Real.exp x - Real.log c1'))
      (Real.exp (Real.exp z - Real.log c1') * Real.exp z) z :=
    HasDerivAt_comp Real.exp (fun x => Real.exp x - Real.log c1') (Real.exp z)
      (Real.exp (Real.exp z - Real.log c1')) z (hasDerivAt_evarConstC c1' z) (HasDerivAt_exp _)
  have hg : HasDerivAt (fun x => Real.exp x - Real.log c2') (Real.exp z) z :=
    hasDerivAt_evarConstC c2' z
  have hmul := HasDerivAt_mul (fun x => Real.exp (Real.exp x - Real.log c1'))
    (fun x => Real.exp x - Real.log c2')
    (Real.exp (Real.exp z - Real.log c1') * Real.exp z) (Real.exp z) z hf hg
  have hsub := HasDerivAt_sub
    (fun x => Real.exp (Real.exp x - Real.log c1') * (Real.exp x - Real.log c2'))
    (fun _ => (1 : Real))
    (Real.exp (Real.exp z - Real.log c1') * Real.exp z * (Real.exp z - Real.log c2')
      + Real.exp (Real.exp z - Real.log c1') * Real.exp z)
    0 z hmul (HasDerivAt_const 1 z)
  have e : Real.exp (Real.exp z - Real.log c1') * Real.exp z * (Real.exp z - Real.log c2')
      + Real.exp (Real.exp z - Real.log c1') * Real.exp z - 0
      = Real.exp (Real.exp z - Real.log c1') * Real.exp z * (Real.exp z - Real.log c2')
        + Real.exp (Real.exp z - Real.log c1') * Real.exp z := sub_zero _
  rwa [e] at hsub

/-- `g`'s raw derivative value is strictly positive whenever `log c2' ≤ 1` — it factors as
`(positive) · (exp z - (log c2' - 1))`, and the bracket is positive since `exp z > 0 ≥ log c2' -
1`. -/
theorem g_deriv_pos (c1' c2' z : Real) (hle : Real.log c2' ≤ 1) :
    0 < Real.exp (Real.exp z - Real.log c1') * Real.exp z * (Real.exp z - Real.log c2')
        + Real.exp (Real.exp z - Real.log c1') * Real.exp z := by
  have hP : 0 < Real.exp (Real.exp z - Real.log c1') * Real.exp z :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  have h0 : (0 : Real) ≤ 1 - Real.log c2' := by
    have h := add_le_add_left hle (-(Real.log c2'))
    have e1 : -(Real.log c2') + Real.log c2' = 0 := by mach_ring
    have e2 : -(Real.log c2') + 1 = 1 - Real.log c2' := by mach_ring
    rwa [e1, e2] at h
  have hbracket : 0 < Real.exp z - Real.log c2' + 1 := by
    have hexppos := Real.exp_pos z
    have hsum := add_le_add_left h0 (Real.exp z)
    have e1 : Real.exp z + 0 = Real.exp z := add_zero _
    have e2 : Real.exp z + (1 - Real.log c2') = Real.exp z - Real.log c2' + 1 := by mach_ring
    rw [e1, e2] at hsum
    exact lt_of_lt_of_le hexppos hsum
  have e : Real.exp (Real.exp z - Real.log c1') * Real.exp z * (Real.exp z - Real.log c2')
        + Real.exp (Real.exp z - Real.log c1') * Real.exp z
      = (Real.exp (Real.exp z - Real.log c1') * Real.exp z) * (Real.exp z - Real.log c2' + 1) := by
    mach_ring
  rw [e]
  exact mul_pos hP hbracket

/-- **`g` has at most one zero on any open interval.** Strict monotonicity from a positive
derivative (`g_deriv_pos`), via `strictMono_of_deriv_pos` + `atMostOneZero_of_strictMono`. No
domain restriction needed — the positivity holds everywhere given `log c2' ≤ 1`. -/
theorem g_atMostOneZero (c1' c2' : Real) (hle : Real.log c2' ≤ 1) (c d : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, c < z ∧ z < d ∧
        Real.exp (Real.exp z - Real.log c1') * (Real.exp z - Real.log c2') - 1 = 0) →
      zeros.length ≤ 1 := by
  apply atMostOneZero_of_strictMono
  intro x y _hxc _hxd _hyc _hyd hxy
  apply strictMono_of_deriv_pos
    (fun w => Real.exp (Real.exp w - Real.log c1') * (Real.exp w - Real.log c2') - 1) x y hxy
  · intro w _ _
    exact ⟨_, hasDerivAt_g c1' c2' w⟩
  · intro w f' _ _ hderiv
    rw [HasDerivAt_unique _ _ _ w hderiv (hasDerivAt_g c1' c2' w)]
    exact g_deriv_pos c1' c2' w hle

/-- `t2eval z = exp z - log c2'` is positive whenever `z` is past the sign crossing, converting
the strict `log c2' < exp z` fact into the subtraction form needed downstream. -/
theorem t2eval_pos_of_gt_x0 {c2' z : Real} (hgt : Real.log c2' < Real.exp z) :
    0 < Real.exp z - Real.log c2' := by
  have e := sub_lt_sub_right_of_lt (r := Real.log c2') hgt
  have e2 : Real.log c2' - Real.log c2' = 0 := by mach_ring
  rwa [e2] at e

/-- **The algebraic bridge**: `t`'s raw derivative (`D`) vanishing implies `g` vanishes, clearing
denominators via `E ≠ 0` and `T ≠ 0`. Proved abstractly over three atoms to keep the `1/T` division
fully opaque throughout (`mach_ring` cannot relate different syntactic forms of a division, so
every step here stays in terms of the SAME literal `1/T` atom introduced by `generalize`). -/
theorem cross_cancel_bridge {A E T : Real} (hE : E ≠ 0) (hT : T ≠ 0)
    (hD : A * E - 1 / T * E = 0) : A * T - 1 = 0 := by
  generalize hRdef : (1 : Real) / T = R at hD
  have step1 : A * E = R * E := by
    have e : A * E = (A * E - R * E) + R * E := by mach_ring
    rw [hD] at e
    have e2 : (0 : Real) + R * E = R * E := by mach_ring
    rwa [e2] at e
  have step2 : E * A = E * R := by
    have e1 : E * A = A * E := by mach_ring
    have e2 : E * R = R * E := by mach_ring
    rw [e1, e2]; exact step1
  have step3 : A = R := mul_left_cancel hE step2
  have step4 : R * T = 1 := by
    rw [← hRdef, mul_comm]
    exact mul_inv T hT
  have step5 : A * T = 1 := by rw [step3]; exact step4
  rw [step5]; mach_ring

/-- `t`'s own derivative on the right region (`z` past the sign crossing), via chain + product +
sub rules — the raw combinator-produced form, matching what `cross_cancel_bridge` expects. -/
theorem hasDerivAt_t_right (c1' c2' z : Real) (hzpos : 0 < Real.exp z - Real.log c2') :
    HasDerivAt
      (fun y => Real.exp (Real.exp y - Real.log c1') - Real.log (Real.exp y - Real.log c2'))
      (Real.exp (Real.exp z - Real.log c1') * Real.exp z
        - 1 / (Real.exp z - Real.log c2') * Real.exp z) z := by
  have hlog : HasDerivAt (fun y => Real.log (Real.exp y - Real.log c2'))
      (1 / (Real.exp z - Real.log c2') * Real.exp z) z :=
    HasDerivAt_comp Real.log (fun y => Real.exp y - Real.log c2') (Real.exp z)
      (1 / (Real.exp z - Real.log c2')) z (hasDerivAt_evarConstC c2' z)
      (HasDerivAt_log_pos _ hzpos)
  have hexp : HasDerivAt (fun y => Real.exp (Real.exp y - Real.log c1'))
      (Real.exp (Real.exp z - Real.log c1') * Real.exp z) z :=
    HasDerivAt_comp Real.exp (fun y => Real.exp y - Real.log c1') (Real.exp z)
      (Real.exp (Real.exp z - Real.log c1')) z (hasDerivAt_evarConstC c1' z)
      (HasDerivAt_exp _)
  exact HasDerivAt_sub (fun y => Real.exp (Real.exp y - Real.log c1'))
    (fun y => Real.log (Real.exp y - Real.log c2'))
    (Real.exp (Real.exp z - Real.log c1') * Real.exp z)
    (1 / (Real.exp z - Real.log c2') * Real.exp z) z hexp hlog

/-- **The main result**: `eml (eml var (const c1')) (eml var (const c2'))` — BOTH children
depth-1 compound simultaneously — has boundedly many zeros (`≤3`) on ANY interval, given `c2' > 1`
(the sign-crossing condition) and `Real.log c2' ≤ 1` (i.e. `c2' ≤ e`, keeping `g`'s derivative
sign a single monotonicity check). `c1'` is completely unrestricted. NO `EMLPfaffianValidOn`
assumption anywhere. -/
theorem eml_evarConstC1_evarConstC2_boundedZeros (c1' c2' : Real) (hc2' : 1 < c2')
    (hc2'le : Real.log c2' ≤ 1) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1'))
          (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z = 0) →
      zeros.length ≤ 3 := by
  intro zeros hnd hz
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  let x0 : Real := Real.log (Real.log c2')
  obtain ⟨hlt_side, hgt_side⟩ := exp_lt_log_c2_iff_lt_switch hc2'
  have heval_uniform : ∀ z, (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1'))
      (EMLTree.eml EMLTree.var (EMLTree.const c2'))).eval z
      = Real.exp (Real.exp z - Real.log c1') - Real.log (Real.exp z - Real.log c2') :=
    fun z => rfl
  have hlt_bound : (zeros.filter (fun z => decide (z < x0))).length ≤ 0 := by
    have hempty : zeros.filter (fun z => decide (z < x0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hzmem hzlt
      have hzlt' : z < x0 := of_decide_eq_true hzlt
      obtain ⟨_, _, hfz⟩ := hz z hzmem
      rw [heval_uniform] at hfz
      have ht2neg : Real.exp z - Real.log c2' < 0 := by
        have h := hlt_side z hzlt'
        have e := sub_lt_sub_right_of_lt (r := Real.log c2') h
        have e2 : Real.log c2' - Real.log c2' = 0 := by mach_ring
        rwa [e2] at e
      have hcl : Real.log (Real.exp z - Real.log c2') = 0 := Real.log_nonpos (le_of_lt ht2neg)
      rw [hcl, sub_zero] at hfz
      exact lt_irrefl_ax 0 (hfz ▸ Real.exp_pos (Real.exp z - Real.log c1'))
    rw [hempty]; simp
  have hnd_ge : (zeros.filter (fun z => !decide (z < x0))).Nodup := hnd.filter _
  have heq_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => decide (z = x0))).length ≤ 1 := by
    apply EMLExplicitBound.length_le_one_of_forall_eq _ (hnd_ge.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    exact of_decide_eq_true hzmem.2
  have hgt_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => !decide (z = x0))).length ≤ 2 := by
    rcases lt_total x0 b with hb | hb | hb
    · have hgt_general : ∀ zeros_f' : List Real, zeros_f'.Nodup →
          (∀ z ∈ zeros_f', x0 < z ∧ z < b ∧
            Real.exp (Real.exp z - Real.log c1') - Real.log (Real.exp z - Real.log c2') = 0) →
          zeros_f'.length ≤ 2 :=
        zero_count_bound_by_deriv
          (fun y => Real.exp (Real.exp y - Real.log c1') - Real.log (Real.exp y - Real.log c2'))
          x0 b hb
          (fun z hz0 _hzb =>
            ⟨_, hasDerivAt_t_right c1' c2' z (t2eval_pos_of_gt_x0 (hgt_side z hz0))⟩)
          1
          (fun zeros_d hnd' hzd => by
            apply g_atMostOneZero c1' c2' hc2'le x0 b
            · exact hnd'
            · intro z hzmem
              obtain ⟨hz0, hzb, f'', hderiv', hf''0⟩ := hzd z hzmem
              have hzpos : 0 < Real.exp z - Real.log c2' := t2eval_pos_of_gt_x0 (hgt_side z hz0)
              rw [HasDerivAt_unique _ _ _ z hderiv' (hasDerivAt_t_right c1' c2' z hzpos)] at hf''0
              have hgz : Real.exp (Real.exp z - Real.log c1') * (Real.exp z - Real.log c2') - 1
                  = 0 := cross_cancel_bridge (ne_of_gt (Real.exp_pos z)) (ne_of_gt hzpos) hf''0
              exact ⟨hz0, hzb, hgz⟩)
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
      rw [heval_uniform] at hfz
      exact ⟨hzgt0, hzb, hfz⟩
    · have hempty : (zeros.filter (fun z => !decide (z < x0))).filter
          (fun z => !decide (z = x0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hzmem _hzne
        rw [List.mem_filter] at hzmem
        obtain ⟨hzz, hzge⟩ := hzmem
        obtain ⟨_, hzb, _⟩ := hz z hzz
        have hzltx0 : z < x0 := hb ▸ hzb
        have hd : decide (z < x0) = true := decide_eq_true hzltx0
        rw [hd] at hzge
        simp at hzge
      rw [hempty]; simp
    · have hempty : (zeros.filter (fun z => !decide (z < x0))).filter
          (fun z => !decide (z = x0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hzmem _hzne
        rw [List.mem_filter] at hzmem
        obtain ⟨hzz, hzge⟩ := hzmem
        obtain ⟨_, hzb, _⟩ := hz z hzz
        have hzltx0 : z < x0 := lt_trans_ax hzb hb
        have hd : decide (z < x0) = true := decide_eq_true hzltx0
        rw [hd] at hzge
        simp at hzge
      rw [hempty]; simp
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

end Real
end MachLib
