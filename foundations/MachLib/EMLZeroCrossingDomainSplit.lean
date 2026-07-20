import MachLib.EMLZeroCrossingDepth2Compound

/-!
# The real domain-splitting case: a compound `t2` that genuinely changes sign

Continuation of path (1). Every prior result deliberately kept `t2` simple (a leaf) specifically
to AVOID this problem. This file attacks it directly: `t2 = eml var (const c2)` (`c2 > 1`) is
compound AND genuinely sign-changing — `t2.eval x = exp(x) - log(c2)`, strictly increasing
(derivative `exp(x) > 0` always), going from a negative limit as `x → -∞` to `+∞` as `x → ∞`, so
it crosses zero exactly once, at `x0 = log(log(c2))`. This is the smallest tractable instance of
the actual hard part named throughout this arc: `t = eml (const c1) t2` needs its `log(t2.eval
x)` branch to be genuinely DIFFERENT on either side of `x0` — clamped (`t.eval` collapses to the
constant `exp(c1)`) below it, the true log above it — and the two pieces need to be bounded and
glued separately, exactly the "split by sign, reduce on the bad region, bound each piece" strategy
from `EMLExplicitBoundGlue.lean`, now actually carried out on a live example rather than just
described.

**Why this instance stays tractable despite being genuinely new.** On the `x > x0` side, `t`'s
derivative works out to `-exp(x)/(exp(x)-log(c2))` — never zero (`exp(x) > 0` always, and the
denominator is exactly `t2.eval x > 0` there) — so `zero_count_bound_by_deriv` applies with `N=0`
directly: at most ONE zero on `(x0,B)`, no second-derivative or monotonicity argument needed at
all. On `x < x0`, `t.eval` collapses to the CONSTANT `exp(c1)` (never zero). The genuinely new
content is establishing `x0` itself and the two sign facts around it, not the zero-counting
technique — which turned out to be simpler here than in the `eml var var` base case.

**The result**: `t = eml (const c1) (eml var (const c2))`, for `c2 > 1`, has boundedly many zeros
(`≤ 4`) on any interval, with NO `EMLPfaffianValidOn` assumption anywhere.
-/

namespace MachLib
namespace Real

/-- `log c2 > 0` for `c2 > 1` — direct from `log`'s strict monotonicity and `log 1 = 0`. -/
theorem log_pos_of_gt_one {c2 : Real} (hc2 : 1 < c2) : 0 < Real.log c2 := by
  have h := log_lt_log zero_lt_one_ax hc2
  rwa [Real.log_one] at h

/-- The switch point `x0 = log(log c2)`, and the two sign facts either side of it: `exp x <
log c2` for `x < x0`, `exp x > log c2` for `x > x0` — both via `exp`'s strict monotonicity plus
`exp_log` inverting `log`'s definition, no converse-monotonicity lemma needed. -/
theorem exp_lt_log_c2_iff_lt_switch {c2 : Real} (hc2 : 1 < c2) :
    (∀ x : Real, x < Real.log (Real.log c2) → Real.exp x < Real.log c2) ∧
    (∀ x : Real, Real.log (Real.log c2) < x → Real.log c2 < Real.exp x) := by
  have hlc2pos : 0 < Real.log c2 := log_pos_of_gt_one hc2
  constructor
  · intro x hlt
    have h := Real.exp_lt hlt
    rwa [Real.exp_log hlc2pos] at h
  · intro x hlt
    have h := Real.exp_lt hlt
    rwa [Real.exp_log hlc2pos] at h

/-- Subtracting a fixed value from both sides of a strict inequality preserves it. Small
reusable helper: `add_lt_add_left` gives `r + p < r + q` (constant on the LEFT of an addition),
not `p - r < q - r` (constant on the RIGHT of a subtraction) — mathematically the same fact,
syntactically different, and needed three times below. -/
theorem sub_lt_sub_right_of_lt {p q r : Real} (h : p < q) : p - r < q - r := by
  have hstep := add_lt_add_left h (-r)
  have e1 : -r + p = p - r := by mach_ring
  have e2 : -r + q = q - r := by mach_ring
  rwa [e1, e2] at hstep

/-- **`exp c1 - log(exp x - log c2)` has at most one zero on `(x0,B)`, given `t2 = exp x - log
c2` is positive throughout (`hgt_side`).** Its derivative is `-(1/(exp x - log c2)) · exp x`,
never zero (`exp x > 0` always; the reciprocal factor is nonzero since `t2 > 0` there) — Rolle's
theorem then gives `≤ 0+1 = 1` directly, no monotonicity argument needed. Extracted as its own
theorem (mirroring `exp_expSubLog_sub_log_atMostTwoZeros_pos`'s own shape,
`EMLZeroCrossingDepth2Compound.lean`) so it can be `apply`-ed directly to a specific filtered
list — `zero_count_bound_by_deriv` unifies cleanly against a `∀zeros_f, ...`-shaped goal, not
against an already-specialized `(list).length ≤ K` goal. -/
theorem exp_c1_sub_log_expSubLogC2_atMostOneZero (c1 c2 x0 B : Real) (hx0B : x0 < B)
    (hgt_side : ∀ x : Real, x0 < x → Real.log c2 < Real.exp x) :
    ∀ zeros_f : List Real, zeros_f.Nodup →
      (∀ z ∈ zeros_f, x0 < z ∧ z < B ∧
        Real.exp c1 - Real.log (Real.exp z - Real.log c2) = 0) →
      zeros_f.length ≤ 1 := by
  apply zero_count_bound_by_deriv
    (fun y => Real.exp c1 - Real.log (Real.exp y - Real.log c2)) x0 B hx0B
  · intro z hz0 _hzb
    have hzpos : 0 < Real.exp z - Real.log c2 := by
      have h := hgt_side z hz0
      have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
      have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
      rwa [e2] at e
    have hinner : HasDerivAt (fun y => Real.exp y - Real.log c2) (Real.exp z) z := by
      have h := HasDerivAt_sub Real.exp (fun _ => Real.log c2) (Real.exp z) 0 z
        (HasDerivAt_exp z) (HasDerivAt_const (Real.log c2) z)
      have e : Real.exp z - 0 = Real.exp z := sub_zero _
      rwa [e] at h
    have hlog : HasDerivAt (fun y => Real.log (Real.exp y - Real.log c2))
        (1 / (Real.exp z - Real.log c2) * Real.exp z) z :=
      HasDerivAt_comp Real.log (fun y => Real.exp y - Real.log c2) (Real.exp z)
        (1 / (Real.exp z - Real.log c2)) z hinner (HasDerivAt_log_pos _ hzpos)
    exact ⟨_, HasDerivAt_sub (fun _ => Real.exp c1)
      (fun y => Real.log (Real.exp y - Real.log c2)) 0 _ z
      (HasDerivAt_const (Real.exp c1) z) hlog⟩
  · intro zeros_f' hnd' hzf'
    match zeros_f', hzf' with
    | [], _ => simp
    | w :: ws, hzf' =>
        exfalso
        obtain ⟨hw0, hwb, f'', hderiv, hf''0⟩ := hzf' w (List.mem_cons_self _ _)
        have hwpos : 0 < Real.exp w - Real.log c2 := by
          have h := hgt_side w hw0
          have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
          have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
          rwa [e2] at e
        have hinner : HasDerivAt (fun y => Real.exp y - Real.log c2) (Real.exp w) w := by
          have h := HasDerivAt_sub Real.exp (fun _ => Real.log c2) (Real.exp w) 0 w
            (HasDerivAt_exp w) (HasDerivAt_const (Real.log c2) w)
          have e : Real.exp w - 0 = Real.exp w := sub_zero _
          rwa [e] at h
        have hlog : HasDerivAt (fun y => Real.log (Real.exp y - Real.log c2))
            (1 / (Real.exp w - Real.log c2) * Real.exp w) w :=
          HasDerivAt_comp Real.log (fun y => Real.exp y - Real.log c2) (Real.exp w)
            (1 / (Real.exp w - Real.log c2)) w hinner (HasDerivAt_log_pos _ hwpos)
        have hderiv_eq : HasDerivAt
            (fun y => Real.exp c1 - Real.log (Real.exp y - Real.log c2))
            (0 - 1 / (Real.exp w - Real.log c2) * Real.exp w) w :=
          HasDerivAt_sub (fun _ => Real.exp c1)
            (fun y => Real.log (Real.exp y - Real.log c2)) 0 _ w
            (HasDerivAt_const (Real.exp c1) w) hlog
        rw [HasDerivAt_unique _ _ _ w hderiv hderiv_eq] at hf''0
        have hrecip_pos : 0 < 1 / (Real.exp w - Real.log c2) :=
          div_pos_of_pos_pos zero_lt_one_ax hwpos
        have hrecip_ne : (1 : Real) / (Real.exp w - Real.log c2) ≠ 0 := ne_of_gt hrecip_pos
        have hf''0' : (1 : Real) / (Real.exp w - Real.log c2) * Real.exp w = 0 := by
          generalize hXdef : (1 : Real) / (Real.exp w - Real.log c2) * Real.exp w = X at hf''0 ⊢
          have e : X = 0 - (0 - X) := by mach_ring
          rw [hf''0] at e
          have e2 : (0 : Real) - 0 = 0 := by mach_ring
          rwa [e2] at e
        have hexpw0 : Real.exp w = 0 :=
          PfaffianChainMod.mul_eq_zero_of_factor_ne_zero hrecip_ne hf''0'
        exact lt_irrefl_ax 0 (hexpw0 ▸ Real.exp_pos w)

/-- **`eml (const c1) (eml var (const c2))` (`c2 > 1`) has boundedly many zeros (`≤ 4`) on ANY
interval, with NO `EMLPfaffianValidOn` assumption anywhere.** The first result in this arc built
against a genuinely sign-changing compound `t2`. -/
theorem eml_const_evarConstC2_boundedZeros (c1 c2 : Real) (hc2 : 1 < c2) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.const c1)
          (EMLTree.eml EMLTree.var (EMLTree.const c2))).eval z = 0) →
      zeros.length ≤ 4 := by
  intro zeros hnd hz
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  let x0 : Real := Real.log (Real.log c2)
  obtain ⟨hlt_side, hgt_side⟩ := exp_lt_log_c2_iff_lt_switch hc2
  have heval_uniform : ∀ z, (EMLTree.eml (EMLTree.const c1)
      (EMLTree.eml EMLTree.var (EMLTree.const c2))).eval z
      = Real.exp c1 - Real.log (Real.exp z - Real.log c2) := fun z => rfl
  -- x < x0: t2.eval z < 0, clamp forces t.eval z = exp c1, never 0.
  have hlt_bound : (zeros.filter (fun z => decide (z < x0))).length ≤ 0 := by
    have hempty : zeros.filter (fun z => decide (z < x0)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro z hzmem hzlt
      have hzlt' : z < x0 := of_decide_eq_true hzlt
      obtain ⟨_, _, hfz⟩ := hz z hzmem
      rw [heval_uniform] at hfz
      have ht2neg : Real.exp z - Real.log c2 < 0 := by
        have h := hlt_side z hzlt'
        have e := sub_lt_sub_right_of_lt (r := Real.log c2) h
        have e2 : Real.log c2 - Real.log c2 = 0 := by mach_ring
        rwa [e2] at e
      have hcl : Real.log (Real.exp z - Real.log c2) = 0 := Real.log_nonpos (le_of_lt ht2neg)
      rw [hcl, sub_zero] at hfz
      exact lt_irrefl_ax 0 (hfz ▸ Real.exp_pos c1)
    rw [hempty]; simp
  -- x = x0: t2.eval x0 = 0 exactly, clamp forces t.eval x0 = exp c1, never 0.
  have hnd_ge : (zeros.filter (fun z => !decide (z < x0))).Nodup := hnd.filter _
  have heq_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => decide (z = x0))).length ≤ 1 := by
    apply EMLExplicitBound.length_le_one_of_forall_eq _ (hnd_ge.filter _)
    intro z hzmem
    rw [List.mem_filter] at hzmem
    exact of_decide_eq_true hzmem.2
  -- x > x0: t2.eval z > 0, t's derivative on this side is never zero, so at most one zero.
  have hgt_bound : ((zeros.filter (fun z => !decide (z < x0))).filter
      (fun z => !decide (z = x0))).length ≤ 1 := by
    rcases lt_total x0 b with hb | hb | hb
    · apply exp_c1_sub_log_expSubLogC2_atMostOneZero c1 c2 x0 b hb hgt_side _ (hnd_ge.filter _)
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
