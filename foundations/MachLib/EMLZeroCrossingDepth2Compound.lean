import MachLib.EMLZeroCrossingDepth1
import MachLib.KhovanskiiReduction
import MachLib.EMLExplicitBoundGlue

/-!
# A first genuine inductive step: compound left child, still no validity assumption

Continuation of path (1). `EMLZeroCrossingDepth1.lean` closed the induction's base case (all four
depth-1 shapes). This file attempts the first COMPOUND case: `t = eml t1 (const c)` with `t1`
itself depth-1 (`eml var var`) — i.e. the induction actually being USED (the zero-count bound for
`t1`'s own DERIVATIVE, established as a byproduct of closing `t1`'s base case, is reused directly
here), not just the base case restated one level down.

**Why `t2 = const c` specifically, honestly.** This deliberately AVOIDS the hardest part of the
inductive step named in `EMLExplicitBoundGlue.lean` — domain-splitting when `t2` ITSELF is
compound and sign-changing, which needs the full "collect every internal node's critical points,
refine, re-validate per piece" machinery, not attempted here. With `t2` a leaf constant, there is
no domain split to perform at all: `log(t2.eval x) = log(c)` doesn't depend on `x`. What IS new
here, genuinely: `t1` compound means `t.eval`'s own clamp-region structure (inherited from `t1`'s
internal `var` node) still has to be tracked, and `t`'s derivative computation goes through the
chain rule around `t1`'s own (already-established) derivative — the first real use of "reuse a
smaller tree's already-proven derivative-zero bound," which is the actual mechanism the full
induction needs, demonstrated on the smallest case where it can be checked without also solving
the domain-splitting problem at the same time.

**The result**: `t = eml (eml var var) (const c)`, for ANY `c` (the sign of `c` turns out not to
matter — Lean's unused-variable linter caught an initial `c > 0` hypothesis as dead), has
boundedly many zeros (`≤ 6`) on any interval, with NO `EMLPfaffianValidOn` assumption on `t` OR
on `t1 = eml var var`.
-/

namespace MachLib
namespace Real

/-- `eml var var`'s own derivative on `x > 0`, extracted as a standalone reusable fact (built
inline inside `exp_sub_log_atMostTwoZeros_pos`'s proof in `EMLZeroCrossingDepth1.lean`, not
previously exposed on its own). -/
theorem hasDerivAt_exp_sub_log (x : Real) (hx : 0 < x) :
    HasDerivAt (fun y => Real.exp y - Real.log y) (Real.exp x - 1 / x) x :=
  HasDerivAt_sub Real.exp Real.log (Real.exp x) (1 / x) x (HasDerivAt_exp x)
    (HasDerivAt_log_pos x hx)

/-- **`exp(exp(x)-log(x)) - log(c)` has at most two zeros on any `(0,B)`.** Its derivative is
`exp(exp(x)-log(x)) · (exp(x)-1/x)` (chain rule around `hasDerivAt_exp_sub_log`, plus the
constant `log c` contributing nothing) — since the `exp(...)` factor is never `0`, the
derivative is `0` exactly when `exp(x)-1/x = 0`, which `exp_sub_inv_atMostOneZero`
(`EMLZeroCrossingDepth1.lean`) already bounds by `1` on any `(0,B)`. Rolle's theorem lifts that
to `≤ 2` for the function itself. -/
theorem exp_expSubLog_sub_log_atMostTwoZeros_pos (c B : Real) (hB : 0 < B) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, 0 < z ∧ z < B ∧
        Real.exp (Real.exp z - Real.log z) - Real.log c = 0) → zeros.length ≤ 2 := by
  apply zero_count_bound_by_deriv
    (fun y => Real.exp (Real.exp y - Real.log y) - Real.log c) 0 B hB
  · intro x hx0 _hxB
    have hcomp : HasDerivAt (fun y => Real.exp (Real.exp y - Real.log y))
        (Real.exp (Real.exp x - Real.log x) * (Real.exp x - 1 / x)) x :=
      HasDerivAt_comp Real.exp (fun y => Real.exp y - Real.log y) (Real.exp x - 1 / x)
        (Real.exp (Real.exp x - Real.log x)) x (hasDerivAt_exp_sub_log x hx0) (HasDerivAt_exp _)
    exact ⟨_, HasDerivAt_sub (fun y => Real.exp (Real.exp y - Real.log y)) (fun _ => Real.log c)
      _ 0 x hcomp (HasDerivAt_const (Real.log c) x)⟩
  · intro zeros_f' hnd hzf'
    apply exp_sub_inv_atMostOneZero B zeros_f' hnd
    intro z hzmem
    obtain ⟨hz0, hzB, f'', hderiv, hf''0⟩ := hzf' z hzmem
    have hcomp : HasDerivAt (fun y => Real.exp (Real.exp y - Real.log y))
        (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z)) z :=
      HasDerivAt_comp Real.exp (fun y => Real.exp y - Real.log y) (Real.exp z - 1 / z)
        (Real.exp (Real.exp z - Real.log z)) z (hasDerivAt_exp_sub_log z hz0) (HasDerivAt_exp _)
    have hderiv_eq : HasDerivAt (fun y => Real.exp (Real.exp y - Real.log y) - Real.log c)
        (Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) - 0) z :=
      HasDerivAt_sub (fun y => Real.exp (Real.exp y - Real.log y)) (fun _ => Real.log c) _ 0 z
        hcomp (HasDerivAt_const (Real.log c) z)
    rw [HasDerivAt_unique _ _ _ z hderiv hderiv_eq] at hf''0
    have hf''0' : Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) = 0 := by
      have e : Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) - 0
          = Real.exp (Real.exp z - Real.log z) * (Real.exp z - 1 / z) := sub_zero _
      rwa [e] at hf''0
    have hne : Real.exp (Real.exp z - Real.log z) ≠ 0 := ne_of_gt (Real.exp_pos _)
    exact ⟨hz0, hzB, PfaffianChainMod.mul_eq_zero_of_factor_ne_zero hne hf''0'⟩

/-- **`exp(exp x) - log c` (`c>0`) has at most one zero anywhere.** `x ↦ exp(exp x)` is a
composition of two strictly increasing functions, hence strictly increasing, hence injective —
via `exp_lt` applied twice, no derivative needed. Covers the `x ≤ 0` clamp region of `eml (eml
var var) (const c)`, where `(eml var var).eval` reduces to the unclamped `exp x`. -/
theorem exp_exp_sub_log_atMostOneZero (c : Real) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ Real.exp (Real.exp z) - Real.log c = 0) →
      zeros.length ≤ 1 := by
  apply atMostOneZero_of_injOn
  intro x y _hxa _hxb _hya _hyb hxy hEq
  have hEq' : Real.exp (Real.exp x) - Real.log c = Real.exp (Real.exp y) - Real.log c := hEq
  have hExpExpEq : Real.exp (Real.exp x) = Real.exp (Real.exp y) := by
    have e1 : Real.exp (Real.exp x)
        = (Real.exp (Real.exp x) - Real.log c) + Real.log c := by mach_ring
    have e2 : Real.exp (Real.exp y)
        = (Real.exp (Real.exp y) - Real.log c) + Real.log c := by mach_ring
    rw [e1, e2, hEq']
  have hlt1 : Real.exp x < Real.exp y := Real.exp_lt hxy
  have hlt2 : Real.exp (Real.exp x) < Real.exp (Real.exp y) := Real.exp_lt hlt1
  rw [hExpExpEq] at hlt2
  exact lt_irrefl_ax _ hlt2

/-- **`eml (eml var var) (const c)` has boundedly many zeros (`≤ 6`) on ANY interval, for ANY
`c` — with NO `EMLPfaffianValidOn` assumption on it OR on its own left child.** The first
genuine inductive step: `t1 = eml var var`'s already-established derivative-zero bound
(`exp_sub_inv_atMostOneZero`) is reused directly, via the chain rule, to bound the COMPOUND
tree `eml t1 (const c)` — not just `t1` itself. A small surprise found while assembling this
(Lean's unused-variable linter caught it): the argument never needs `c > 0` — every step goes
through `Real.log c` symbolically, and its clamped-or-not value never mattered to the bound. -/
theorem eml_evarvar_const_boundedZeros (c : Real) (a b : Real) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧
        (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var) (EMLTree.const c)).eval z = 0) →
      zeros.length ≤ 6 := by
  intro zeros hnd hz
  haveI : DecidableEq Real := fun x y => Classical.propDecidable (x = y)
  have heval_uniform : ∀ z, (EMLTree.eml (EMLTree.eml EMLTree.var EMLTree.var)
      (EMLTree.const c)).eval z = Real.exp ((EMLTree.eml EMLTree.var EMLTree.var).eval z)
      - Real.log c := fun z => rfl
  have hlt_bound : (zeros.filter (fun z => decide (z ≤ 0))).length ≤ 2 := by
    have hnd_le : (zeros.filter (fun z => decide (z ≤ 0))).Nodup := hnd.filter _
    have hlt0_bound :
        ((zeros.filter (fun z => decide (z ≤ 0))).filter (fun z => decide (z < 0))).length ≤ 1 := by
      apply exp_exp_sub_log_atMostOneZero c a 0 _ (hnd_le.filter _)
      intro z hzmem
      rw [List.mem_filter, List.mem_filter] at hzmem
      obtain ⟨⟨hzz, _⟩, hzlt⟩ := hzmem
      have hzlt' : z < 0 := of_decide_eq_true hzlt
      obtain ⟨hza, _, hfz⟩ := hz z hzz
      rw [heval_uniform] at hfz
      have hcl : (EMLTree.eml EMLTree.var EMLTree.var).eval z = Real.exp z := by
        show Real.exp z - Real.log z = Real.exp z
        rw [Real.log_nonpos (le_of_lt hzlt')]; exact sub_zero _
      rw [hcl] at hfz
      exact ⟨hza, hzlt', hfz⟩
    have heq0_bound :
        ((zeros.filter (fun z => decide (z ≤ 0))).filter (fun z => !decide (z < 0))).length ≤ 1 := by
      apply EMLExplicitBound.length_le_one_of_forall_eq _ (hnd_le.filter _)
      intro z hzmem
      rw [List.mem_filter] at hzmem
      obtain ⟨hzle, hzge⟩ := hzmem
      rw [List.mem_filter] at hzle
      have hzle' : z ≤ 0 := of_decide_eq_true hzle.2
      have hzge' : ¬ z < 0 := of_decide_eq_false (by simpa using hzge)
      rcases lt_total z 0 with h | h | h
      · exact absurd h hzge'
      · exact h
      · exact absurd (lt_of_lt_of_le h hzle') (lt_irrefl_ax 0)
    have hpart0 : ((zeros.filter (fun z => decide (z ≤ 0))).filter (fun z => decide (z < 0))).length
        + ((zeros.filter (fun z => decide (z ≤ 0))).filter (fun z => !decide (z < 0))).length
        = (zeros.filter (fun z => decide (z ≤ 0))).length :=
      MultiVarMod.length_filter_partition (fun z => decide (z < 0))
        (zeros.filter (fun z => decide (z ≤ 0)))
    omega
  have hnd_hi : (zeros.filter (fun z => !decide (z ≤ 0))).Nodup := hnd.filter _
  have hgt_bound : (zeros.filter (fun z => !decide (z ≤ 0))).length ≤ 2 := by
    rcases lt_total 0 b with hb | hb | hb
    · apply exp_expSubLog_sub_log_atMostTwoZeros_pos c b hb _ hnd_hi
      intro z hzmem
      rw [List.mem_filter] at hzmem
      obtain ⟨hzz, hzgt⟩ := hzmem
      have hzgt' : 0 < z := by
        have hne0 := of_decide_eq_false (show decide (z ≤ 0) = false by simpa using hzgt)
        rcases lt_total z 0 with h | h | h
        · exact absurd (le_of_lt h) hne0
        · exact absurd (h ▸ le_refl (0 : Real)) hne0
        · exact h
      obtain ⟨_, hzb, hfz⟩ := hz z hzz
      rw [heval_uniform] at hfz
      have hcl : (EMLTree.eml EMLTree.var EMLTree.var).eval z = Real.exp z - Real.log z := rfl
      rw [hcl] at hfz
      exact ⟨hzgt', hzb, hfz⟩
    · have hempty : zeros.filter (fun z => !decide (z ≤ 0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hzmem hzgt
        obtain ⟨_, hzb, _⟩ := hz z hzmem
        have hzlt0 : z < 0 := hb ▸ hzb
        have hzle : z ≤ 0 := le_of_lt hzlt0
        have hd : decide (z ≤ 0) = true := decide_eq_true hzle
        simp [hd] at hzgt
      rw [hempty]; simp
    · have hempty : zeros.filter (fun z => !decide (z ≤ 0)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro z hzmem hzgt
        obtain ⟨_, hzb, _⟩ := hz z hzmem
        have hzlt0 : z < 0 := lt_trans_ax hzb hb
        have hzle : z ≤ 0 := le_of_lt hzlt0
        have hd : decide (z ≤ 0) = true := decide_eq_true hzle
        simp [hd] at hzgt
      rw [hempty]; simp
  have hpart : (zeros.filter (fun z => decide (z ≤ 0))).length
      + (zeros.filter (fun z => !decide (z ≤ 0))).length = zeros.length :=
    MultiVarMod.length_filter_partition (fun z => decide (z ≤ 0)) zeros
  omega

end Real
end MachLib
