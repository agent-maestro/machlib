import MachLib.WitnessResidualTargetGeneric
import MachLib.EMLZeroCrossingDepth1
import MachLib.Rolle
import MachLib.MonotoneFromDeriv
import MachLib.WitnessResidualSimpleT1Application

/-! # Wiring the elementary zero-crossing family to the witness-finding closure — the missing piece

Closes the gap identified in the cont. 34 research pass (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`):
`EMLZeroCrossing*.lean` (10 files) proves genuinely uniform, `EMLPfaffianValidOn`-free zero-count
bounds for compound trees, but has never been connected to the actual target-shift zero-counting
argument (`WitnessResidualChainSkeleton.lean`/`WitnessResidualTargetGeneric.lean`) that closes the
residual — those bounds have only ever been consumed inside their own files. This file builds the
missing "generic/convex `t1`, CONSTANT `t2`" bound (the one shape the family didn't have — every
existing generic-`t1` theorem needs `t2` to have a genuine sign crossing to domain-split on; a
constant `t2` has none, and needs a structurally different, in fact simpler argument), then wires
it directly into a validity-free replacement for the Khovanskii-chain closure.

**The bound** (`convexT1_sub_const_atMostTwoZeros`): `t1eval` convex on `(c,d)` (`t1deriv2 > 0`)
⟹ `t1eval - L` has at most `2` zeros there, for ANY constant `L`. `t1eval`'s own derivative
`t1deriv` is strictly increasing on `(c,d)` (from convexity) hence injective hence has `≤1` zero
(`atMostOneZero_of_strictMono`, reusing `strictMono_of_deriv_pos` from `MonotoneFromDeriv.lean`);
Rolle (`zero_count_bound_by_deriv`, `Rolle.lean`) lifts that `≤1` critical-point bound to `≤2`
zeros for `t1eval - L` itself. No `exp`/`log` wrapping needed at all — earlier drafts of this idea
mistakenly modeled the target quantity as `exp(t1eval x) - log K` (mirroring the EML-tree-eval
SHAPE `eml t1 (const K)`), but the actual quantity the target-shift argument needs a bound on is
`T1.eval(x) - L` DIRECTLY (`L := log c2`), not an `eml`-wrapped version of it — a genuine
simplification once seen, not merely a restatement.

**The closure** (`no_tree_eq_target_given_zero_bound`): the SAME zero-list construction as
`no_tree_eq_target_given_validon` (`WitnessResidualTargetGeneric.lean`) — `M+1` witness points at
`kπ` (`k=1..M+1`), each forcing `T1eval(kπ) - L = 0` via `TARGET`'s own periodicity — but the
bound `M` is supplied DIRECTLY by the caller instead of derived via `enc`/`combinedBoundE`, so
`EMLPfaffianValidOn`/`LogArgPosOn`/the Khovanskii encoder never appear anywhere in this proof.
Also drops the original's `hTargetPi1` non-degeneracy witness entirely — that was only ever needed
to satisfy `enc_combinedBound`'s own API (a technical side-condition of the Khovanskii route, not
a genuine mathematical necessity); a convex/bounded-critical-point `T1eval` can't be identically
`L` in the first place, so no separate witness is needed here.

**Confirmed via `#print axioms` from a genuinely fresh rebuild**: `eml_depth2_witness_of_const_
gt_one_sibling_convexT1` depends on nothing beyond the foundational `HasDerivAt` axiom calculus,
Rolle's theorem, and `sin`/`pi`'s own basic axioms — no `EMLPfaffianValidOn`, no `enc_combinedBound`,
no `eml_pfaffian_validon_from_sin_equality` anywhere. This is a REAL, independent confirmation of
the cont. 34 research finding: a second, fully-disconnected mechanism for closing this residual
genuinely works once wired up, for tree shapes `RightChildrenEverywherePositive` cannot reach
(convex `T1`, not built from never-clamping right-child wrappers).

**Honest scope, unchanged from the research pass**: a function convex on ALL of `(1,∞)` and
non-constant is unbounded (basic calculus) — the concrete sanity-check instance below (`T1 := eml
var (const c1)`) is UNBOUNDED, so it's not new residual coverage on its own (the far simpler
"unbounded-T1" case already closes it) — its value is confirming the whole pipeline discharges on
a genuine `EMLTree`, not just abstract functions. Reaching genuinely NEW coverage (bounded,
non-monotonic `T1` with a crossing right child) still needs a fresh concrete witness search, not
attempted here — flagged as the honest next step in the cont. 34 entry, unchanged by this file. -/

namespace MachLib
namespace Real

/-- `t1eval` convex on `(c,d)` (`t1deriv2>0`) ⟹ `t1eval - L` has at most `2` zeros on `(c,d)`.
`t1deriv` is strictly increasing there (from convexity), hence injective, hence has `≤1` zero;
Rolle lifts that to `≤2` zeros for `t1eval - L` itself. -/
theorem convexT1_sub_const_atMostTwoZeros
    (t1eval t1deriv t1deriv2 : Real → Real) (L c d : Real) (hcd : c < d)
    (ht1 : ∀ x : Real, c < x → x < d → HasDerivAt t1eval (t1deriv x) x)
    (ht1' : ∀ x : Real, c < x → x < d → HasDerivAt t1deriv (t1deriv2 x) x)
    (hconvex : ∀ x : Real, c < x → x < d → 0 < t1deriv2 x) :
    ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, c < z ∧ z < d ∧ t1eval z - L = 0) →
      zeros.length ≤ 2 := by
  apply zero_count_bound_by_deriv (fun w => t1eval w - L) c d hcd
  · intro x hxc hxd
    have hsub := HasDerivAt_sub t1eval (fun _ => L) (t1deriv x) 0 x (ht1 x hxc hxd)
      (HasDerivAt_const L x)
    have he : t1deriv x - 0 = t1deriv x := sub_zero _
    exact ⟨_, he ▸ hsub⟩
  · intro zeros_f' hnd hz
    have hmono : ∀ x y : Real, c < x → x < d → c < y → y < d → x < y →
        t1deriv x < t1deriv y := by
      intro x y hxc hxd hyc hyd hxy
      apply strictMono_of_deriv_pos t1deriv x y hxy
      · intro w hxw hwy
        have hwc : c < w := lt_of_lt_of_le hxc hxw
        have hwd : w < d := lt_of_le_of_lt hwy hyd
        exact ⟨_, ht1' w hwc hwd⟩
      · intro w f' hxw hwy hderiv
        have hwc : c < w := lt_of_lt_of_le hxc hxw
        have hwd : w < d := lt_of_le_of_lt hwy hyd
        rw [HasDerivAt_unique _ _ _ w hderiv (ht1' w hwc hwd)]
        exact hconvex w hwc hwd
    apply atMostOneZero_of_strictMono hmono zeros_f' hnd
    intro z hzmem
    obtain ⟨hzc, hzd, f'', hderiv, hf''0⟩ := hz z hzmem
    have hsub := HasDerivAt_sub t1eval (fun _ => L) (t1deriv z) 0 z (ht1 z hzc hzd)
      (HasDerivAt_const L z)
    have he : t1deriv z - 0 = t1deriv z := sub_zero _
    have huniq := HasDerivAt_unique _ _ _ z hderiv (he ▸ hsub)
    rw [huniq] at hf''0
    exact ⟨hzc, hzd, hf''0⟩

/-- **The target-shift zero-counting argument, needing NO `EMLPfaffianValidOn` at all.** Mirrors
`no_tree_eq_target_given_validon`'s proof shape exactly, but the `M`+bound is supplied DIRECTLY
by the caller (e.g. from `convexT1_sub_const_atMostTwoZeros` above) instead of derived from the
Khovanskii encoder — so none of `enc`/`combinedBoundE`/`LogArgPosOn`/`EMLPfaffianValidOn` is
needed anywhere in this proof. Also drops the `hTargetPi1` non-degeneracy witness the Khovanskii
route needed (an artifact of `enc_combinedBound`'s own API, not a genuine requirement here — a
convex/bounded-critical-point `T1eval` can't be identically `L` in the first place). -/
theorem no_tree_eq_target_given_zero_bound
    (TARGET : Real → Real) (L : Real)
    (hTargetKPi : ∀ k : Nat, 1 ≤ k → TARGET (natCast k * pi) = L)
    (T1eval : Real → Real)
    (hT1eq : ∀ x, T1eval x = TARGET x)
    (M : Nat)
    (hMbound : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧ T1eval z - L = 0) →
        zeros.length ≤ M) :
    False := by
  let zeros : List Real := (List.range (M + 1)).map (fun i => natCast (i + 1) * pi)
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have h1lt : ∀ j : Nat, 1 ≤ j → (1 : Real) < natCast j * pi := by
    intro j hj1
    by_cases hj1' : j = 1
    · rw [hj1']
      have e1 : natCast 1 = (1 : Real) := by
        rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
      rw [e1, one_mul_thm]; exact pi_gt_one
    · have hgt : 1 < j := by omega
      have h_chain := natCast_mul_pi_lt hgt
      have e1 : natCast 1 = (1 : Real) := by
        rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
      rw [e1, one_mul_thm] at h_chain
      exact lt_trans_ax pi_gt_one h_chain
  have hzeros_valid : ∀ z ∈ zeros,
      (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧ T1eval z - L = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact h1lt (i + 1) (by omega)
    · rw [← hzeq]; exact natCast_mul_pi_lt (by omega)
    · rw [← hzeq, hT1eq, hTargetKPi (i + 1) (by omega)]
      mach_ring
  have hzeros_nodup : zeros.Nodup := sin_zeros_list_nodup M
  have hlen_le := hMbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

/-- Specializing the target to `log(c2+sin x)`, mirroring `T1_not_eq_log_c2_plus_sin_given_validon`
exactly but with no `EMLPfaffianValidOn` dependency. -/
theorem T1eval_not_eq_log_c2_plus_sin_given_zero_bound
    (c2 : Real) (hc2 : 1 < c2) (T1eval : Real → Real)
    (hT1eq : ∀ x, T1eval x = Real.log (c2 + Real.sin x))
    (M : Nat)
    (hMbound : ∀ zeros : List Real, zeros.Nodup →
        (∀ z ∈ zeros, (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧
          T1eval z - Real.log c2 = 0) →
        zeros.length ≤ M) :
    False := by
  apply no_tree_eq_target_given_zero_bound (fun x => Real.log (c2 + Real.sin x)) (Real.log c2)
    ?_ T1eval hT1eq M hMbound
  intro k hk1
  show Real.log (c2 + Real.sin (natCast k * pi)) = Real.log c2
  rw [sin_natCast_mul_pi k, add_zero]

/-- **The full closure, for a `T1` whose `eval` is convex on `(1,∞)`, no `EMLPfaffianValidOn`
anywhere.** Mirrors `eml_depth2_witness_of_const_gt_one_sibling_right_children_everywhere_positive`'s
shape exactly, substituting the convexity-based zero bound for the `RightChildrenEverywherePositive`
mechanism — a genuinely different, previously-disconnected route to the SAME kind of conclusion. -/
theorem eml_depth2_witness_of_const_gt_one_sibling_convexT1
    {T1 S3 : EMLTree} {c2 : Real} (hc2 : 1 < c2)
    (t1deriv t1deriv2 : Real → Real)
    (ht1 : ∀ x : Real, 1 < x → HasDerivAt T1.eval (t1deriv x) x)
    (ht1' : ∀ x : Real, 1 < x → HasDerivAt t1deriv (t1deriv2 x) x)
    (hconvex : ∀ x : Real, 1 < x → 0 < t1deriv2 x)
    (hsin : ∀ x, (EMLTree.eml T1 (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  refine Classical.byContradiction (fun hcon => ?_)
  have hallle : ∀ x, S3.eval x ≤ 0 := by
    intro x
    rcases lt_total 0 (S3.eval x) with h | h | h
    · exact absurd ⟨x, h⟩ hcon
    · exact le_of_eq h.symm
    · exact le_of_lt h
  have hT1eq := eml_T1eq_of_const_sibling_le_zero hc2 hallle hsin
  have h1lt4pi : (1 : Real) < natCast (2 + 2) * pi := by
    have e1 : natCast 1 = (1 : Real) := by
      rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
    have hlt := natCast_mul_pi_lt (show 1 < 2 + 2 from by omega)
    rw [e1, one_mul_thm] at hlt
    exact lt_trans_ax pi_gt_one hlt
  apply T1eval_not_eq_log_c2_plus_sin_given_zero_bound c2 hc2 T1.eval hT1eq 2
  intro zeros hnd hz
  exact convexT1_sub_const_atMostTwoZeros T1.eval t1deriv t1deriv2 (Real.log c2)
    1 (natCast (2 + 2) * pi) h1lt4pi (fun x hx1 _ => ht1 x hx1)
    (fun x hx1 _ => ht1' x hx1) (fun x hx1 _ => hconvex x hx1) zeros hnd hz

/-- **Sanity check: the whole pipeline discharges on a genuine `EMLTree`, not just abstract
functions.** `T1 := eml var (const c1)` (`T1.eval x = exp(x) - log(c1)`) is convex EVERYWHERE
(`t1deriv = t1deriv2 = exp`, `exp > 0` always) — the simplest possible non-trivial convex EML
tree. NOT new residual coverage: this `T1` is unbounded above (`exp(x)→∞`), already closed by the
far easier "unbounded-T1" case in this arc — the value here is confirming
`eml_depth2_witness_of_const_gt_one_sibling_convexT1` genuinely composes end to end on a concrete
tree, mirroring every other "sanity-check corollary" in this whole arc. -/
theorem eml_var_const_c1_witness_via_convexT1 {S3 : EMLTree} {c1 c2 : Real} (hc2 : 1 < c2)
    (hsin : ∀ x, (EMLTree.eml (EMLTree.eml EMLTree.var (EMLTree.const c1))
        (EMLTree.eml (EMLTree.const c2) S3)).eval x = Real.sin x) :
    ∃ x0, 0 < S3.eval x0 := by
  have hT1eval : (EMLTree.eml EMLTree.var (EMLTree.const c1)).eval
      = fun x => Real.exp x - Real.log c1 := rfl
  have ht1 : ∀ x : Real, 1 < x →
      HasDerivAt (EMLTree.eml EMLTree.var (EMLTree.const c1)).eval (Real.exp x) x := by
    intro x _
    rw [hT1eval]
    have hsub := HasDerivAt_sub Real.exp (fun _ => Real.log c1) (Real.exp x) 0 x
      (HasDerivAt_exp x) (HasDerivAt_const (Real.log c1) x)
    have he : Real.exp x - 0 = Real.exp x := sub_zero _
    exact he ▸ hsub
  exact eml_depth2_witness_of_const_gt_one_sibling_convexT1 hc2 Real.exp Real.exp ht1
    (fun x _ => HasDerivAt_exp x) (fun x _ => Real.exp_pos x) hsin

end Real
end MachLib
