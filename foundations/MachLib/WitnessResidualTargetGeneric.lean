import MachLib.WitnessResidualChainSkeleton
import MachLib.SinNotInEMLDepth2Sweep
import MachLib.OperatorBasisComplete

/-!
# The zero-counting argument, generalized over the target — and one nesting level pushed through

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). The 2026-07-20 finding
that `EMLWitnesses A x0`/`EMLWitnesses B x0` and the deferred `c2 ≥ 2` case are the SAME
difficulty (both bottom out in "does a finite tree equal a `log(log(...))`-nested target") means
neither closes without a proof that works for the WHOLE nested-target family, not just
`log(c2+sin x)`. This file takes that at face value: `T1_not_eq_log_c2_plus_sin_given_validon`
(`WitnessResidualChainSkeleton.lean`) is almost entirely target-agnostic already — reading it
closely, the ONLY places `log(c2+sin x)` specifically enters are (a) the value each node takes
at every `kπ` (`log(c2+sin(kπ)) = log(c2)`, constant, via `sin(kπ)=0`) and (b) a witness that the
target DIFFERS from that constant somewhere (`log(c2+sin(π+1)) ≠ log(c2)`, via `sin(π+1)≠0`). The
`M+1`-zeros-exceed-`M` machinery in between never touches the target's specific shape.

**What's here:**

1. `no_tree_eq_target_given_validon` — the SAME proof as
   `T1_not_eq_log_c2_plus_sin_given_validon`, with `log(c2+sin x)` replaced by an abstract
   `TARGET : Real → Real` and `log c2` replaced by an abstract level `L`, taking exactly the two
   facts described above as hypotheses (`hTargetKPi`, `hTargetPi1`) instead of deriving them
   from `sin`'s specific algebra. `EMLPfaffianValidOn T1` is STILL taken as an explicit
   hypothesis, unchanged from the chain-skeleton file — this does not touch the genuinely open
   induction, only removes the target-specific hardcoding around it.
2. `T1_not_eq_nested_log_given_validon` — the abstraction actually used once, one level deeper
   than before: `TARGET(x) = log(d + log(c2+sin x))` (the exact shape identified in the
   2026-07-20 rescoping entry as what `A` would have to equal in the "`B` a large constant"
   escape route). Proving `hTargetKPi`/`hTargetPi1` for this target needs one new ingredient not
   used at the `log(c2+sin x)` level — `log_injective_pos` (`c2+sin(π+1) ≠ c2` only refutes
   `log(c2+sin(π+1)) ≠ log(c2)` if `log` is known injective on the relevant positive arguments;
   the un-nested proof avoided this by working with `exp`/`log` composed the OTHER way round).
   Confirms the abstraction genuinely reaches the next level, not just restates the old result
   with renamed variables.

**What this still does NOT do**: discharge `hvalidon_any_b` for either instantiation, or turn
this into an actual induction over arbitrarily many nesting levels (that needs a formal
definition of the nested-target family and induction on its depth, not attempted here). One
level, concretely verified, is the honest scope of this pass.
-/

namespace MachLib

open MachLib.Real
open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

/-- **The zero-counting argument, with the target abstracted out.** Identical proof shape to
`T1_not_eq_log_c2_plus_sin_given_validon`, but `log(c2+sin x)` is replaced by an arbitrary
`TARGET`, and the two facts that proof derived from `sin`'s own algebra (`TARGET(kπ) = L` for
every `k ≥ 1`, `TARGET(π+1) ≠ L`) are taken as hypotheses instead. `EMLPfaffianValidOn T1` is
still an explicit, undischarged hypothesis — this isolates the target-shift argument itself from
both the still-open induction AND from `sin`-specific hardcoding. -/
theorem no_tree_eq_target_given_validon
    (TARGET : Real → Real) (L : Real)
    (hTargetKPi : ∀ k : Nat, 1 ≤ k → TARGET (natCast k * pi) = L)
    (hTargetPi1 : TARGET (pi + 1) ≠ L)
    (T1 : EMLTree)
    (hT1eq : ∀ x, T1.eval x = TARGET x)
    (hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b) :
    False := by
  let p := (enc T1 emlEmptyChain).2
  let p' := MultiPoly.sub p (MultiPoly.const L)
  let M := combinedBoundE (len T1 0) (enc T1 emlEmptyChain).1 (encTags T1 emlEmptyChain ()) p'
  have hB_pos : (0 : Real) < natCast (M + 3) * pi := natCast_mul_pi_pos (by omega)
  have hvalidon : EMLPfaffianValidOn T1 0 (natCast (M + 3) * pi) :=
    hvalidon_any_b (natCast (M + 3) * pi) hB_pos
  have hbb : natCast (M + 2) * pi < natCast (M + 3) * pi := natCast_mul_pi_lt (by omega)
  have hlogPos : LogArgPosOn T1 (Icc 1 (natCast (M + 2) * pi)) :=
    logArgPosOn_Icc_of_validOn T1 0 (natCast (M + 3) * pi) 1 (natCast (M + 2) * pi)
      zero_lt_one_ax hbb hvalidon
  have h2pi : natCast 2 * pi = pi + pi := by
    have e2 : natCast 2 = natCast 1 + 1 := natCast_succ 1
    have e1 : natCast 1 = (1 : Real) := by
      rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
    rw [e2, e1, mul_distrib_right, one_mul_thm]
  have hpi1lt2pi : pi + 1 < natCast (M + 2) * pi := by
    by_cases hM : M = 0
    · rw [hM, h2pi]; exact add_lt_add_left pi_gt_one pi
    · have hgt : 2 < M + 2 := by omega
      have hlt := natCast_mul_pi_lt hgt
      rw [h2pi] at hlt
      exact lt_trans_ax (add_lt_add_left pi_gt_one pi) hlt
  have h1ltpi1 : (1 : Real) < pi + 1 := by
    have h := add_lt_add_left pi_pos 1
    rw [add_zero, add_comm 1 pi] at h
    exact h
  have hab : (1 : Real) < natCast (M + 2) * pi := lt_trans_ax h1ltpi1 hpi1lt2pi
  have hT1ne : T1.eval (pi + 1) ≠ L := by rw [hT1eq]; exact hTargetPi1
  have hne : ∃ z, (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧
      (pfaffianChainFn (enc T1 emlEmptyChain).1 p').eval z ≠ 0 := by
    refine ⟨pi + 1, h1ltpi1, hpi1lt2pi, ?_⟩
    show MultiPoly.eval p' (pi + 1) ((enc T1 emlEmptyChain).1.chainValues (pi + 1)) ≠ 0
    show MultiPoly.eval p (pi + 1) ((enc T1 emlEmptyChain).1.chainValues (pi + 1)) - L ≠ 0
    have heval : MultiPoly.eval p (pi + 1) ((enc T1 emlEmptyChain).1.chainValues (pi + 1))
        = T1.eval (pi + 1) := enc_eval T1 emlEmptyChain (pi + 1)
    rw [heval]
    intro hz
    have e : T1.eval (pi + 1) = (T1.eval (pi + 1) - L) + L := by mach_ring
    rw [hz] at e
    have e2 : (0 : Real) + L = L := by mach_ring
    rw [e2] at e
    exact hT1ne e
  have hbound := enc_combinedBound T1 emlEmptyChain () 1 (natCast (M + 2) * pi) hab
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p' hne
  let zeros : List Real := (List.range (M + 1)).map (fun i => natCast (i + 1) * pi)
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧
        (pfaffianChainFn (enc T1 emlEmptyChain).1 p').eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
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
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact h1lt (i + 1) (by omega)
    · rw [← hzeq]; exact natCast_mul_pi_lt (by omega)
    · rw [← hzeq]
      show MultiPoly.eval p' (natCast (i + 1) * pi)
          ((enc T1 emlEmptyChain).1.chainValues (natCast (i + 1) * pi)) = 0
      show MultiPoly.eval p (natCast (i + 1) * pi)
          ((enc T1 emlEmptyChain).1.chainValues (natCast (i + 1) * pi)) - L = 0
      have heval : MultiPoly.eval p (natCast (i + 1) * pi)
          ((enc T1 emlEmptyChain).1.chainValues (natCast (i + 1) * pi))
          = T1.eval (natCast (i + 1) * pi) := enc_eval T1 emlEmptyChain (natCast (i + 1) * pi)
      rw [heval, hT1eq, hTargetKPi (i + 1) (by omega)]
      mach_ring
  have hzeros_nodup : zeros.Nodup := sin_zeros_list_nodup M
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

/-- **One nesting level deeper, concretely.** `TARGET(x) = log(d + log(c2+sin x))` — exactly the
target `A` would need to equal in the "`B` a large constant" escape route flagged in the
2026-07-20 decision-doc entry (there, `d = log b` for the specific `b` chosen). `hdc2` says the
outer `log`'s argument never goes non-positive (`d + log(c2-1)`, the minimum of
`d + log(c2+sin x)` over all `x`, stays `> 0`) — without it the target isn't even a genuine
`log(log(...))` composition (it would clamp somewhere, collapsing to a different, easier shape).
No finite tree can equal this target and have `EMLPfaffianValidOn` throughout, by the same
zero-counting argument as the un-nested case. -/
theorem T1_not_eq_nested_log_given_validon
    (c2 d : Real) (hc2 : 1 < c2) (hdc2 : 0 < d + Real.log (c2 - 1)) (T1 : EMLTree)
    (hT1eq : ∀ x, T1.eval x = Real.log (d + Real.log (c2 + Real.sin x)))
    (hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b) :
    False := by
  have hc2pos : (0 : Real) < c2 := lt_trans_ax zero_lt_one_ax hc2
  have hc2m1_pos : (0 : Real) < c2 - 1 := by
    have h01 : (0 : Real) + 1 = 1 := by mach_ring
    exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  have hsinpi1 : Real.sin (pi + 1) ≠ 0 := by
    have heq : Real.sin (pi + 1) = Real.cos pi * Real.sin 1 := by
      rw [Real.sin_add, Real.sin_pi, zero_mul, zero_add]
    have hneg : Real.cos pi * Real.sin 1 < 0 := by
      rw [Real.cos_pi]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos zero_lt_one_ax) Real.sin_one_pos
    rw [heq]; exact ne_of_lt hneg
  have hsin_ge : (-1 : Real) ≤ Real.sin (pi + 1) := neg_one_le_sin (pi + 1)
  have hpos : (0 : Real) < c2 + Real.sin (pi + 1) := by
    rcases (le_iff_lt_or_eq _ _).mp hsin_ge with h | h
    · have hstep := add_lt_add hc2 h
      have e : (1 : Real) + (-1) = 0 := by mach_ring
      rwa [e] at hstep
    · rw [← h]
      have e : c2 + (-1) = c2 - 1 := by mach_ring
      rw [e]; exact hc2m1_pos
  -- `log(c2+sin(pi+1)) ≥ log(c2-1)`: the outer log's argument never clamps at pi+1 either.
  have hcm1_le : c2 - 1 ≤ c2 + Real.sin (pi + 1) := by
    have h := add_le_add_left hsin_ge c2
    have e1 : c2 + (-1) = c2 - 1 := by mach_ring
    rwa [e1] at h
  have hlog_ge_pi1 : Real.log (c2 - 1) ≤ Real.log (c2 + Real.sin (pi + 1)) :=
    log_mono hc2m1_pos hcm1_le
  have hd_pos_pi1 : (0 : Real) < d + Real.log (c2 + Real.sin (pi + 1)) :=
    lt_of_lt_of_le hdc2 (add_le_add_left hlog_ge_pi1 d)
  -- `log(c2) ≥ log(c2-1)` similarly, so `d + log c2` doesn't clamp either.
  have hcm1_le_c2 : c2 - 1 ≤ c2 := sub_le_self (le_of_lt zero_lt_one_ax)
  have hlog_ge_c2 : Real.log (c2 - 1) ≤ Real.log c2 := log_mono hc2m1_pos hcm1_le_c2
  have hd_pos_c2 : (0 : Real) < d + Real.log c2 :=
    lt_of_lt_of_le hdc2 (add_le_add_left hlog_ge_c2 d)
  have hTargetKPi : ∀ k : Nat, 1 ≤ k →
      Real.log (d + Real.log (c2 + Real.sin (natCast k * pi))) = Real.log (d + Real.log c2) := by
    intro k hk
    rw [sin_natCast_mul_pi k]
    have e : c2 + 0 = c2 := by mach_ring
    rw [e]
  have hTargetPi1 :
      Real.log (d + Real.log (c2 + Real.sin (pi + 1))) ≠ Real.log (d + Real.log c2) := by
    intro hcontra
    have hstep1 : d + Real.log (c2 + Real.sin (pi + 1)) = d + Real.log c2 :=
      log_injective_pos hd_pos_pi1 hd_pos_c2 hcontra
    have hstep2 : Real.log (c2 + Real.sin (pi + 1)) = Real.log c2 := by
      have e : Real.log (c2 + Real.sin (pi + 1))
          = (d + Real.log (c2 + Real.sin (pi + 1))) - d := by mach_ring
      have e2 : Real.log c2 = (d + Real.log c2) - d := by mach_ring
      rw [e, e2, hstep1]
    have hstep3 : c2 + Real.sin (pi + 1) = c2 := log_injective_pos hpos hc2pos hstep2
    have hsin0 : Real.sin (pi + 1) = 0 := by
      have e : Real.sin (pi + 1) = (c2 + Real.sin (pi + 1)) - c2 := by mach_ring
      rw [e, hstep3]; mach_ring
    exact hsinpi1 hsin0
  exact no_tree_eq_target_given_validon
    (fun x => Real.log (d + Real.log (c2 + Real.sin x))) (Real.log (d + Real.log c2))
    hTargetKPi hTargetPi1 T1 hT1eq hvalidon_any_b

end MachLib
