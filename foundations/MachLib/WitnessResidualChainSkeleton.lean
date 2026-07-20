import MachLib.EMLExplicitBoundSinBarrier
import MachLib.WitnessResidualDepth1

/-!
# Threading `T1`'s own chain through `enc_combinedBound` — the shape, isolated from the induction

Part of the 2026-07-19/20 continuation of Option D
(`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Mirrors `sin_not_in_eml_any_depth`'s exact
proof shape (`EMLExplicitBoundSinBarrier.lean`), but for an ARBITRARY tree `T1` satisfying the
shifted target `T1.eval x = log(c2 + sin x)` instead of `sin` itself, using the target-shift
trick (shift `combinedBoundE`'s polynomial by `log(c2)` instead of `0`; `sin(kπ)=0` still gives
`log(c2+sin(kπ))=log(c2)` at every integer `k`, uniformly in `c2`).

**What this file isolates, deliberately**: `T1`'s own `EMLPfaffianValidOn` — the piece that
needs a genuine strong induction, not yet built — is taken here as an EXPLICIT HYPOTHESIS
(`hvalidon_any_b`), not derived. The point: verify the REST of the argument (the encoder/chain
plumbing — `enc T1 emlEmptyChain`, the shifted `MultiPoly`, `combinedBoundE`, the
`M+1`-zeros-exceed-`M` contradiction) actually closes, GIVEN that one hypothesis — checking the
architecture is sound before attacking the hard piece.
-/

namespace MachLib

open MachLib.Real
open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

theorem T1_not_eq_log_c2_plus_sin_given_validon
    (c2 : Real) (hc2 : 1 < c2) (T1 : EMLTree)
    (hT1eq : ∀ x, T1.eval x = Real.log (c2 + Real.sin x))
    (hvalidon_any_b : ∀ b : Real, 0 < b → EMLPfaffianValidOn T1 0 b) :
    False := by
  let p := (enc T1 emlEmptyChain).2
  let p' := MultiPoly.sub p (MultiPoly.const (Real.log c2))
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
  -- sin(pi+1) != 0 -- reused verbatim from sin_not_in_eml_any_depth's own proof.
  have hsinpi1 : Real.sin (pi + 1) ≠ 0 := by
    have heq : Real.sin (pi + 1) = Real.cos pi * Real.sin 1 := by
      rw [Real.sin_add, Real.sin_pi, zero_mul, zero_add]
    have hneg : Real.cos pi * Real.sin 1 < 0 := by
      rw [Real.cos_pi]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos zero_lt_one_ax) Real.sin_one_pos
    rw [heq]; exact ne_of_lt hneg
  have hc2pos : (0 : Real) < c2 := lt_trans_ax zero_lt_one_ax hc2
  have hsin_ge : (-1 : Real) ≤ Real.sin (pi + 1) := neg_one_le_sin (pi + 1)
  have hpos : (0 : Real) < c2 + Real.sin (pi + 1) := by
    rcases (le_iff_lt_or_eq _ _).mp hsin_ge with h | h
    · have hstep := add_lt_add hc2 h
      have e : (1 : Real) + (-1) = 0 := by mach_ring
      rwa [e] at hstep
    · rw [← h]
      have e : c2 + (-1) = c2 - 1 := by mach_ring
      rw [e]
      have h01 : (0 : Real) + 1 = 1 := by mach_ring
      exact lt_sub_of_add_lt (by rw [h01]; exact hc2)
  -- T1.eval(pi+1) != log(c2): if equal, exp both sides forces sin(pi+1)=0, contradiction.
  have hT1ne : T1.eval (pi + 1) ≠ Real.log c2 := by
    rw [hT1eq]
    intro hcontra
    have h1 : Real.exp (Real.log (c2 + Real.sin (pi + 1))) = Real.exp (Real.log c2) := by
      rw [hcontra]
    rw [Real.exp_log hpos, Real.exp_log hc2pos] at h1
    have hsin0 : Real.sin (pi + 1) = 0 := by
      have e : Real.sin (pi + 1) = (c2 + Real.sin (pi + 1)) - c2 := by mach_ring
      rw [e, h1]; mach_ring
    exact hsinpi1 hsin0
  have hne : ∃ z, (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧
      (pfaffianChainFn (enc T1 emlEmptyChain).1 p').eval z ≠ 0 := by
    refine ⟨pi + 1, h1ltpi1, hpi1lt2pi, ?_⟩
    show MultiPoly.eval p' (pi + 1) ((enc T1 emlEmptyChain).1.chainValues (pi + 1)) ≠ 0
    show MultiPoly.eval p (pi + 1) ((enc T1 emlEmptyChain).1.chainValues (pi + 1))
        - Real.log c2 ≠ 0
    have heval : MultiPoly.eval p (pi + 1) ((enc T1 emlEmptyChain).1.chainValues (pi + 1))
        = T1.eval (pi + 1) := enc_eval T1 emlEmptyChain (pi + 1)
    rw [heval]
    intro hz
    have e : T1.eval (pi + 1) = (T1.eval (pi + 1) - Real.log c2) + Real.log c2 := by mach_ring
    rw [hz] at e
    have e2 : (0 : Real) + Real.log c2 = Real.log c2 := by mach_ring
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
          ((enc T1 emlEmptyChain).1.chainValues (natCast (i + 1) * pi))
          - Real.log c2 = 0
      have heval : MultiPoly.eval p (natCast (i + 1) * pi)
          ((enc T1 emlEmptyChain).1.chainValues (natCast (i + 1) * pi))
          = T1.eval (natCast (i + 1) * pi) := enc_eval T1 emlEmptyChain (natCast (i + 1) * pi)
      rw [heval, hT1eq, sin_natCast_mul_pi (i + 1)]
      have e : c2 + 0 = c2 := by mach_ring
      rw [e]
      mach_ring
  have hzeros_nodup : zeros.Nodup := sin_zeros_list_nodup M
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end MachLib
