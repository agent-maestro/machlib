import MachLib.EMLExplicitBoundEncoder
import MachLib.EMLBarrierBound
import MachLib.EMLLogArgPosBridge
import MachLib.EMLPfaffian

/-!
# Re-routing the sin barrier off `zero_count_bound_classical`

`sin_not_in_eml_any_depth` (`EMLPfaffian.lean`) currently applies `PfaffianFunction.zero_bound`
to `eml_pfaffian t` — which cites the axiom `zero_count_bound_classical` (documented there as
"NOT LOAD-BEARING... the only transitive consumers are the legacy general bridge `eml_pfaffian`
and `PfaffianFunction.zero_bound`"). This file re-derives the same theorem using
`EMLExplicitBound.enc_combinedBound` instead — the fully constructive, axiom-free bound built this
session — closing AXIOM_AUDIT_V2.md §2c(2)'s last piece.

Still depends on `eml_pfaffian_validon_from_sin_equality` — a SEPARATE, deliberately-still-open
axiom (the "sin is smooth ⇒ log-arguments stay positive" analytic argument), out of scope here; see
its own docstring for the closure plan. This file only removes the Khovanskii-bound axiom.
-/

namespace MachLib

open MachLib.Real
open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

theorem sin_not_in_eml_any_depth (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.sin x) k := by
  intro ⟨t, _htd, hsin⟩
  have hsin' : ∀ x, t.eval x = Real.sin x := fun x => (hsin x).symm
  let p := (enc t emlEmptyChain).2
  let M := combinedBoundE (len t 0) (enc t emlEmptyChain).1 (encTags t emlEmptyChain ()) p
  have hB_pos : (0 : Real) < natCast (M + 3) * pi := natCast_mul_pi_pos (by omega)
  have hvalidon : EMLPfaffianValidOn t 0 (natCast (M + 3) * pi) :=
    eml_pfaffian_validon_from_sin_equality t hsin' (natCast (M + 3) * pi) hB_pos
  have hbb : natCast (M + 2) * pi < natCast (M + 3) * pi := natCast_mul_pi_lt (by omega)
  have hlogPos : LogArgPosOn t (Icc 1 (natCast (M + 2) * pi)) :=
    logArgPosOn_Icc_of_validOn t 0 (natCast (M + 3) * pi) 1 (natCast (M + 2) * pi)
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
  have hsinpi1 : Real.sin (pi + 1) ≠ 0 := by
    have heq : Real.sin (pi + 1) = Real.cos pi * Real.sin 1 := by
      rw [sin_add, sin_pi, zero_mul, zero_add]
    have hneg : Real.cos pi * Real.sin 1 < 0 := by
      rw [cos_pi]
      exact mul_neg_of_neg_of_pos (neg_neg_of_pos zero_lt_one_ax) sin_one_pos
    rw [heq]
    exact ne_of_lt hneg
  have hne : ∃ z, (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧
      (pfaffianChainFn (enc t emlEmptyChain).1 p).eval z ≠ 0 := by
    refine ⟨pi + 1, h1ltpi1, hpi1lt2pi, ?_⟩
    show (pfaffianChainFn (enc t emlEmptyChain).1 p).eval (pi + 1) ≠ 0
    rw [enc_eval t emlEmptyChain (pi + 1), hsin' (pi + 1)]
    exact hsinpi1
  have hbound := enc_combinedBound t emlEmptyChain () 1 (natCast (M + 2) * pi) hab
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p hne
  have e1 : natCast 1 = (1 : Real) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
  have h1lt : ∀ j : Nat, 1 ≤ j → (1 : Real) < natCast j * pi := by
    intro j hj1
    by_cases hj1' : j = 1
    · rw [hj1', e1, one_mul_thm]; exact pi_gt_one
    · have hgt : 1 < j := by omega
      have h_chain := natCast_mul_pi_lt hgt
      rw [e1, one_mul_thm] at h_chain
      exact lt_trans_ax pi_gt_one h_chain
  let zeros : List Real := (List.range (M + 1)).map (fun i => natCast (i + 1) * pi)
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      (1 : Real) < z ∧ z < natCast (M + 2) * pi ∧
        (pfaffianChainFn (enc t emlEmptyChain).1 p).eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]; exact h1lt (i + 1) (by omega)
    · rw [← hzeq]; exact natCast_mul_pi_lt (by omega)
    · rw [← hzeq]
      show (pfaffianChainFn (enc t emlEmptyChain).1 p).eval (natCast (i + 1) * pi) = 0
      rw [enc_eval t emlEmptyChain (natCast (i + 1) * pi), hsin' (natCast (i + 1) * pi)]
      exact sin_natCast_mul_pi (i + 1)
  have hzeros_nodup : zeros.Nodup := sin_zeros_list_nodup M
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end MachLib
