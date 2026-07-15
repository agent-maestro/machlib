import MachLib.EMLExplicitBoundSinBarrier
import MachLib.CosNotInEMLAnyDepth

/-!
# Re-routing the cos barrier off `zero_count_bound_classical`

Mirror of `EMLExplicitBoundSinBarrier.lean` for cosine. Same re-derivation via
`EMLExplicitBound.enc_combinedBound`; still depends on `eml_pfaffian_validon_from_cos_equality`
(a separate, deliberately-still-open axiom, out of scope here) plus the two small
classical-citation facts `pi_div_one_plus_one_pos`/`pi_div_one_plus_one_lt_pi` from
`CosNotInEMLAnyDepth.lean` (also out of scope — trivial facts awaiting `div_pos`-style
infrastructure, per that file's own docstring).

One structural difference from the sin barrier: cos's zeros are at `i·π + π/2` starting at
`i = 0` (giving `π/2` itself), which would collide with the natural choice of strictly-interior
left endpoint `a' = π/2` needed for `logArgPosOn_Icc_of_validOn`'s open→closed bridge. Using the
zeros `i = 1, …, M+1` instead (still `M + 1` distinct zeros, all `> π/2`) sidesteps this with no
new fact needed.
-/

namespace MachLib

open MachLib.Real
open MachLib.EMLExplicitBound
open MachLib.EMLLogArgPosBridge
open MachLib.PfaffianGeneralReduce
open MachLib.MultiPolyMod

theorem cos_not_in_eml_any_depth (k : Nat) :
    ¬ InEMLDepth (fun x : Real => Real.cos x) k := by
  intro ⟨t, _htd, hcos⟩
  have hcos' : ∀ x, t.eval x = Real.cos x := fun x => (hcos x).symm
  let p := (enc t emlEmptyChain).2
  let M := combinedBoundE (len t 0) (enc t emlEmptyChain).1 (encTags t emlEmptyChain ()) p
  have hB_pos : (0 : Real) < natCast (M + 3) * pi := natCast_mul_pi_pos (by omega)
  have hvalidon : EMLPfaffianValidOn t 0 (natCast (M + 3) * pi) :=
    eml_pfaffian_validon_from_cos_equality t hcos' (natCast (M + 3) * pi) hB_pos
  have hbb : natCast (M + 2) * pi < natCast (M + 3) * pi := natCast_mul_pi_lt (by omega)
  have hlogPos : LogArgPosOn t (Icc (pi / (1 + 1)) (natCast (M + 2) * pi)) :=
    logArgPosOn_Icc_of_validOn t 0 (natCast (M + 3) * pi) (pi / (1 + 1)) (natCast (M + 2) * pi)
      pi_div_one_plus_one_pos hbb hvalidon
  have neg_one_ne_zero : (-1 : Real) ≠ 0 :=
    ne_of_lt (neg_neg_of_pos zero_lt_one_ax)
  have e1 : natCast 1 = (1 : Real) := by
    rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero, zero_add]
  have hpi_lt_bound : pi < natCast (M + 2) * pi := by
    have h := natCast_mul_pi_lt (show 1 < M + 2 by omega)
    rwa [e1, one_mul_thm] at h
  have hab : pi / (1 + 1) < natCast (M + 2) * pi :=
    lt_trans_ax pi_div_one_plus_one_lt_pi hpi_lt_bound
  have hne : ∃ z, pi / (1 + 1) < z ∧ z < natCast (M + 2) * pi ∧
      (pfaffianChainFn (enc t emlEmptyChain).1 p).eval z ≠ 0 := by
    refine ⟨pi, pi_div_one_plus_one_lt_pi, hpi_lt_bound, ?_⟩
    show (pfaffianChainFn (enc t emlEmptyChain).1 p).eval pi ≠ 0
    rw [enc_eval t emlEmptyChain pi, hcos' pi, cos_pi]
    exact neg_one_ne_zero
  have hbound := enc_combinedBound t emlEmptyChain () (pi / (1 + 1)) (natCast (M + 2) * pi) hab
    trivial trivial (fun i _ hij => i.elim0) (fun _ _ _ i => i.elim0) (fun i => i.elim0)
    hlogPos p hne
  let zeros : List Real := (List.range (M + 1)).map (fun i => natCast (i + 1) * pi + pi / (1 + 1))
  have hzeros_len : zeros.length = M + 1 := by
    simp [zeros, List.length_map, List.length_range]
  have hzeros_valid : ∀ z ∈ zeros,
      pi / (1 + 1) < z ∧ z < natCast (M + 2) * pi ∧
        (pfaffianChainFn (enc t emlEmptyChain).1 p).eval z = 0 := by
    intro z hz
    simp only [zeros, List.mem_map, List.mem_range] at hz
    obtain ⟨i, hi_lt, hzeq⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · rw [← hzeq]
      have hpos : (0 : Real) < natCast (i + 1) * pi := natCast_mul_pi_pos (show 1 ≤ i + 1 by omega)
      have h := add_lt_add_left hpos (pi / (1 + 1))
      rw [add_zero, add_comm (pi / (1 + 1)) (natCast (i + 1) * pi)] at h
      exact h
    · rw [← hzeq]
      have step2 : natCast (i + 1) * pi + pi = natCast (i + 2) * pi := by
        have hs : natCast (i + 2) = natCast (i + 1) + 1 := natCast_succ (i + 1)
        rw [hs, mul_distrib_right, one_mul_thm]
      have step1 : natCast (i + 1) * pi + pi / (1 + 1) < natCast (i + 1) * pi + pi :=
        add_lt_add_left pi_div_one_plus_one_lt_pi (natCast (i + 1) * pi)
      rw [step2] at step1
      have step3 : natCast (i + 2) * pi ≤ natCast (M + 2) * pi := by
        by_cases heqM : i = M
        · rw [heqM]; exact le_refl _
        · exact le_of_lt (natCast_mul_pi_lt (show i + 2 < M + 2 by omega))
      exact lt_of_lt_of_le_r step1 step3
    · rw [← hzeq]
      show (pfaffianChainFn (enc t emlEmptyChain).1 p).eval
          (natCast (i + 1) * pi + pi / (1 + 1)) = 0
      rw [enc_eval t emlEmptyChain (natCast (i + 1) * pi + pi / (1 + 1)), hcos']
      exact cos_at_half_odd_pi (i + 1)
  have hzeros_nodup : zeros.Nodup := by
    have h := cos_zeros_list_nodup M
    show List.Pairwise (· ≠ ·) zeros
    show List.Pairwise (· ≠ ·)
        ((List.range (M + 1)).map (fun i => natCast (i + 1) * pi + pi / (1 + 1)))
    exact (List.nodup_range (M + 1)).map (fun i => natCast (i + 1) * pi + pi / (1 + 1))
      (fun i j (_hij_neq : i ≠ j) => by
        intro hij_eq
        dsimp only at hij_eq
        rcases Nat.lt_or_ge i j with hlt | hge
        · have hh := cos_half_odd_pi_lt (show i + 1 < j + 1 by omega)
          rw [hij_eq] at hh
          exact lt_irrefl_ax _ hh
        · have hlt2 : j < i := by omega
          have hh := cos_half_odd_pi_lt (show j + 1 < i + 1 by omega)
          rw [← hij_eq] at hh
          exact lt_irrefl_ax _ hh)
  have hlen_le : zeros.length ≤ M := hbound zeros hzeros_nodup hzeros_valid
  rw [hzeros_len] at hlen_le
  omega

end MachLib
