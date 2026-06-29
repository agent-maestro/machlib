import MachLib.FixedPoint
import MachLib.OperatorBasisGeneral

/-! # Joint-Lipschitz clamp (`clamp3`) — sound forward error when the clamp BOUNDS are rounded.

`aerr_clamp` (and the `clampO` fold node) bound `clamp v lo hi` with `lo hi : Real` taken as
EXACT reals: the error is `Ebound a` (the *value* arg only), sound precisely because the bounds
carry no rounding error. When a shipped kernel's clamp edge is a *computed* — hence rounded —
value (`clamp(x, alpha*x, hi)`, the parametric ReLU), that assumption breaks; the real-emitted-C
probe `ctarget.py` caught exactly this (the bound claimed `0` while the active edge `alpha*x`
carried `~u·|alpha*x|`).

This file proves the general bound. `clamp = min ∘ max`, and `min`/`max` are each 1-Lipschitz
in BOTH arguments, so `clamp` is JOINTLY 1-Lipschitz in `(v, lo, hi)`:

    |clamp v lo hi − clamp v' lo' hi'| ≤ |v − v'| + |lo − lo'| + |hi − hi'|.

No `lo ≤ hi` precondition is needed for the error bound (it follows structurally from min/max
being 1-Lipschitz). `aerr_clamp3` lifts it to the `AErr` certificate: a clamp whose edges each
carry their own error `Elo`/`Ehi` propagates `Ev + Elo + Ehi`. `sorryAx`-free; no new axioms.
-/

namespace MachLib.Real

private theorem le_total' (a b : Real) : a ≤ b ∨ b ≤ a := by
  rcases lt_total a b with h | h | h
  · exact Or.inl (le_of_lt h)
  · exact Or.inl (le_of_eq h)
  · exact Or.inr (le_of_lt h)

private theorem le_of_not_le' {a b : Real} (h : ¬ a ≤ b) : b ≤ a := by
  rcases le_total' a b with hab | hba
  · exact absurd hab h
  · exact hba

/-! ## second-argument directional bounds (the FixedPoint lemmas vary the FIRST arg) -/

theorem max_sub_le_abs_snd (b c d : Real) : max b c - max b d ≤ abs (c - d) := by
  by_cases hbc : b ≤ c
  · have hm : max b c = c := by unfold max; rw [if_pos hbc]
    rw [hm]; exact le_trans (sub_le_sub_left (le_max_right b d) c) (le_abs_self _)
  · have hm : max b c = b := by unfold max; rw [if_neg hbc]
    rw [hm]; exact le_trans (sub_nonpos_of_le (le_max_left b d)) (abs_nonneg _)

theorem max_sub_le_abs_snd' (b c d : Real) : max b d - max b c ≤ abs (c - d) := by
  have h := max_sub_le_abs_snd b d c
  rw [abs_sub_comm d c] at h; exact h

theorem max_lipschitz_snd (b c d : Real) : abs (max b c - max b d) ≤ abs (c - d) :=
  abs_sub_le_of (max_sub_le_abs_snd b c d) (max_sub_le_abs_snd' b c d)

theorem min_sub_le_abs_snd (b c d : Real) : min b c - min b d ≤ abs (c - d) := by
  by_cases hbc : b ≤ c
  · have hm : min b c = b := by unfold min; rw [if_pos hbc]
    rw [hm]
    by_cases hbd : b ≤ d
    · have hn : min b d = b := by unfold min; rw [if_pos hbd]
      rw [hn, show b - b = (0 : Real) from by mach_ring]; exact abs_nonneg _
    · have hn : min b d = d := by unfold min; rw [if_neg hbd]
      rw [hn]; exact le_trans (sub_le_sub_right hbc d) (le_abs_self _)
  · have hm : min b c = c := by unfold min; rw [if_neg hbc]
    rw [hm]
    by_cases hbd : b ≤ d
    · have hn : min b d = b := by unfold min; rw [if_pos hbd]
      rw [hn]; exact le_trans (sub_nonpos_of_le (le_of_not_le' hbc)) (abs_nonneg _)
    · have hn : min b d = d := by unfold min; rw [if_neg hbd]
      rw [hn]; exact le_abs_self _

theorem min_sub_le_abs_snd' (b c d : Real) : min b d - min b c ≤ abs (c - d) := by
  have h := min_sub_le_abs_snd b d c
  rw [abs_sub_comm d c] at h; exact h

theorem min_lipschitz_snd (b c d : Real) : abs (min b c - min b d) ≤ abs (c - d) :=
  abs_sub_le_of (min_sub_le_abs_snd b c d) (min_sub_le_abs_snd' b c d)

/-! ## joint (two-argument) Lipschitz for max / min, then clamp -/

theorem max_lipschitz2 (a lo b lo' : Real) :
    abs (max a lo - max b lo') ≤ abs (a - b) + abs (lo - lo') := by
  have key : max a lo - max b lo' = (max a lo - max b lo) + (max b lo - max b lo') := by
    mach_mpoly [max a lo, max b lo, max b lo']
  rw [key]
  exact le_trans (abs_add _ _) (add_le_add_both (max_lipschitz a b lo) (max_lipschitz_snd b lo lo'))

theorem min_lipschitz2 (a hi b hi' : Real) :
    abs (min a hi - min b hi') ≤ abs (a - b) + abs (hi - hi') := by
  have key : min a hi - min b hi' = (min a hi - min b hi) + (min b hi - min b hi') := by
    mach_mpoly [min a hi, min b hi, min b hi']
  rw [key]
  exact le_trans (abs_add _ _) (add_le_add_both (min_lipschitz a b hi) (min_lipschitz_snd b hi hi'))

/-- **`clamp` is jointly 1-Lipschitz** in all three arguments. -/
theorem clamp_lipschitz3 (v lo hi v' lo' hi' : Real) :
    abs (clamp v lo hi - clamp v' lo' hi')
      ≤ abs (v - v') + abs (lo - lo') + abs (hi - hi') := by
  unfold clamp
  refine le_trans (min_lipschitz2 (max v lo) hi (max v' lo') hi') ?_
  exact add_le_add_both (max_lipschitz2 v lo v' lo') (le_refl (abs (hi - hi')))

/-- **`clamp` magnitude is bounded by its edges**, unconditionally (`min ∘ max` saturates into
`[−max|lo||hi|, hi]`; no `lo ≤ hi` needed). -/
theorem clamp_abs_le (x lo hi : Real) : abs (clamp x lo hi) ≤ max (abs lo) (abs hi) := by
  apply abs_le_of
  · exact le_trans (clamp_le_hi x lo hi) (le_trans (le_abs_self hi) (le_max_right _ _))
  · unfold clamp
    by_cases hA : max x lo ≤ hi
    · have hm : min (max x lo) hi = max x lo := by unfold min; rw [if_pos hA]
      rw [hm]
      exact le_trans (neg_le_neg (le_max_right x lo))
        (le_trans (neg_le_abs lo) (le_max_left _ _))
    · have hm : min (max x lo) hi = hi := by unfold min; rw [if_neg hA]
      rw [hm]; exact le_trans (neg_le_abs hi) (le_max_right _ _)

/-- **Joint-Lipschitz clamp certificate.** Each clamp edge carries its OWN forward error
(`Elo`/`Ehi`), as a *computed* (rounded) value must; the clamp output's error is the sum
`Ev + Elo + Ehi`, magnitude `max Mlo Mhi`. This is `aerr_clamp` without the exact-bounds
assumption — the bound that soundly covers `clamp(x, alpha*x, hi)`. -/
theorem aerr_clamp3 {Mv Ev v ve Mlo Elo lo loe Mhi Ehi hi hie : Real}
    (hv : AErr Mv Ev v ve) (hlo : AErr Mlo Elo lo loe) (hhi : AErr Mhi Ehi hi hie) :
    AErr (max Mlo Mhi) (Ev + Elo + Ehi) (clamp v lo hi) (clamp ve loe hie) := by
  refine ⟨?_, ?_⟩
  · refine le_trans (clamp_abs_le ve loe hie) ?_
    exact max_le (le_trans hlo.1 (le_max_left Mlo Mhi))
                 (le_trans hhi.1 (le_max_right Mlo Mhi))
  · refine le_trans (clamp_lipschitz3 v lo hi ve loe hie) ?_
    exact add_le_add_both (add_le_add_both hv.2 hlo.2) hhi.2

end MachLib.Real
