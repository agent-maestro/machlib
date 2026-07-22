import MachLib.LogImplicitRepresentability
import MachLib.WitnessResidualNestedTargetTailSign
import MachLib.Forge
import MachLib.FPModel

/-!
# C6: quantitative non-approximation — no tree gets `ε`-close to `sin`, eventually, for any `ε < 1`

Track C, item C6. The muses' proposal framed this as "upgrade exact-equality impossibilities to
`ε`-closeness impossibilities... for intervals long relative to the depth-`d` zero bound" — phrased
in terms of the OLDER zero-counting/Khovanskii mechanism. Checked directly: `TailSign` (this
session's own mechanism) gives something STRONGER for free, with no interval-length bookkeeping at
all. `eml_tailSign_unconditional` says every tree's value eventually settles into exactly one of
three behaviors (eventually positive, eventually negative, eventually exactly zero) — past SOME
threshold, forever. `sin` never settles: it keeps returning to `1` and to `-1`, exactly, past ANY
threshold (2π-periodicity + the existing `nestedTarget cs = []` specialization of
`nestedTarget_at_pi_div_two`/`nestedTarget_at_neg_pi_div_two`, `WitnessResidualNestedTargetTailSign.
lean`/`WitnessResidualNestedTargetBWitness.lean`). Any FIXED sign-definite (or zero-definite)
eventual behavior is farther than `ε < 1` from at least one of `sin`'s own recurring extremes — so
`ε`-closeness fails not just on long intervals, but for ALL sufficiently large `x`, unconditionally.
No new machinery beyond what cont. 58-71 already built; this is a direct corollary.
-/

namespace MachLib
namespace Real

open MachLib

private theorem pi_div_two_pos : (0 : Real) < pi / (1 + 1) := by
  have h11 : (0 : Real) < 1 + 1 := by
    have h := add_lt_add_left zero_lt_one_ax 1
    rw [add_zero] at h
    exact lt_trans_ax zero_lt_one_ax h
  exact div_pos_of_pos_pos pi_pos h11

/-- `sin` recurs to exactly `1`, past any threshold. Specializes the already-proven
`nestedTarget_add_natCast_mul_two_pi`/`nestedTarget_at_pi_div_two` at `cs := []`
(`nestedTarget [] = Real.sin`, definitionally — `.trans` closes the goal via defeq, no `show`
needed). -/
private theorem sin_one_recurring (M : Real) : ∃ x : Real, M < x ∧ Real.sin x = 1 := by
  obtain ⟨n, hn⟩ := archimedean M
  have h1 : natCast n ≤ natCast n * ((1 + 1) * pi) := natCast_le_natCast_mul_two_pi n
  have h2 : M < natCast n * ((1 + 1) * pi) := lt_of_lt_of_le hn h1
  refine ⟨pi / (1 + 1) + natCast n * ((1 + 1) * pi), ?_, ?_⟩
  · have h3 := add_lt_add_left pi_div_two_pos (natCast n * ((1 + 1) * pi))
    rw [add_zero, add_comm (natCast n * ((1 + 1) * pi)) (pi / (1 + 1))] at h3
    exact lt_trans_ax h2 h3
  · exact (nestedTarget_add_natCast_mul_two_pi ([] : List Real) (pi / (1 + 1)) n).trans
      (nestedTarget_at_pi_div_two ([] : List Real) trivial)

/-- `sin` recurs to exactly `-1`, past any threshold. Mirror of `sin_one_recurring`. -/
private theorem sin_neg_one_recurring (M : Real) : ∃ x : Real, M < x ∧ Real.sin x = -1 := by
  obtain ⟨n, hn⟩ := archimedean (M + pi / (1 + 1))
  have h1 : natCast n ≤ natCast n * ((1 + 1) * pi) := natCast_le_natCast_mul_two_pi n
  have h2 : M + pi / (1 + 1) < natCast n * ((1 + 1) * pi) := lt_of_lt_of_le hn h1
  refine ⟨-(pi / (1 + 1)) + natCast n * ((1 + 1) * pi), ?_, ?_⟩
  · have h3 := add_lt_add_left h2 (-(pi / (1 + 1)))
    have e1 : -(pi / (1 + 1)) + (M + pi / (1 + 1)) = M := by mach_ring
    rwa [e1] at h3
  · exact (nestedTarget_add_natCast_mul_two_pi ([] : List Real) (-(pi / (1 + 1))) n).trans
      (nestedTarget_at_neg_pi_div_two ([] : List Real) trivial)

/-- **No finite EML tree stays within `ε` of `sin` for ALL sufficiently large `x`, for any
`ε < 1`.** Strictly stronger than a bounded-interval statement: no threshold `R` past which
closeness holds, full stop. `TailSign` pins `T.eval` to one fixed regime past some `R1`;
`sin`'s recurring exact `±1` past ANY threshold (including past `max R R1`) lands at least `1`
away from `T.eval`'s regime, exceeding `ε`. -/
theorem no_tree_eps_close_to_sin_eventually (T : EMLTree) (ε : Real) (hε : ε < 1)
    (R : Real) (hclose : ∀ x : Real, R < x → abs (T.eval x - Real.sin x) < ε) : False := by
  rcases eml_tailSign_unconditional T with ⟨R1, hR1⟩ | ⟨R1, hR1⟩ | ⟨R1, hR1⟩
  · -- T eventually positive: sin hits -1 past max(R,R1); T x + 1 < ε while T x + 1 > 1.
    obtain ⟨M, hMR, hMR1⟩ := lt_of_lt_both R R1
    obtain ⟨x, hxM, hsinx⟩ := sin_neg_one_recurring M
    have hTpos : 0 < T.eval x := hR1 x (lt_trans_ax hMR1 hxM)
    have hlt1 : T.eval x - Real.sin x < ε := lt_of_abs_lt (hclose x (lt_trans_ax hMR hxM))
    rw [hsinx] at hlt1
    have e : T.eval x - (-1 : Real) = T.eval x + 1 := by mach_ring
    rw [e] at hlt1
    have hgt1 : (1 : Real) < T.eval x + 1 := by
      have h := add_lt_add_left hTpos 1
      rwa [add_zero, add_comm 1 (T.eval x)] at h
    exact lt_irrefl_ax ε (lt_trans_ax hε (lt_trans_ax hgt1 hlt1))
  · -- T eventually negative: sin hits 1 past max(R,R1); 1 - T x < ε while 1 - T x > 1.
    obtain ⟨M, hMR, hMR1⟩ := lt_of_lt_both R R1
    obtain ⟨x, hxM, hsinx⟩ := sin_one_recurring M
    have hTneg : T.eval x < 0 := hR1 x (lt_trans_ax hMR1 hxM)
    have habs2 : abs (Real.sin x - T.eval x) < ε := by
      rw [show Real.sin x - T.eval x = -(T.eval x - Real.sin x) from by mach_ring, abs_neg]
      exact hclose x (lt_trans_ax hMR hxM)
    have hlt1 : Real.sin x - T.eval x < ε := lt_of_abs_lt habs2
    rw [hsinx] at hlt1
    have hgt1 : (1 : Real) < 1 - T.eval x := by
      have hneg : (0 : Real) < -T.eval x := by
        have hh := add_lt_add_left hTneg (-T.eval x)
        rwa [add_zero, neg_add_self] at hh
      have h := add_lt_add_left hneg 1
      rw [add_zero] at h
      have e : (1 : Real) - T.eval x = 1 + -T.eval x := by mach_ring
      rwa [e]
    exact lt_irrefl_ax ε (lt_trans_ax hε (lt_trans_ax hgt1 hlt1))
  · -- T eventually exactly zero: sin hits 1 past max(R,R1); 1 - 0 = 1, but < ε < 1.
    obtain ⟨M, hMR, hMR1⟩ := lt_of_lt_both R R1
    obtain ⟨x, hxM, hsinx⟩ := sin_one_recurring M
    have hTzero : T.eval x = 0 := hR1 x (lt_trans_ax hMR1 hxM)
    have habs2 : abs (Real.sin x - T.eval x) < ε := by
      rw [show Real.sin x - T.eval x = -(T.eval x - Real.sin x) from by mach_ring, abs_neg]
      exact hclose x (lt_trans_ax hMR hxM)
    have hlt1 : Real.sin x - T.eval x < ε := lt_of_abs_lt habs2
    rw [hsinx, hTzero, sub_zero] at hlt1
    exact lt_irrefl_ax ε (lt_trans_ax hε hlt1)

end Real
end MachLib
