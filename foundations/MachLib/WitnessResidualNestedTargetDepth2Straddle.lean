import MachLib.WitnessResidualNestedTargetTailSign
import MachLib.WitnessResidualNonMonotonic

/-!
# A reusable straddle criterion, one nesting level at a time — and a genuine depth-2 instance

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 60 resolved the
`cs = [c2]` straddle boundary exactly but left deeper nestings (`cs = [d, c2]` and beyond)
unchecked against the sharpened condition (`nestedLo cs ≤ 0 < nestedHi cs`). Rather than hand-check
one more concrete level (what cont. 57-60 each did once already), this file extracts the REUSABLE
step: given `cs'`'s own range bounds `nestedLo cs'`/`nestedHi cs'` (known regardless of whether
`cs'` itself straddles), what window must a new outer shift `c` land in for `c :: cs'` to straddle?

**`nestedTarget_cons_straddle`.** Given `nestedWF (c :: cs')` (so `c + nestedLo cs' > 0`, the log
argument is positive), straddling at this level reduces to pure arithmetic on the shift: `nestedLo
(c :: cs') ≤ 0` iff `c + nestedLo cs' ≤ 1`, and `0 < nestedHi (c :: cs')` iff `1 < c + nestedHi
cs'` (`log` is monotone/order-reflecting around its zero at `1`). This is independent of whether
`cs'` itself straddles — the window is defined purely by `cs'`'s OWN bounds, at ANY depth, so this
lemma applies at every nesting level, not just depth 2.

**Concrete instance, chosen to avoid needing any numeric bound beyond what's already proven.**
`cs' = [1 + 1]` (i.e. `c2 = 2`, the EXACT boundary cont. 60 found — `nestedLo [2] = log(1) = 0`,
touching zero but not crossing it) with outer shift `d = 1`. The window check becomes `1 + 0 ≤ 1`
(trivial) and `1 < 1 + nestedHi [2] = 1 + log 3` (reduces to `0 < log 3`, already established
unconditionally for `c2 > 1` in cont. 60). No fresh numeric bound on `log` needed at all — picking
`c2 = 2` exactly (rather than some other value in `(1, 2]`) was deliberate, since it makes `nestedLo
[c2] = 0` exactly, collapsing the window check to arithmetic instead of needing to bound `log(c2-1)`
away from `-1`.

**Payoff.** `no_tree_eq_log_one_plus_log_two_plus_sin_unconditional` — no finite EML tree's `eval`
equals `log(1 + log(2 + sin x))`, unconditionally. This is a genuine depth-2 nested target
(`WitnessResidualTargetGeneric.lean` flagged `log(d + log(c2 + sin x))` as exactly the shape `A`
would have to realize in the "`B` a large constant" escape route from the 2026-07-20 rescoping
finding) — the first instance of the family closed at this depth by the unconditional TailSign
route, not just the hand-derived `EMLPfaffianValidOn`-conditional version from
`WitnessResidualTargetGeneric.lean`.

**Honest scope.** One concrete depth-2 point, chosen for a clean proof rather than being
representative of the whole `(d, c2)` window `nestedTarget_cons_straddle` characterizes. Whether
the general theorem reaches useful instances at depth 3+ has not been checked.
-/

namespace MachLib
namespace Real

/-- **The straddle window for one more nesting level, purely in terms of the inner list's own
range bounds.** Reusable at ANY depth — does not require `cs'` itself to straddle. -/
theorem nestedTarget_cons_straddle (c : Real) (cs' : List Real) (hwf : nestedWF (c :: cs'))
    (hc_le : c + nestedLo cs' ≤ 1) (hc_gt : 1 < c + nestedHi cs') :
    nestedLo (c :: cs') ≤ 0 ∧ 0 < nestedHi (c :: cs') := by
  obtain ⟨hwf_c, _⟩ := hwf
  refine ⟨?_, ?_⟩
  · rw [nestedLo_cons, ← log_one]
    exact log_mono hwf_c hc_le
  · rw [nestedHi_cons, ← log_one]
    exact log_lt_log zero_lt_one_ax hc_gt

/-- **A genuine depth-2 instance, closed unconditionally.** `cs = [1, 2]`, i.e.
`nestedTarget [1, 1+1] x = log(1 + log((1+1) + sin x)) = log(1 + log(2 + sin x))`. -/
theorem no_tree_eq_log_one_plus_log_two_plus_sin_unconditional
    (T : EMLTree)
    (heq : ∀ x : Real, T.eval x = Real.log (1 + Real.log ((1 + 1) + Real.sin x))) :
    False := by
  have hwf_c2 : nestedWF [(1 + 1 : Real)] := by
    refine ⟨?_, trivial⟩
    show (0 : Real) < (1 + 1) + nestedLo ([] : List Real)
    show (0 : Real) < (1 + 1) + (-1)
    have e : (1 + 1 : Real) + (-1) = 1 := by mach_ring
    rw [e]; exact zero_lt_one_ax
  have hlo_c2 : nestedLo [(1 + 1 : Real)] = 0 := by
    show Real.log ((1 + 1) + nestedLo ([] : List Real)) = 0
    show Real.log ((1 + 1) + (-1)) = 0
    have e : (1 + 1 : Real) + (-1) = 1 := by mach_ring
    rw [e]; exact log_one
  have hhi_c2_pos : (0 : Real) < nestedHi [(1 + 1 : Real)] := by
    show (0 : Real) < Real.log ((1 + 1) + nestedHi ([] : List Real))
    show (0 : Real) < Real.log ((1 + 1) + 1)
    rw [← log_one]
    have h3gt1 : (1 : Real) < (1 + 1) + 1 :=
      lt_trans_ax one_lt_one_add_one (lt_add_pos (1 + 1) 1 zero_lt_one_ax)
    exact log_lt_log zero_lt_one_ax h3gt1
  have hwf : nestedWF [1, (1 + 1 : Real)] := by
    refine ⟨?_, hwf_c2⟩
    show (0 : Real) < (1 : Real) + nestedLo [(1 + 1 : Real)]
    rw [hlo_c2, add_zero]; exact zero_lt_one_ax
  have hc_le : (1 : Real) + nestedLo [(1 + 1 : Real)] ≤ 1 := by
    rw [hlo_c2, add_zero]
    exact le_refl 1
  have hc_gt : (1 : Real) < (1 : Real) + nestedHi [(1 + 1 : Real)] := by
    have h := add_lt_add_left hhi_c2_pos (1 : Real)
    rwa [add_zero] at h
  obtain ⟨hlo, hhi⟩ := nestedTarget_cons_straddle 1 [(1 + 1 : Real)] hwf hc_le hc_gt
  have heq' : ∀ x : Real, T.eval x = nestedTarget [1, (1 + 1 : Real)] x := by
    intro x
    rw [nestedTarget_cons, nestedTarget_cons, nestedTarget_nil]
    exact heq x
  exact no_tree_eq_nestedTarget_unconditional [1, (1 + 1 : Real)] hwf hlo hhi T heq'

end Real
end MachLib
