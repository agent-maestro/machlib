import MachLib.WitnessResidualNestedTargetDepth2Straddle

/-!
# An infinite tower: one unconditional closure at EVERY nesting depth

Continuation of Option D (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`). Cont. 61 closed one
depth-2 instance (`cs = [1, 2]`) and flagged depth 3+ as unchecked. This file checks it — and finds
the `c2 = 2, d = 1` choice isn't a one-off convenience, it's a FIXED POINT: `nestedLo` stays EXACTLY
`0` at every level of prepending another `1`, so the same zero-fresh-numeric-facts argument that
closed depth 2 closes EVERY depth, by one induction on `Nat`.

**The tower.** `oneShiftTower n` — `n` copies of `1` prepended to `[1+1]`. `oneShiftTower 0 = [2]`
(cont. 60's boundary instance); `oneShiftTower 1 = [1, 2]` (cont. 61's depth-2 instance);
`oneShiftTower 2 = [1, 1, 2]`, and so on.

**Why `nestedLo` is a fixed point at `1`.** `nestedLo [2] = log(2-1) = log 1 = 0` (cont. 60).
Prepending another `1`: `nestedLo (1 :: cs) = log(1 + nestedLo cs)`. If `nestedLo cs = 0`, this is
`log(1+0) = log 1 = 0` — EXACTLY the same value, not merely bounded. So `nestedLo (oneShiftTower
n) = 0` for every `n`, by induction, with no accumulating error or drift to track.

**Why `nestedHi` only needs to stay positive, not be tracked precisely.**
`nestedTarget_cons_straddle`'s window only needs `0 < nestedHi cs` at each level to conclude `0 <
nestedHi (1 :: cs)` (via `log_lt_log` at `1 < 1 + nestedHi cs`, which is exactly `0 < nestedHi
cs`) — the ACTUAL size of `nestedHi cs` never enters the argument, only its sign. So positivity
alone propagates up the tower, one application of the depth-2 argument's own mechanism per level,
without ever needing a numeric bound on how big `nestedHi` gets.

**Payoff.** `oneShiftTower_straddles : ∀ n, nestedWF (oneShiftTower n) ∧ nestedLo (oneShiftTower n)
≤ 0 ∧ 0 < nestedHi (oneShiftTower n)`, hence `no_tree_eq_oneShiftTower_unconditional : ∀ n, ` no
finite EML tree's `eval` equals `nestedTarget (oneShiftTower n)` — an INFINITE family of
unconditionally-closed nested targets, one at every depth, not just the two hand-checked instances
from cont. 60-61.

**Honest scope.** Still one specific family (built from repeated `1`-shifts over the `c2 = 2`
boundary) inside the much larger space `nestedWF cs` allows — not "every deep `cs` closes," but
"depth is not itself an obstruction to this method," which was the open question after cont. 61.
-/

namespace MachLib
namespace Real

/-- `n` copies of `1` prepended to `[1+1]`. -/
noncomputable def oneShiftTower : Nat → List Real
  | 0 => [(1 + 1 : Real)]
  | (n + 1) => 1 :: oneShiftTower n

/-- The induction carries EXACT equality on `nestedLo` (not just `≤ 0`) — wellformedness at the
NEXT level genuinely needs `0 < 1 + nestedLo cs`, which `nestedLo cs ≤ 0` alone cannot supply
(only `nestedLo cs = 0` pins it down to exactly `1 > 0`). -/
theorem oneShiftTower_facts (n : Nat) :
    nestedWF (oneShiftTower n) ∧ nestedLo (oneShiftTower n) = 0 ∧
      0 < nestedHi (oneShiftTower n) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · show nestedWF [(1 + 1 : Real)]
      refine ⟨?_, trivial⟩
      show (0 : Real) < (1 + 1) + nestedLo ([] : List Real)
      show (0 : Real) < (1 + 1) + (-1)
      have e : (1 + 1 : Real) + (-1) = 1 := by mach_ring
      rw [e]; exact zero_lt_one_ax
    · show nestedLo [(1 + 1 : Real)] = 0
      show Real.log ((1 + 1) + nestedLo ([] : List Real)) = 0
      show Real.log ((1 + 1) + (-1)) = 0
      have e : (1 + 1 : Real) + (-1) = 1 := by mach_ring
      rw [e, log_one]
    · show (0 : Real) < nestedHi [(1 + 1 : Real)]
      show (0 : Real) < Real.log ((1 + 1) + nestedHi ([] : List Real))
      show (0 : Real) < Real.log ((1 + 1) + 1)
      rw [← log_one]
      have h3gt1 : (1 : Real) < (1 + 1) + 1 :=
        lt_trans_ax one_lt_one_add_one (lt_add_pos (1 + 1) 1 zero_lt_one_ax)
      exact log_lt_log zero_lt_one_ax h3gt1
  | succ m ih =>
    obtain ⟨ihwf, ihlo, ihhi⟩ := ih
    have hwf : nestedWF (1 :: oneShiftTower m) := by
      refine ⟨?_, ihwf⟩
      show (0 : Real) < (1 : Real) + nestedLo (oneShiftTower m)
      rw [ihlo, add_zero]; exact zero_lt_one_ax
    have hc_le : (1 : Real) + nestedLo (oneShiftTower m) ≤ 1 := by
      rw [ihlo, add_zero]; exact le_refl 1
    have hc_gt : (1 : Real) < (1 : Real) + nestedHi (oneShiftTower m) := by
      have h := add_lt_add_left ihhi (1 : Real)
      rwa [add_zero] at h
    obtain ⟨hlo, hhi⟩ := nestedTarget_cons_straddle 1 (oneShiftTower m) hwf hc_le hc_gt
    have hlo_eq : nestedLo (1 :: oneShiftTower m) = 0 := by
      show Real.log ((1 : Real) + nestedLo (oneShiftTower m)) = 0
      rw [ihlo, add_zero]; exact log_one
    exact ⟨hwf, hlo_eq, hhi⟩

/-- **An infinite tower of unconditionally-closed nested targets, one at every depth.** -/
theorem no_tree_eq_oneShiftTower_unconditional (n : Nat) (T : EMLTree)
    (heq : ∀ x : Real, T.eval x = nestedTarget (oneShiftTower n) x) : False := by
  obtain ⟨hwf, hlo, hhi⟩ := oneShiftTower_facts n
  exact no_tree_eq_nestedTarget_unconditional (oneShiftTower n) hwf (le_of_eq hlo) hhi T heq

end Real
end MachLib
