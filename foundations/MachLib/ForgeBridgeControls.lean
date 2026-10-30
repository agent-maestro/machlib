import MachLib.Forge

/-!
# The two removed Forge "bridge" axioms, and the theorem one of them proved: three refutations (2026-10-27)

`Forge.lean` carried two "bridge" axioms whose docstrings said the Forge emitter would apply them only when a
literal condition held (`k ≤ 1`; `j + k ≤ 1`) — a condition stated in prose and missing from the type. Both were
false, and `interval_add_scale`, proved through the second, had a false statement too. All three were removed or
restated on 2026-10-27 (found by that day's independent review; the owner ruled to fix them in a separate change).
This module keeps the old statements as propositions and refutes each from the field and order axioms alone, so
"removed" reads as "was false", not "was unused":

* `unit_lit_le_false`: the old `interval_scale_unit_lit_le` (`0 < k → 0 < k → k ≤ 1`) at `k = 1 + 1`.
* `weight_sum_le_false`: the old `interval_weight_sum_le` (`j, k ∈ (0, 1] → j + k ≤ 1`) at `j = k = 1`.
* `old_interval_add_scale_false`: the old `interval_add_scale` (no `j + k ≤ 1` hypothesis) at `x = y = j = k = 1`,
  where `x·j + y·k = 1 + 1`.

The restated `interval_add_scale` takes `j + k ≤ 1`; these propositions are recorded in
`tools/hypothesis_baseline.json` as refuted statements, which must never gain a producer.
-/

namespace MachLib
namespace Real
namespace ForgeBridgeControls

/-- The statement of `interval_scale_unit_lit_le` before 2026-10-27. -/
def OldUnitLitLeStatement : Prop := ∀ {k : Real}, 0 < k → 0 < k → k ≤ 1

/-- The statement of `interval_weight_sum_le` before 2026-10-27. -/
def OldWeightSumLeStatement : Prop := ∀ {j k : Real}, 0 < j → 0 < k → j ≤ 1 → k ≤ 1 → j + k ≤ 1

/-- The statement of `interval_add_scale` before 2026-10-27. -/
def OldIntervalAddScaleStatement : Prop :=
  ∀ (x y j k : Real), 0 < j → 0 < k → j ≤ 1 → k ≤ 1 → 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 →
    (0 : Real) ≤ x * j + y * k ∧ x * j + y * k ≤ 1

private theorem one_lt_two_c : (1 : Real) < 1 + 1 := by
  have v := add_lt_add_left zero_lt_one_ax (1 : Real)
  rw [add_zero] at v
  exact v

private theorem not_two_le_one : ¬ ((1 : Real) + 1 ≤ 1) := fun h =>
  lt_irrefl_ax 1 (lt_of_lt_of_le one_lt_two_c h)

private theorem one_le_one_c : (1 : Real) ≤ 1 := (le_iff_lt_or_eq 1 1).mpr (Or.inr rfl)

/-- **The old `interval_scale_unit_lit_le` is false**: at `k = 1 + 1` it says `1 + 1 ≤ 1`. -/
theorem unit_lit_le_false (h : OldUnitLitLeStatement) : False := by
  have h0 : (0 : Real) < 1 + 1 := lt_trans_ax zero_lt_one_ax one_lt_two_c
  exact not_two_le_one (h h0 h0)

/-- **The old `interval_weight_sum_le` is false**: at `j = k = 1` it says `1 + 1 ≤ 1`. -/
theorem weight_sum_le_false (h : OldWeightSumLeStatement) : False :=
  not_two_le_one (h zero_lt_one_ax zero_lt_one_ax one_le_one_c one_le_one_c)

/-- **The old `interval_add_scale` is false**: at `x = y = j = k = 1` its upper half says `1·1 + 1·1 ≤ 1`. -/
theorem old_interval_add_scale_false (h : OldIntervalAddScaleStatement) : False := by
  have h0 : (0 : Real) ≤ 1 := (le_iff_lt_or_eq 0 1).mpr (Or.inl zero_lt_one_ax)
  have hb := (h 1 1 1 1 zero_lt_one_ax zero_lt_one_ax one_le_one_c one_le_one_c h0 one_le_one_c h0 one_le_one_c).2
  rw [mul_one_ax] at hb
  exact not_two_le_one hb

end ForgeBridgeControls
end Real
end MachLib
