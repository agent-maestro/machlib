import MachLib.EMLCharacterisation
import MachLib.EMLDerivClosure

/-!
# What the closure constructions COST

`EMLCharacterisation` settles the class question and says nothing about depth. Six write-ups called
the constructions *"depth-expensive and unoptimised"* without a number. **Here are the numbers.**

They are bad, and deliberately recorded: `mulGen var var` — a tree for `x·x` — is **depth 54**,
while `mulPos var var`, which computes the same function under a positivity hypothesis, is **24**,
and the hand-built `1/x` witness is **6**.

> ### These are UPPER bounds from one particular encoding. Nothing here is optimal, and the gap between 6 and 54 is a measure of how much slack the general operators carry.

The one question the characterisation leaves: **what is the MINIMAL depth of `1/x`?** Known
`> 1` (`inv_x_not_in_eml_1`), and now `≤ 6`.
-/

set_option maxRecDepth 8000

namespace MachLib

open Real

theorem logTree_depth (t : EMLTree) : (logTree t).depth = 3 + t.depth := by
  simp only [logTree, negOffset, expOf, EMLTree.depth, Nat.zero_max, Nat.max_zero]
  omega

theorem domTree_depth (t : EMLTree) : (domTree t).depth = 3 + t.depth := by
  simp only [domTree, negOffset, expOf, EMLTree.depth, Nat.zero_max, Nat.max_zero]
  omega

/-- The `1/x` witness of `inv_x_mem_EML`, named so its depth is machine-checkable. -/
noncomputable def invXTree : EMLTree :=
  EMLTree.eml (EMLTree.eml (EMLTree.const (log (log (exp 1)))) (witT (exp 1))) (EMLTree.const 0)

theorem invXTree_eval : ∀ x : Real, 0 < x → invXTree.eval x = 1 / x := by
  have hm : (1 : Real) < exp 1 := by
    have step : exp 0 < exp 1 := exp_lt zero_lt_one_ax
    rw [exp_zero] at step
    exact step
  have hmpos : (0 : Real) < exp 1 := lt_trans_ax zero_lt_one_ax hm
  have hc : (0 : Real) < log (exp 1) + 1 := by
    rw [log_exp]; exact add_pos zero_lt_one_ax zero_lt_one_ax
  exact inv_x_of_mx hm (fun x hx => witT_eval hmpos hc x hx)

/-- **`1/x` at depth 6** — the current upper bound, machine-checked. -/
theorem invXTree_depth : invXTree.depth = 6 := by rfl

-- ▸ The cost of the general operators, at their cheapest arguments.

theorem subTree_var_var_depth : (subTree EMLTree.var EMLTree.var).depth = 4 := by rfl
theorem addTree_var_var_depth : (addTree EMLTree.var EMLTree.var).depth = 8 := by rfl
theorem subGen_var_var_depth  : (subGen  EMLTree.var EMLTree.var).depth = 15 := by rfl
theorem mulPos_var_var_depth  : (mulPos  EMLTree.var EMLTree.var).depth = 24 := by rfl
theorem addGen_var_var_depth  : (addGen  EMLTree.var EMLTree.var).depth = 34 := by rfl
theorem invPos_var_depth      : (invPos  EMLTree.var).depth = 16 := by rfl

/-- **`x·x` costs 54 levels** through the unconditional operator — against 24 through `mulPos`,
which needs positivity, and 6 for the hand-built `1/x`. **The generality is not free.** -/
theorem mulGen_var_var_depth : (mulGen EMLTree.var EMLTree.var).depth = 54 := by rfl

end MachLib
