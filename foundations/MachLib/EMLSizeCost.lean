import MachLib.EMLPolynomialsAll

/-!
# What the closure constructions cost in SIZE

`EMLDepthCost` measured depth, because depth is what the `EML_k` hierarchy counts. **Size is a second
axis and it is exponentially worse.** This measures it.

**The blowup is not intrinsic to EML.** Every operator that avoids putting `domTree u` and `u` in the
same expression mentions each argument **exactly once**, so its size is **linear**:

```
expOf 2+ ·   negOffset 4+ ·   logTree 6+ ·   domTree 6+ ·
subTree 9+a+b   addTree 21+a+b   mulTree 35+a+b
```

The duplicating ones all use the shift gadget. Measured argument multiplicity:
`mulPos (2,2)`, `subGen (3,1)`, `addGen (7,3)`, `mulL (4,6)`, **`mulGen (28,24)`**.

> ### Unconditionality was paid for in SIZE, and the receipt is `mulGen`: **28 copies of its left argument.**
-/

namespace MachLib

/-- Node count. -/
def EMLTree.size : EMLTree → Nat
  | .const _ => 1
  | .var => 1
  | .eml a b => 1 + a.size + b.size

namespace Real

-- ▸ The LINEAR operators: each argument appears exactly once.

theorem size_expOf (t : EMLTree) : (expOf t).size = 2 + t.size := by
  simp only [expOf, EMLTree.size]; omega

theorem size_negOffset (c : Real) (t : EMLTree) : (negOffset c t).size = 4 + t.size := by
  simp only [negOffset, expOf, EMLTree.size]; omega

theorem size_logTree (t : EMLTree) : (logTree t).size = 6 + t.size := by
  simp only [logTree, negOffset, expOf, EMLTree.size]; omega

theorem size_domTree (t : EMLTree) : (domTree t).size = 6 + t.size := by
  simp only [domTree, negOffset, expOf, EMLTree.size]; omega

theorem size_subTree (a b : EMLTree) : (subTree a b).size = 9 + a.size + b.size := by
  simp only [subTree, logTree, negOffset, expOf, EMLTree.size]; omega

theorem size_addTree (a b : EMLTree) : (addTree a b).size = 21 + a.size + b.size := by
  simp only [addTree, subTree, logTree, negOffset, expOf, EMLTree.size]; omega

theorem size_mulTree (a b : EMLTree) : (mulTree a b).size = 35 + a.size + b.size := by
  simp only [mulTree, addTree, subTree, logTree, negOffset, expOf, EMLTree.size]; omega

-- ▸ The DUPLICATING operators, at leaf arguments.

theorem size_mulPos_var_var : (mulPos EMLTree.var EMLTree.var).size = 135 := by rfl
theorem size_subGen_var_var : (subGen EMLTree.var EMLTree.var).size = 67 := by rfl
theorem size_addGen_var_var : (addGen EMLTree.var EMLTree.var).size = 223 := by rfl
theorem size_mulL_var_var   : (mulL   EMLTree.var EMLTree.var).size = 347 := by rfl

/-- **`x·x` unconditionally: 1 811 nodes** — against 135 through `mulPos`. -/
theorem size_mulGen_var_var : (mulGen EMLTree.var EMLTree.var).size = 1811 := by rfl

/-- The hand-built `1/x` witness is **13 nodes** — against 1 811 for `mulGen var var`.
**A 139× gap between hand-construction and generic machinery.** -/
theorem size_invXTree : invXTree.size = 13 := by rfl

end Real

set_option maxRecDepth 2000000 in
theorem size_polyTree_two : (polyTree [0, 1]).size = 412597 := by rfl

set_option maxRecDepth 40000000 in
/-- **29 712 565 nodes** for `x²` as a generic polynomial — `~72×` per coefficient. -/
theorem size_polyTree_three : (polyTree [0, 0, 1]).size = 29712565 := by rfl

end MachLib
