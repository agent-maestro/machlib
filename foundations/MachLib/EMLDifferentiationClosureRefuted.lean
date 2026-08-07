import MachLib.EMLPolynomialClosure
import MachLib.EMLDifferentiationClosureFailure

/-!
# The differentiation-closure arc's own witness IS in EML

`EMLDifferentiationClosureFailure` differentiates `eml var var = exp x − log x` (depth 1), targets

```
f(x) = exp x − 1/x
```

proves `f ∉ EML₁`, and leaves the general-depth statement **open** — reducing it, per its own
header, to a sub-lemma that *"converges with the open problem from the addition-closure attempt."*
That reduction ran through `1/x ∉ EML`, which `EMLDepth2Case9Closure.inv_x_mem_EML` refutes.

**`f` is in EML.** `subTree` needs only its LEFT operand positive, and `exp x > 0` everywhere.

## What this does NOT say

**EML is not thereby closed under differentiation.** The general statement needs
`A'·exp A − B'/B` for arbitrary subtrees, and `mulPos` requires **both** factors positive while `A'`
is sign-changing. **Open.**

`f ∉ EML₁` remains **true** — differentiation does not preserve depth. Only the *general-depth*
claim about this witness falls.
-/

namespace MachLib

open Real

/-- **`exp x − 1/x ∈ EML`** — the differentiation-closure arc's own witness, on `x > 0`. -/
theorem exp_sub_inv_x_mem_EML :
    ∃ t : EMLTree, ∀ x : Real, 0 < x → t.eval x = Real.exp x - 1 / x := by
  obtain ⟨R, hR⟩ := inv_x_mem_EML
  refine ⟨subTree (expOf .var) R, fun x hx => ?_⟩
  have hv : (EMLTree.var).eval x = x := rfl
  have hpos : 0 < (expOf (EMLTree.var)).eval x := by
    rw [expOf_eval, hv]; exact exp_pos x
  rw [subTree_eval R hpos, expOf_eval, hv, hR x hx]

end MachLib
