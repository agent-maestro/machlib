import MachLib.EMLDepth2Case9Closure
import MachLib.EMLAdditionClosureFailure

/-!
# EML is closed under multiplication of POSITIVE subtrees — and contains every `xⁿ`

`EMLAdditionClosureFailure` proves `mulTree_eval` under `1 < a.eval x`. That hypothesis excludes
everything vanishing at `0`, so it cannot be iterated: `x·x` is out of reach because `x` is not
eventually above `1` near the origin.

**`a + 1 > 1` whenever `a > 0`.** So shift, multiply, and subtract the cross-terms back off:

```
a·b  =  (a+1)(b+1)  −  (a + b + 1)
```

Every side-condition is then plain **positivity**, and positivity is **preserved** by the result —
which is what makes it iterate. `xⁿ` follows by induction.

Companion to `EMLDepth2Case9Closure.inv_x_mem_EML`. Same domain restriction (`x > 0`) and for the
same reason: `exp ∘ log = id` needs a positive argument.
-/

namespace MachLib

open Real

/-- `0 < a → 1 < a + 1`. -/
theorem one_lt_add_one {a : Real} (ha : 0 < a) : 1 < a + 1 := by
  have h := add_lt_add_left ha 1
  have e1 : (1 : Real) + 0 = 1 := by mach_ring
  have e2 : (1 : Real) + a = a + 1 := by mach_ring
  rw [e1, e2] at h
  exact h

theorem zero_lt_add_one {a : Real} (ha : 0 < a) : 0 < a + 1 :=
  lt_trans_ax one_pos (one_lt_add_one ha)

/-- **Multiplication needing only POSITIVITY of both factors** — `a·b = (a+1)(b+1) − (a+b+1)`. -/
noncomputable def mulPos (a b : EMLTree) : EMLTree :=
  subTree (mulTree (addTree a (.const 1)) (addTree b (.const 1)))
          (addTree (addTree a b) (.const 1))

theorem mulPos_eval {a b : EMLTree} {x : Real}
    (ha : 0 < a.eval x) (hb : 0 < b.eval x) :
    (mulPos a b).eval x = a.eval x * b.eval x := by
  have hc : (EMLTree.const (1 : Real)).eval x = 1 := rfl
  have hA : (addTree a (.const 1)).eval x = a.eval x + 1 := by
    rw [addTree_eval (.const 1) ha, hc]
  have hB : (addTree b (.const 1)).eval x = b.eval x + 1 := by
    rw [addTree_eval (.const 1) hb, hc]
  have hA1 : 1 < (addTree a (.const 1)).eval x := by rw [hA]; exact one_lt_add_one ha
  have hB0 : 0 < (addTree b (.const 1)).eval x := by rw [hB]; exact zero_lt_add_one hb
  have hM : (mulTree (addTree a (.const 1)) (addTree b (.const 1))).eval x
      = (a.eval x + 1) * (b.eval x + 1) := by
    rw [mulTree_eval hA1 hB0, hA, hB]
  have hMpos : 0 < (mulTree (addTree a (.const 1)) (addTree b (.const 1))).eval x := by
    rw [hM]; exact mul_pos (zero_lt_add_one ha) (zero_lt_add_one hb)
  have hS : (addTree a b).eval x = a.eval x + b.eval x := addTree_eval b ha
  have hS1 : (addTree (addTree a b) (.const 1)).eval x = a.eval x + b.eval x + 1 := by
    rw [addTree_eval (.const 1) (by rw [hS]; exact add_pos ha hb), hS, hc]
  rw [mulPos, subTree_eval _ hMpos, hM, hS1]
  mach_mpoly [a.eval x, b.eval x]

/-- Positivity is PRESERVED — this is what lets `mulPos` iterate. -/
theorem mulPos_pos {a b : EMLTree} {x : Real}
    (ha : 0 < a.eval x) (hb : 0 < b.eval x) : 0 < (mulPos a b).eval x := by
  rw [mulPos_eval ha hb]; exact mul_pos ha hb

/-- `x ↦ xⁿ`, defined here so the module stays free of `Monoid.npow`. -/
noncomputable def powN (x : Real) : Nat → Real
  | 0 => 1
  | n + 1 => x * powN x n

noncomputable def powTree : Nat → EMLTree
  | 0 => .const 1
  | n + 1 => mulPos EMLTree.var (powTree n)

theorem powN_pos {x : Real} (hx : 0 < x) : ∀ n : Nat, 0 < powN x n
  | 0 => one_pos
  | n + 1 => mul_pos hx (powN_pos hx n)

/-- **`xⁿ ∈ EML` for every `n`**, on `x > 0`. -/
theorem powTree_eval {x : Real} (hx : 0 < x) : ∀ n : Nat, (powTree n).eval x = powN x n
  | 0 => rfl
  | n + 1 => by
      have hp : (powTree n).eval x = powN x n := powTree_eval hx n
      have hv : EMLTree.var.eval x = x := rfl
      have hppos : 0 < (powTree n).eval x := by rw [hp]; exact powN_pos hx n
      show (mulPos EMLTree.var (powTree n)).eval x = x * powN x n
      rw [mulPos_eval (by rw [hv]; exact hx) hppos, hv, hp]

/-- **`x² ∈ EML`** — the successor question of `RESULT_DOWNSTREAM_AUDIT.md`, answered YES. -/
theorem x_sq_mem_EML : ∃ t : EMLTree, ∀ x : Real, 0 < x → t.eval x = x * x :=
  ⟨mulPos EMLTree.var EMLTree.var, fun x hx => by
    have hv : EMLTree.var.eval x = x := rfl
    rw [mulPos_eval (by rw [hv]; exact hx) (by rw [hv]; exact hx), hv]⟩

end MachLib
