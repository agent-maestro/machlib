import MachLib.EMLPolynomialClosure

/-!
# EML is closed under `+`, `−`, `×` — **with no hypotheses at all**

Every closure result the corpus had carried a **positivity side-condition**, because
`exp ∘ log = id` needs a positive argument: `addTree`/`subTree` need `0 < a`, `mulTree` needs
`1 < a`, and `mulPos` (see `EMLPolynomialClosure`) needs both factors positive. Those conditions
blocked everything sign-changing — `x · log x` was the smallest instance, and the gateway to `xˣ`.

**They all lift, via one gadget.** For any subtree `t`,

```
domTree t := exp (1 − t)          -- positive, and dominates −t
```

is positive **and** satisfies `domTree t + t > 1 > 0`, because `y < exp y` at `y = 1 − t`. So any
subtree can be shifted into the positive range by an EML-expressible amount and the shift subtracted
back off afterwards. **The side-conditions were never about the class; they were about the route.**

The results are unconditional in `x` as well: no step needs `0 < x`.
-/

namespace MachLib

open Real

/-- `exp (1 − t)` — positive, and dominates `−t`. -/
noncomputable def domTree (t : EMLTree) : EMLTree := expOf (negOffset 0 t)

theorem domTree_eval (t : EMLTree) (x : Real) :
    (domTree t).eval x = Real.exp (1 - t.eval x) := by
  rw [domTree, expOf_eval, negOffset_eval, exp_zero]

theorem domTree_pos (t : EMLTree) (x : Real) : 0 < (domTree t).eval x := by
  rw [domTree_eval]; exact exp_pos _

/-- **The shift is enough**: `exp (1 − t) + t > 0`, unconditionally. -/
theorem domTree_add_pos (t : EMLTree) (x : Real) :
    0 < (domTree t).eval x + t.eval x := by
  have h : (1 - t.eval x) < Real.exp (1 - t.eval x) := exp_grows_strictly_thm _
  rw [domTree_eval]
  have h1 : (0 : Real) < Real.exp (1 - t.eval x) - (1 - t.eval x) := sub_pos_of_lt h
  have h2 : Real.exp (1 - t.eval x) - (1 - t.eval x)
      = (Real.exp (1 - t.eval x) + t.eval x) - 1 := by mach_ring
  rw [h2] at h1
  have h3 : (1 : Real) < Real.exp (1 - t.eval x) + t.eval x := by
    have := add_lt_add_left h1 1
    have e1 : (1 : Real) + 0 = 1 := by mach_ring
    have e2 : (1 : Real) + ((Real.exp (1 - t.eval x) + t.eval x) - 1)
        = Real.exp (1 - t.eval x) + t.eval x := by mach_ring
    rw [e1, e2] at this
    exact this
  exact lt_trans_ax one_pos h3

/-- `(domTree u) + u`, the canonical positive shift of `u`. -/
theorem shift_pos (u : EMLTree) (x : Real) :
    0 < (addTree (domTree u) u).eval x := by
  rw [addTree_eval u (domTree_pos u x)]
  exact domTree_add_pos u x

theorem shift_eval (u : EMLTree) (x : Real) :
    (addTree (domTree u) u).eval x = (domTree u).eval x + u.eval x :=
  addTree_eval u (domTree_pos u x)

/-- **Subtraction, unconditional.** -/
noncomputable def subGen (u v : EMLTree) : EMLTree :=
  subTree (addTree (domTree u) u) (addTree (domTree u) v)

theorem subGen_eval (u v : EMLTree) (x : Real) :
    (subGen u v).eval x = u.eval x - v.eval x := by
  rw [subGen, subTree_eval _ (shift_pos u x), shift_eval,
      addTree_eval v (domTree_pos u x)]
  mach_ring

/-- **Addition, unconditional.** -/
noncomputable def addGen (u v : EMLTree) : EMLTree :=
  subGen (addTree (addTree (domTree u) u) v) (domTree u)

theorem addGen_eval (u v : EMLTree) (x : Real) :
    (addGen u v).eval x = u.eval x + v.eval x := by
  rw [addGen, subGen_eval, addTree_eval v (shift_pos u x), shift_eval]
  mach_ring

/-- **Multiplication needing only the LEFT factor positive** — the right one is arbitrary. -/
noncomputable def mulL (a b : EMLTree) : EMLTree :=
  subTree (mulPos a (addTree (domTree b) b)) (mulPos a (domTree b))

theorem mulL_eval {a : EMLTree} (b : EMLTree) {x : Real} (ha : 0 < a.eval x) :
    (mulL a b).eval x = a.eval x * b.eval x := by
  have hP : 0 < (mulPos a (addTree (domTree b) b)).eval x :=
    mulPos_pos ha (shift_pos b x)
  rw [mulL, subTree_eval _ hP, mulPos_eval ha (shift_pos b x),
      mulPos_eval ha (domTree_pos b x), shift_eval]
  mach_mpoly [a.eval x, b.eval x, (domTree b).eval x]

/-- **Multiplication, unconditional — both factors arbitrary.** -/
noncomputable def mulGen (u v : EMLTree) : EMLTree :=
  subGen (mulL (addTree (domTree u) u) v) (mulL (domTree u) v)

theorem mulGen_eval (u v : EMLTree) (x : Real) :
    (mulGen u v).eval x = u.eval x * v.eval x := by
  rw [mulGen, subGen_eval, mulL_eval v (shift_pos u x),
      mulL_eval v (domTree_pos u x), shift_eval]
  mach_mpoly [u.eval x, v.eval x, (domTree u).eval x]

/-- **Negation, unconditional.** -/
noncomputable def negGen (u : EMLTree) : EMLTree := subGen (.const 0) u

theorem negGen_eval (u : EMLTree) (x : Real) : (negGen u).eval x = -u.eval x := by
  have hc : (EMLTree.const (0 : Real)).eval x = 0 := rfl
  rw [negGen, subGen_eval, hc]
  mach_ring

/-- **`x · log x ∈ EML`** — the frontier instance, on `x > 0`. -/
theorem x_mul_log_mem_EML :
    ∃ t : EMLTree, ∀ x : Real, 0 < x → t.eval x = x * Real.log x := by
  refine ⟨mulGen EMLTree.var (logTree EMLTree.var), fun x hx => ?_⟩
  have hv : (EMLTree.var).eval x = x := rfl
  rw [mulGen_eval, hv, logTree_eval, hv]

/-- **`xˣ ∈ EML`** — `exp (x · log x)`, on `x > 0`. -/
theorem x_pow_x_mem_EML :
    ∃ t : EMLTree, ∀ x : Real, 0 < x → t.eval x = Real.exp (x * Real.log x) := by
  refine ⟨expOf (mulGen EMLTree.var (logTree EMLTree.var)), fun x hx => ?_⟩
  have hv : (EMLTree.var).eval x = x := rfl
  rw [expOf_eval, mulGen_eval, hv, logTree_eval, hv]

end MachLib
