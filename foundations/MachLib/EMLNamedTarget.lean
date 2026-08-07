import MachLib.EMLBranchPigeonhole

/-!
# A2′ localized — the regress needs a LEAF, not a constant, and only case 9 resists

`EMLTerminationRoute.lean` showed `pins_right` determines the child but names `u.eval x`, so the
regress needs a target it can NAME. I recorded the condition as *"`u` must be constant-valued"*.

> ## ⚠ THAT CONDITION IS TOO STRONG, AND THIS FILE CORRECTS IT.

The pinned value `exp (exp (u.eval x) − f)` is a named function of `x` exactly when `u.eval` is a
known function — and **both leaves qualify**:

| `u` | pinned target for `w` | |
|---|---|---|
| `const a` | `exp (exp a − f)` | named **up to one real parameter** |
| **`var`** | **`exp (exp x − f)`** | named **with NO free parameter** |
| a subtree | `exp (exp (u.eval x) − f)` | not named |

> ### `var` is a BETTER case for the regress than `const`, not a worse one. The "constant-valued" framing had it backwards.

**And the clamped branch was never affected at all**: `clamped_pins_left` gives `u.eval x = log f`,
with no reference to `w` whatsoever.

## Where A2′ actually lives

`a2prime_residue` gives the exhaustive split. Against the census's nine root cases:

| case | children | target |
|---|---|---|
| 1, 2, 4, 5 | both leaves | named — **all four already CLOSED** |
| 3, 6 | `const`/`var` over subtree | **named** (left is a leaf) |
| 7, 8 | subtree over `const`/`var` | **named** (right is a leaf) |
| **9** | **subtree over subtree** | ❌ **the residue** |

> **A2′ is not "the varying-left branch". It is census case 9, on the positive branch.** Cases 3, 6
> and 8 recurse because the target is **NEW**, not because it is **UNNAMED** — a distinction the
> census never drew.

## ⚠ WHAT THIS DOES NOT DO

**Case 9 is the generic case and remains the real obstacle.** Naming where a difficulty lives is not
removing it, and changing *why* cases 3/6/8 recurse does not change *that* they recurse.
**`1/x ∉ EML` is untouched.**
-/

namespace MachLib
namespace Real

open EMLTree

/-! ## A leaf on the left names the right child's target -/

/-- **`u = const a`** — named up to the one parameter `a`. (This is `const_left_pins_child`
specialised; kept here so the four naming cases sit together.) -/
theorem const_left_names_right {w : EMLTree} {a f x : Real}
    (hw : 0 < w.eval x)
    (e : (EMLTree.eml (EMLTree.const a) w).eval x = f) :
    w.eval x = exp (exp a - f) :=
  const_left_pins_child rfl hw e

/-- **`u = var` — the target is named with NO free parameter.**

`w.eval x = exp (exp x − f)`. **Strictly better for the regress than the `const` case**, which
carries an unknown `a`. This is the case the *"`u` must be constant-valued"* framing wrongly
excluded. -/
theorem var_left_names_right {w : EMLTree} {f x : Real}
    (hw : 0 < w.eval x)
    (e : (EMLTree.eml EMLTree.var w).eval x = f) :
    w.eval x = exp (exp x - f) :=
  const_left_pins_child rfl hw e

/-! ## A leaf on the right names the left child's target -/

/-- **`w = const c`, `c > 0`** — `exp (u.eval x) = f + log c`, named up to `c`. -/
theorem const_right_names_left {u : EMLTree} {c f x : Real}
    (hc : 0 < c)
    (e : (EMLTree.eml u (EMLTree.const c)).eval x = f) :
    exp (u.eval x) = f + log c := by
  have v : (EMLTree.eml u (EMLTree.const c)).eval x = exp (u.eval x) - log c := rfl
  rw [v] at e
  have e2 : exp (u.eval x) = (exp (u.eval x) - log c) + log c := by mach_ring
  rw [e2, e]

/-- **`w = var`, `x > 0` — named with NO free parameter.** `exp (u.eval x) = f + log x`.

The mirror of `var_left_names_right`: a `var` on either side names the other child's target
outright. -/
theorem var_right_names_left {u : EMLTree} {f x : Real}
    (hx : 0 < x)
    (e : (EMLTree.eml u EMLTree.var).eval x = f) :
    exp (u.eval x) = f + log x := by
  have v : (EMLTree.eml u EMLTree.var).eval x = exp (u.eval x) - log x := rfl
  rw [v] at e
  have e2 : exp (u.eval x) = (exp (u.eval x) - log x) + log x := by mach_ring
  rw [e2, e]

/-! ## The clamped branch never needed naming at all -/

/-- **On the clamped branch the target is ALWAYS named**, for any `u` and `w` whatsoever:
`u.eval x = log f`, with **no reference to `w`**.

**So A2′ cannot bite on the clamped branch.** The morning's write-up did not say this. -/
theorem clamped_target_always_named {u w : EMLTree} {f x : Real}
    (hw : w.eval x ≤ 0)
    (e : (EMLTree.eml u w).eval x = f) :
    u.eval x = log f :=
  clamped_pins_left hw e

/-! ## A2′, localized -/

/-- **The exhaustive split, and it puts A2′ in exactly one cell.**

1. **clamped** — target named (`log f`), no condition on either child;
2. **positive, left a leaf** — `w`'s target named;
3. **positive, right a leaf** — `u`'s target named;
4. **positive, both of depth ≥ 1** — **THE RESIDUE.**

> **Against the census's nine root cases, cell 4 is case 9 alone.** Cases 3, 6 and 8 land in cells 2
> and 3: their targets ARE named, and they recurse because the target is NEW. -/
theorem a2prime_residue (u w : EMLTree) {f x : Real}
    (e : (EMLTree.eml u w).eval x = f) :
    (w.eval x ≤ 0 ∧ u.eval x = log f)
    ∨ (0 < w.eval x ∧ u.depth = 0)
    ∨ (0 < w.eval x ∧ w.depth = 0)
    ∨ (0 < w.eval x ∧ 1 ≤ u.depth ∧ 1 ≤ w.depth) := by
  rcases pos_or_nonpos (w.eval x) with hpos | hnp
  · rcases Nat.eq_zero_or_pos u.depth with hu | hu
    · exact Or.inr (Or.inl ⟨hpos, hu⟩)
    · rcases Nat.eq_zero_or_pos w.depth with hw | hw
      · exact Or.inr (Or.inr (Or.inl ⟨hpos, hw⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hpos, hu, hw⟩))
  · exact Or.inl ⟨hnp, clamped_pins_left hnp e⟩

/-- **The residue is not empty** — `eml (eml var var) (eml var var)` is a case-9 shape, positive at
`x = 1`, with both children of depth 1.

**Stated so the localization cannot be mistaken for an exclusion.** Cell 4 is where the work is, and
it has inhabitants. -/
theorem a2prime_residue_nonempty :
    1 ≤ (EMLTree.eml EMLTree.var EMLTree.var).depth ∧
      0 < (EMLTree.eml EMLTree.var EMLTree.var).eval 1 := by
  constructor
  · exact Nat.le_refl 1
  · show 0 < exp (1 : Real) - log (1 : Real)
    rw [log_one]
    have e : exp (1 : Real) - 0 = exp 1 := by mach_ring
    rw [e]
    exact exp_pos 1

end Real
end MachLib
