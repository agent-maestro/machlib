import MachLib.EMLDepthTameness
import MachLib.EMLRationalGerm

/-!
# `SignHardCase` without the logarithm

`SignHardCase` is the last cancellation obligation: is `exp (A x) − log (B x)` eventually of constant
sign, when the right child is positive so its log is the real one? `evSign_of_hard` already reduces
sign-definiteness of *every* EML tree to it, so it is the whole remaining gap in the depth
programme.

This module removes the `log` from the statement.

## The observation

`log 1 = 0`, so `eml t (const 1)` evaluates to `exp (t.eval x)` — **`exp ∘ t` is again an EML tree**
(`expTree_eval`). Hence so is `exp ∘ exp ∘ t`. And on a ray where `B > 0`, `log` is a strictly
increasing bijection onto its image, so

```
exp (A x) − log (B x)  >  0   ⟺   exp (exp (A x))  >  B x
exp (A x) − log (B x)  ≤  0   ⟺   exp (exp (A x))  ≤  B x
```

Both sides of the right-hand comparison are EML tree values. So the obligation is equivalent to a
statement with **no logarithm and no totalisation in it at all**:

```
SignCompareExpExp : ∀ A B : EMLTree, EvSign (fun x => exp (exp (A.eval x)) − B.eval x)
```

## Why this is worth having

The totalised `log` (`log y = 0` for `y ≤ 0`) is what makes the depth induction awkward — it is the
reason `SignHardCase` has to carry a positivity hypothesis on `B` in the first place, and the reason
the branch where `B ≤ 0` is trivial while the branch where `B > 0` is not.
`signHardCase_of_compareExpExp` shows none of that is essential: what is left after the reduction is
a pure **growth comparison** between two EML germs, one of them a double exponential. The
positivity hypothesis is *consumed* by the reduction and does not reappear.

That matches this corpus's own diagnosis of the sign problem, recorded in `EMLGermSign`:
sign-definiteness is not hard in general, it is hard when the representation offers no normal form to
read it from. Here the representation question is now visible as such — comparability of EML germs —
rather than tangled with the totalisation convention.

## What is **not** claimed

`SignHardCase` stays **open** in the ledger. Nothing here discharges it; the content is that it is
the *same* obligation as a growth comparison, so the totalised `log` is removable rather than merely
avoidable.

Two forms, and the difference matters:

* `SignCompareExpExpPos` **keeps** `B`'s positivity and is **equivalent** to `SignHardCase`
  (`signHardCase_of_compareExpExpPos` and `compareExpExpPos_of_signHardCase`). This is the useful
  one — it neither strengthens nor weakens the obligation.
* `SignCompareExpExp` **drops** the positivity and is therefore *strictly stronger*, so
  `signHardCase_of_compareExpExpPos` composed with it reformulates the difficulty without lowering
  it. Kept only because it is the hypothesis-free shape a Hardy-field argument would naturally
  supply, and `treeComparable_imp` records that full pairwise comparability of EML germs gives it.

`signHard_of_le_one` is included to show where the difficulty is *not*: if `B` is eventually at most
`1` the node is positive for free, so the whole problem lives on the ray where `B > 1`.
-/

namespace MachLib

open Real

/-! ## Two order facts, in the local idiom -/

private theorem lt_of_sub_pos {a b : Real} (h : 0 < a - b) : b < a := by
  have v := add_lt_add_left h b
  have l : b + 0 = b := by mach_ring
  have r : b + (a - b) = a := by mach_ring
  rw [l, r] at v; exact v

private theorem le_of_sub_nonpos {a b : Real} (h : a - b ≤ 0) : a ≤ b := by
  have v := add_le_add_wit (le_refl b) h
  have l : b + (a - b) = a := by mach_ring
  have r : b + 0 = b := by mach_ring
  rw [l, r] at v; exact v

private theorem sub_nonpos_of_le {a b : Real} (h : a ≤ b) : a - b ≤ 0 := by
  have v := add_le_add_wit h (le_refl (-b))
  have l : a + -b = a - b := by mach_ring
  have r : b + -b = 0 := by mach_ring
  rw [l, r] at v; exact v

private theorem sub_pos_of_lt {a b : Real} (h : b < a) : 0 < a - b := by
  have v := add_lt_add_left h (-b)
  have l : -b + b = 0 := by mach_ring
  have r : -b + a = a - b := by mach_ring
  rw [l, r] at v; exact v

/-! ## `exp ∘ t` is again a tree -/

/-- **`exp` is expressible.** `log 1 = 0`, so the node `eml t (const 1)` *is* `exp ∘ t`. -/
theorem expTree_eval (t : EMLTree) (x : Real) :
    (EMLTree.eml t (EMLTree.const 1)).eval x = exp (t.eval x) := by
  show exp (t.eval x) - log (1 : Real) = exp (t.eval x)
  rw [log_one]
  mach_ring

/-- And therefore so is `exp ∘ exp ∘ t`. -/
theorem expExpTree_eval (t : EMLTree) (x : Real) :
    (EMLTree.eml (EMLTree.eml t (EMLTree.const 1)) (EMLTree.const 1)).eval x
      = exp (exp (t.eval x)) := by
  rw [expTree_eval, expTree_eval]

/-! ## Where the difficulty is not -/

/-- **`B ≤ 1` is free.** On a ray where `0 < B ≤ 1` the log is non-positive and the node is
positive, with no comparison needed. The whole problem lives on the ray where `B > 1`. -/
theorem signHard_of_le_one (A B : EMLTree) (X₀ : Real) (hX₀ : 1 ≤ X₀)
    (hB : ∀ x : Real, X₀ ≤ x → 0 < B.eval x) (hle : ∀ x : Real, X₀ ≤ x → B.eval x ≤ 1) :
    EvSign (fun x => exp (A.eval x) - log (B.eval x)) := by
  refine Or.inl ⟨X₀, hX₀, fun x hx => ?_⟩
  have hlog : log (B.eval x) ≤ 0 := by
    have h := log_le_log (hB x hx) (hle x hx)
    rwa [log_one] at h
  have hexp : 0 < exp (A.eval x) := exp_pos _
  exact lt_of_lt_of_le (sub_pos_of_lt (lt_of_le_of_lt hlog hexp)) (le_refl _)

/-! ## The reduction, and the equivalence

Keeping `B`'s positivity gives a statement **equivalent** to `SignHardCase`; dropping it gives a
strictly stronger one. Both are recorded, and the difference is the whole point of the section. -/

/-- The growth comparison, with `B`'s positivity retained. -/
def SignCompareExpExpPos : Prop :=
  ∀ (A B : EMLTree) (X₀ : Real), 1 ≤ X₀ → (∀ x : Real, X₀ ≤ x → 0 < B.eval x) →
    EvSign (fun x => exp (exp (A.eval x)) - B.eval x)

private theorem exp_le_of_le {x y : Real} (h : x ≤ y) : exp x ≤ exp y := by
  rcases lt_total x y with hlt | heq | hgt
  · exact le_of_lt (exp_lt hlt)
  · rw [heq]; exact le_refl _
  · exact absurd (lt_of_lt_of_le hgt h) (fun hh => (ne_of_lt hh) rfl)

/-- **The obligation IS a growth comparison.** Stated as an `Iff` on purpose: nothing here
discharges `SignHardCase`, and a theorem whose bare conclusion were `SignHardCase` would read to the
obligation ledger — correctly — as a discharger of an **open** row, and would silently break that
gate's canary 5, whose specimen is literally `SignHardCase`. -/
theorem signHardCase_iff_compareExpExpPos : SignHardCase ↔ SignCompareExpExpPos := by
  constructor
  · intro h A B X₀ hX₀ hB
    rcases h A B X₀ hX₀ hB with ⟨X₁, hX₁, hp⟩ | ⟨X₁, hX₁, hn⟩
    · obtain ⟨X, hX, h0, h1⟩ := two_bounds' hX₀ hX₁
      refine Or.inl ⟨X, hX, fun x hx => ?_⟩
      have hBx : 0 < B.eval x := hB x (le_trans h0 hx)
      have v : 0 < exp (A.eval x) - log (B.eval x) := hp x (le_trans h1 hx)
      have w := exp_lt (lt_of_sub_pos v)
      rw [exp_log hBx] at w
      exact sub_pos_of_lt w
    · obtain ⟨X, hX, h0, h1⟩ := two_bounds' hX₀ hX₁
      refine Or.inr ⟨X, hX, fun x hx => ?_⟩
      have hBx : 0 < B.eval x := hB x (le_trans h0 hx)
      have v : exp (A.eval x) - log (B.eval x) ≤ 0 := hn x (le_trans h1 hx)
      have w := exp_le_of_le (le_of_sub_nonpos v)
      rw [exp_log hBx] at w
      exact sub_nonpos_of_le w
  · intro h A B X₀ hX₀ hB
    rcases h A B X₀ hX₀ hB with ⟨X₁, hX₁, hgt⟩ | ⟨X₁, hX₁, hle⟩
    · obtain ⟨X, hX, h0, h1⟩ := two_bounds' hX₀ hX₁
      refine Or.inl ⟨X, hX, fun x hx => ?_⟩
      have hBx : 0 < B.eval x := hB x (le_trans h0 hx)
      have v : 0 < exp (exp (A.eval x)) - B.eval x := hgt x (le_trans h1 hx)
      have hlog : log (B.eval x) < exp (A.eval x) := by
        have w := log_lt_log hBx (lt_of_sub_pos v)
        rwa [log_exp] at w
      exact sub_pos_of_lt hlog
    · refine Or.inr ⟨X₁, hX₁, fun x hx => ?_⟩
      have v : exp (exp (A.eval x)) - B.eval x ≤ 0 := hle x hx
      have hlog : exp (A.eval x) ≤ log (B.eval x) := by
        have w := log_le_log (exp_pos (exp (A.eval x))) (le_of_sub_nonpos v)
        rwa [log_exp] at w
      exact sub_nonpos_of_le hlog

/-- The comparison with the positivity **dropped** — strictly stronger, and the hypothesis-free shape
a Hardy-field argument would naturally supply. -/
def SignCompareExpExp : Prop :=
  ∀ A B : EMLTree, EvSign (fun x => exp (exp (A.eval x)) - B.eval x)

theorem compareExpExpPos_of_compareExpExp (h : SignCompareExpExp) : SignCompareExpExpPos := by
  intro A B _ _ _
  exact h A B

/-- Full pairwise comparability of EML germs is more than the reduction needs, but it does imply it —
`exp ∘ exp ∘ A` is a tree, so the required comparison is a special case. -/
theorem treeComparable_imp
    (h : ∀ s t : EMLTree, EvSign (fun x => s.eval x - t.eval x)) : SignCompareExpExp := by
  intro A B
  rcases h (EMLTree.eml (EMLTree.eml A (EMLTree.const 1)) (EMLTree.const 1)) B with
    ⟨X, hX, hp⟩ | ⟨X, hX, hn⟩
  · refine Or.inl ⟨X, hX, fun x hx => ?_⟩
    have v : 0 < (EMLTree.eml (EMLTree.eml A (EMLTree.const 1)) (EMLTree.const 1)).eval x
        - B.eval x := hp x hx
    rw [expExpTree_eval] at v
    exact v
  · refine Or.inr ⟨X, hX, fun x hx => ?_⟩
    have v : (EMLTree.eml (EMLTree.eml A (EMLTree.const 1)) (EMLTree.const 1)).eval x
        - B.eval x ≤ 0 := hn x hx
    rw [expExpTree_eval] at v
    exact v

end MachLib
