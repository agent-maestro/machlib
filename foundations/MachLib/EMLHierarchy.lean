import MachLib.Exp
import MachLib.Log
import MachLib.EML
import MachLib.SinNotInEML
import MachLib.CosNotInEML

/-!
# EML depth hierarchy — `EML_k ⊊ EML_{k+1}` for small k

A depth class is non-trivial only if it strictly contains the previous one.
This file establishes:

- `EML_0 ⊊ EML_1`, witnessed by `Real.exp`. Concretely:
  * `exp_in_eml_1`: `Real.exp = eml(var, const 1).eval`, depth 1.
  * `exp_not_in_eml_0`: no depth-0 tree's evaluation equals `Real.exp`
    everywhere (const can't be non-constant; var fails at x = 0).
  * `strict_eml_zero_subset_eml_one`: forward inclusion (depth-0 trees are
    depth-1 trees) plus the `exp` witness.

- `EML_1 ⊊ EML_2`, partial:
  * `exp_exp_in_eml_2`: `exp ∘ exp = eml(eml(var, const 1), const 1).eval`,
    depth 2.
  * The non-membership direction `exp(exp x) ∉ EML_1` follows the same
    case-analysis pattern as `sin_not_in_eml_depth_le_1` but with `exp` as
    target instead of `sin`. Recorded as a future bounded artifact in this
    file's docstring; not stated as a `sorry`'d theorem (the discipline is
    to land positive theorems only).

This file does not depend on Mathlib. The zero-Mathlib gate continues to
pass after this addition.
-/

namespace MachLib

open Real

-- ===================================================================
-- The depth-class membership predicate
-- ===================================================================

/-- `InEMLDepth f k` says `f : Real → Real` is realized by some EML tree of
depth at most `k`. This is the predicate version of the depth class
`EML_k`. -/
def InEMLDepth (f : Real → Real) (k : Nat) : Prop :=
  ∃ t : EMLTree, t.depth ≤ k ∧ ∀ x : Real, f x = t.eval x

/-- Trivial monotonicity: a function in `EML_k` is in `EML_{k+m}` for any
`m`. Direct consequence of `Nat` order. -/
theorem in_eml_depth_mono {f : Real → Real} {k m : Nat}
    (h : InEMLDepth f k) (hle : k ≤ m) : InEMLDepth f m := by
  obtain ⟨t, htd, hfx⟩ := h
  exact ⟨t, Nat.le_trans htd hle, hfx⟩

-- ===================================================================
-- EML_0 ⊊ EML_1 : exp is the witness
-- ===================================================================

/-- `exp(x) = (eml var (const 1)).eval x`. Depth 1. -/
theorem exp_in_eml_1 : InEMLDepth Real.exp 1 := by
  refine ⟨EMLTree.eml .var (.const 1), ?_, ?_⟩
  · simp [EMLTree.depth]
  · intro x
    simp [EMLTree.eval, log_one, sub_zero]

/-- `Real.exp` is not in `EML_0`: depth-0 trees are constants or the
identity, neither of which equals `exp` globally. -/
theorem exp_not_in_eml_0 : ¬ InEMLDepth Real.exp 0 := by
  intro ⟨t, htd, hexp⟩
  cases t with
  | const c =>
    -- exp would be constant c, but exp 0 = 1, exp 1 > 1 (one_lt_exp_one).
    have h0 := hexp 0
    have h1 := hexp 1
    simp only [EMLTree.eval] at h0 h1
    -- h0 : Real.exp 0 = c, h1 : Real.exp 1 = c
    rw [exp_zero] at h0
    -- h0 : 1 = c
    rw [← h0] at h1
    -- h1 : exp 1 = 1
    have h_gt : (1 : Real) < exp 1 := one_lt_exp_one
    rw [h1] at h_gt
    -- h_gt : 1 < 1
    exact lt_irrefl_ax 1 h_gt
  | var =>
    -- exp would equal id, but exp 0 = 1 ≠ 0.
    have h0 := hexp 0
    simp only [EMLTree.eval] at h0
    -- h0 : Real.exp 0 = 0
    rw [exp_zero] at h0
    -- h0 : 1 = 0
    exact zero_ne_one_ax h0.symm
  | eml _ _ =>
    -- An eml node has depth ≥ 1, contradicting htd.
    simp only [EMLTree.depth] at htd
    omega

/-- **`EML_0 ⊊ EML_1`.** Forward inclusion plus the `exp` witness for strict
containment. -/
theorem strict_eml_zero_subset_eml_one :
    (∀ f : Real → Real, InEMLDepth f 0 → InEMLDepth f 1) ∧
    (∃ f : Real → Real, InEMLDepth f 1 ∧ ¬ InEMLDepth f 0) := by
  refine ⟨?_, ⟨Real.exp, exp_in_eml_1, exp_not_in_eml_0⟩⟩
  intro f hf
  exact in_eml_depth_mono hf (by omega)

-- ===================================================================
-- EML_1 ⊊ EML_2 : exp(exp x) is the candidate witness (easy direction)
-- ===================================================================

/-- `(exp ∘ exp) x = (eml (eml var (const 1)) (const 1)).eval x`. Depth 2.

Uses `eml(t, const 1) = exp(t.eval x) - log 1 = exp(t.eval x)` twice. -/
theorem exp_exp_in_eml_2 :
    InEMLDepth (fun x : Real => Real.exp (Real.exp x)) 2 := by
  refine ⟨EMLTree.eml (EMLTree.eml .var (.const 1)) (.const 1), ?_, ?_⟩
  · simp [EMLTree.depth]
  · intro x
    simp [EMLTree.eval, log_one, sub_zero]

/-- Forward inclusion `EML_1 ⊆ EML_2`. -/
theorem eml_one_subset_eml_two :
    ∀ f : Real → Real, InEMLDepth f 1 → InEMLDepth f 2 := by
  intro f hf
  exact in_eml_depth_mono hf (by omega)

/-! ### `EML_1 ⊊ EML_2` strict direction — future bounded artifact

The strict-containment witness for `EML_1 ⊊ EML_2` is `fun x ↦ exp(exp x)`.
The easy direction (the function is in `EML_2`) is `exp_exp_in_eml_2`
above. The non-membership direction — `¬ InEMLDepth (fun x ↦ exp(exp x))
1` — follows the same case-analysis pattern as `sin_not_in_eml_depth_le_1`
and `cos_not_in_eml_depth_le_1`, with the six depth-≤-1 grammar shapes
each closed by two-point evaluation. The argument needs:

- `exp 1 ≠ Real.exp (Real.exp 1)`, i.e., `exp e ≠ e`, derivable from
  `e > 1` plus strict `exp_lt`: `exp e > exp 1 = e`, so `exp e ≠ e`.

That gives the contradiction for the `var`, `eml(var, var)`, and
`eml(const c, var)` cases. The `eml(var, const c)` case needs one
additional step on `2*e - 1 ≠ exp e`, which follows from `exp e > e`
and `2 * e - 1 < 2 * e < e * exp(1) = exp(e) * (1)` — bounds are tight
but doable.

This is recorded for the next bounded research artifact. It is not stated
as a `sorry`'d theorem here because publishing a `sorry`'d placeholder
would tick the public Lean sorry count without shipping a positive
theorem. -/

end MachLib
