import MachLib.Exp
import MachLib.Log
import MachLib.EML
import MachLib.EMLHierarchy
import MachLib.ExpExpNotInEML1

/-!
# Strict hierarchy `EML_k ⊊ EML_{k+1}` via iterated exp (Phase E)

Phase E of the Pfaffian programme. Ships:

1. **`iter_exp` recursive definition**: `iter_exp k x = exp ∘ ... ∘
   exp x` (k applications of exp).

2. **EML membership**: `iter_exp k ∈ EML_k`, witnessed by the
   recursively built tree `eml(eml(... eml(var, const 1) ..., const
   1), const 1)` with k levels of `eml(_, const 1)`.

3. **Parameterized strict hierarchy**:
   `strict_eml_via_iter_exp k h : EML_k ⊊ EML_{k+1}` where `h :
   ¬ InEMLDepth (iter_exp (k+1)) k`.

4. **Concrete strict hierarchy for k = 0, 1, 2**:
   - `strict_eml_zero_one`: EML_0 ⊊ EML_1 (already in
     EMLHierarchy.lean as `strict_eml_zero_subset_eml_one`; we
     repackage via `iter_exp` here).
   - `strict_eml_one_two`: EML_1 ⊊ EML_2 (already as
     `strict_eml_one_subset_eml_two`; repackaged).
   - For k = 2 and beyond, the hypothesis `iter_exp (k+1) ∉ EML_k`
     requires depth-k case enumeration (~32 cases for k = 2) and
     is deferred to a focused follow-up artifact.

**Honest scope:** The general `∀ k, EML_k ⊊ EML_{k+1}` is NOT proven
here. It requires either:
- Per-k depth enumeration (the depth-2 sin barrier template applies
  to `exp_exp_exp_not_in_eml_2`, ~32 cases per depth).
- Pfaffian-order argument (would require additional axioms about
  function-intrinsic minimum Pfaffian order, beyond Phase A's
  chain-extrinsic axioms).

The Phase E deliverable is the EML embedding for `iter_exp` plus the
parameterized strict-hierarchy theorem — the building blocks that
per-k closures plug into.

No Mathlib dependency. Zero-Mathlib gate stays PASS.
-/

namespace MachLib

open Real

/-! ## `iter_exp` and its EML tree -/

/-- `iter_exp k x = exp(exp(...(exp x)))`, k applications of exp.
`iter_exp 0 = id`. -/
noncomputable def iter_exp : Nat → Real → Real
  | 0, x => x
  | k + 1, x => Real.exp (iter_exp k x)

/-- The EML tree realizing `iter_exp k`:
`eml(eml(... eml(var, const 1) ..., const 1), const 1)` with k
levels of `eml(_, const 1)`. -/
noncomputable def iter_exp_tree : Nat → EMLTree
  | 0 => EMLTree.var
  | k + 1 => EMLTree.eml (iter_exp_tree k) (EMLTree.const 1)

/-- Tree depth equals iteration count. -/
theorem iter_exp_tree_depth (k : Nat) : (iter_exp_tree k).depth = k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have h : iter_exp_tree (n + 1) =
              EMLTree.eml (iter_exp_tree n) (EMLTree.const 1) := rfl
    rw [h]
    simp only [EMLTree.depth, ih]
    -- Goal: 1 + max n 0 = n + 1.
    omega

/-- Tree evaluation gives `iter_exp`. -/
theorem iter_exp_tree_eval (k : Nat) (x : Real) :
    (iter_exp_tree k).eval x = iter_exp k x := by
  induction k with
  | zero => rfl
  | succ n ih =>
    have htree : iter_exp_tree (n + 1) =
                  EMLTree.eml (iter_exp_tree n) (EMLTree.const 1) := rfl
    have hiter : iter_exp (n + 1) x = Real.exp (iter_exp n x) := rfl
    rw [htree, hiter]
    -- (eml t1 t2).eval x = exp (t1.eval x) - log (t2.eval x).
    -- t1 = iter_exp_tree n, t2 = const 1.
    -- t1.eval x = iter_exp n x (by ih).
    -- t2.eval x = 1.
    -- log 1 = 0.
    simp only [EMLTree.eval, ih]
    -- Goal: exp (iter_exp n x) - log 1 = exp (iter_exp n x).
    rw [log_one, sub_zero]

/-- `iter_exp k ∈ EML_k`. -/
theorem iter_exp_in_eml (k : Nat) : InEMLDepth (iter_exp k) k := by
  refine ⟨iter_exp_tree k, ?_, ?_⟩
  · rw [iter_exp_tree_depth]; exact Nat.le_refl _
  · intro x
    exact (iter_exp_tree_eval k x).symm

/-! ## Parameterized strict hierarchy -/

/-- **Parameterized strict containment** `EML_k ⊊ EML_{k+1}`. Given
the hypothesis that `iter_exp (k+1) ∉ EML_k`, this is the strict
containment with `iter_exp (k+1)` as witness. -/
theorem strict_eml_via_iter_exp (k : Nat)
    (h : ¬ InEMLDepth (iter_exp (k + 1)) k) :
    (∀ f : Real → Real, InEMLDepth f k → InEMLDepth f (k + 1)) ∧
    (∃ f : Real → Real, InEMLDepth f (k + 1) ∧ ¬ InEMLDepth f k) := by
  refine ⟨?_, ⟨iter_exp (k + 1), iter_exp_in_eml (k + 1), h⟩⟩
  intro f hf
  exact in_eml_depth_mono hf (by omega)

/-! ## Concrete strict containments for small k -/

/-- **`EML_0 ⊊ EML_1`** via `iter_exp 1 = exp`. -/
theorem strict_eml_zero_one_via_iter_exp :
    (∀ f : Real → Real, InEMLDepth f 0 → InEMLDepth f 1) ∧
    (∃ f : Real → Real, InEMLDepth f 1 ∧ ¬ InEMLDepth f 0) := by
  have h : ¬ InEMLDepth (iter_exp 1) 0 := by
    intro hexp
    have hexp' : InEMLDepth Real.exp 0 := by
      obtain ⟨t, htd, heval⟩ := hexp
      refine ⟨t, htd, ?_⟩
      intro x
      -- iter_exp 1 x = Real.exp x = Real.exp (iter_exp 0 x) = Real.exp x by definition.
      have := heval x
      -- this : iter_exp 1 x = t.eval x. But iter_exp 1 x = Real.exp x.
      exact this
    exact exp_not_in_eml_0 hexp'
  exact strict_eml_via_iter_exp 0 h

/-- **`EML_1 ⊊ EML_2`** via `iter_exp 2 = exp ∘ exp`. -/
theorem strict_eml_one_two_via_iter_exp :
    (∀ f : Real → Real, InEMLDepth f 1 → InEMLDepth f 2) ∧
    (∃ f : Real → Real, InEMLDepth f 2 ∧ ¬ InEMLDepth f 1) := by
  have h : ¬ InEMLDepth (iter_exp 2) 1 := by
    intro h_in
    have h_in' : InEMLDepth (fun x : Real => Real.exp (Real.exp x)) 1 := by
      obtain ⟨t, htd, heval⟩ := h_in
      refine ⟨t, htd, ?_⟩
      intro x
      -- iter_exp 2 x = Real.exp (Real.exp x) by definition.
      exact heval x
    exact exp_exp_not_in_eml_1 h_in'
  exact strict_eml_via_iter_exp 1 h

end MachLib
