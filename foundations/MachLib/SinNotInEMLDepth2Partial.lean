import MachLib.Trig
import MachLib.EML
import MachLib.SinNotInEML

/-!
# `sin ∉ EML_k` partial extensions toward depth ≤ 2

The full `sin_not_in_eml_depth_le_2` theorem requires 32 sub-cases of
depth-2 enumeration (4 ceml shapes for `t1` times 4 ceml shapes for `t2`
on the (depth-1, depth-1) row alone). This file ships the structurally
clean *general* lemma that handles a wide family of those cases plus
useful corollaries, deferring the full enumeration to a future dedicated
artifact.

The general lemma:

`sin_not_in_eml_when_t2_zero_at_zero` — for any depth `n` tree
`.eml t1 t2`, if `t2.eval 0 = 0`, then the tree's evaluation does not
equal `Real.sin` globally. Closure at `x = 0` via `exp_pos`:
`exp(t1.eval 0) = sin 0 = 0` is impossible.

Corollaries cover the `t2 = .var` sub-cases of depth ≤ 2, ≤ 3, etc.
without further work.

This is partial relative to `sin_not_in_eml_depth_le_2` but the partial
result is itself a clean positive theorem worth landing.
-/

namespace MachLib

open Real

/-- General lemma: if the second argument of an outer `.eml` evaluates
to `0` at `x = 0`, then the tree cannot equal `sin` globally.

Proof: at `x = 0`, the outer eval becomes `exp(t1.eval 0) - log 0 =
exp(t1.eval 0)` (since `log 0 = 0` by MachLib convention). But
`sin 0 = 0`, so `exp(t1.eval 0) = 0` is forced. Contradicts `exp_pos`. -/
theorem sin_not_in_eml_when_t2_zero_at_zero (t1 t2 : EMLTree)
    (h : t2.eval 0 = 0) :
    ¬ (∀ x : Real, (EMLTree.eml t1 t2).eval x = Real.sin x) := by
  intro hsin
  have h0 := hsin 0
  simp only [EMLTree.eval, sin_zero] at h0
  -- h0 : exp (t1.eval 0) - log (t2.eval 0) = 0
  rw [h, log_zero, sub_zero] at h0
  -- h0 : exp (t1.eval 0) = 0
  have hpos : 0 < exp (t1.eval 0) := exp_pos _
  rw [h0] at hpos
  exact lt_irrefl_ax 0 hpos

/-- Corollary: the `t2 = .var` family at any depth is dispatched. -/
theorem sin_not_in_eml_when_t2_var (t1 : EMLTree) :
    ¬ (∀ x : Real, (EMLTree.eml t1 .var).eval x = Real.sin x) := by
  apply sin_not_in_eml_when_t2_zero_at_zero t1 .var
  rfl  -- .var.eval 0 = 0 by definition

/-- **Cleanly closes 4 of the 32 depth-2 cases for `sin_not_in_eml_depth_le_2`:**
when the outer tree is `.eml t1 .var` with `t1` of depth 1, the
`sin_not_in_eml_when_t2_var` corollary applies. The other 28 cases
remain as a future bounded artifact. -/
theorem sin_not_in_eml_depth_2_with_t2_var (t1 : EMLTree) (ht1 : t1.depth ≤ 1) :
    let t : EMLTree := .eml t1 .var
    t.depth ≤ 2 ∧ ¬ (∀ x : Real, t.eval x = Real.sin x) := by
  refine ⟨?_, sin_not_in_eml_when_t2_var t1⟩
  simp only [EMLTree.depth]
  have h := Nat.le_max_left t1.depth 0
  omega

end MachLib
