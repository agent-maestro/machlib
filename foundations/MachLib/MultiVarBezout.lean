import MachLib.MultiVar

/-!
# Bezout skeleton for `MultiVar 2` — the multivariate counting principle (Gate 2d, Rung 0 Layer B)

The go/no-go question for the multivariate Khovanskii bound (scoping doc §4): *does solution-counting
work in the Mathlib-free `MachLib.Real` model at all, and where does the difficulty escalate?*

This file answers the first half: the **combinatorial core of Bezout is provable in-model**. A system
`{p(x,y)=0, q(x,y)=0}` is counted by decomposing its solution set into **vertical fibers** (grouped by
the `x`-coordinate): if there are `≤ A` fibers and each fiber holds `≤ B` solutions, the total is
`≤ A·B`. That reduction — number-of-fibers × fiber-size — *is* the shape of the Bezout bound
(`A ≈ deg`, `B ≈ deg`), and it is pure, decidability-free list arithmetic.

**What is proven here** (`bezout_skeleton`): the reduction, fully, no Mathlib, no sorry.

**What is NOT here** (the pinned analytic obligations, = the escalation point — see the FINDINGS section
of `roadmap/multivariate-khovanskii-gate2d-scoping.md`):
1. *Producing the fibration with `≤ A ≈ deg p · deg q` fibers* — the `x`-coordinates of common zeros are
   roots of the **resultant** `Res_y(p,q) ∈ ℝ[x]`; bounding their count needs the resultant construction
   plus monogate's single-variable polynomial root count. **Not built.**
2. *Bounding each fiber by `B ≈ deg`* — on a fixed vertical line `x = x₀`, common solutions are common
   roots of the univariate `p(x₀,·), q(x₀,·)`; needs substitution `MultiVar 2 → (univariate)` and the
   single-variable count. **Partially reachable** via the existing `ExpPoly`/`Poly` root count.

The skeleton makes the go/no-go crisp: the *counting principle* is sound and in-model; the remaining work
is the *elimination theory* (resultant) feeding it — a bounded, identified target, not an open gate.
-/

namespace MachLib
namespace MultiVarMod

/-- The concatenated length of a list of vertical fibers is `≤ (#fibers)·B` when each fiber holds `≤ B`
solutions. Pure `List`/`Nat` induction (`(f::fs).flatMap g = g f ++ fs.flatMap g`), hand-rolled — no
Mathlib `length_flatMap` / `sum_le_card_nsmul`. -/
theorem length_flatMap_le {β : Type} (B : Nat) :
    ∀ fibers : List (β × List (Fin 2 → Real)),
      (∀ f ∈ fibers, f.2.length ≤ B) →
      (fibers.flatMap (fun f => f.2)).length ≤ fibers.length * B
  | [], _ => by simp
  | f :: fs, h => by
      have h0 : f.2.length ≤ B := h f (List.mem_cons_self f fs)
      have hrest := length_flatMap_le B fs (fun x hx => h x (List.mem_cons_of_mem f hx))
      show (f.2 ++ fs.flatMap (fun f => f.2)).length ≤ (fs.length + 1) * B
      rw [List.length_append, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add h0 hrest) (by omega)

/-- **The Bezout skeleton for `MultiVar 2`.** A solution set presented as a flat concatenation of
vertical fibers `fibers` (each `f.2` a list of solutions sharing an `x`-coordinate `f.1`): if there are
`≤ A` fibers and each holds `≤ B` solutions, the total solution count is `≤ A·B`. This is the
number-of-fibers × fiber-size reduction that gives Bezout its `deg·deg` shape — proven purely, in-model,
Mathlib-free. The analytic content (`A ≈ deg` via the resultant, `B ≈ deg` via the univariate fiber
count) lives in the hypotheses `hA`, `hB`, and the fibration `sols = fibers.flatMap _`. -/
theorem bezout_skeleton {β : Type}
    (fibers : List (β × List (Fin 2 → Real))) (A B : Nat)
    (hA : fibers.length ≤ A) (hB : ∀ f ∈ fibers, f.2.length ≤ B) :
    (fibers.flatMap (fun f => f.2)).length ≤ A * B :=
  Nat.le_trans (length_flatMap_le B fibers hB) (Nat.mul_le_mul hA (Nat.le_refl B))

/-- Restatement tying the skeleton to an explicit system `{p = 0, q = 0}`: any solution list that is a
vertical fibration with `≤ A` fibers of size `≤ B` has `≤ A·B` elements. (`p`, `q`, and the
"every listed point is a common zero" hypothesis are carried to fix the intended reading; the count
itself is the combinatorial skeleton — the *bound's shape* is Bezout, the *analytic obligations* are
`hA`/`hB`, per this file's header.) -/
theorem multiVar2_system_count {β : Type} (p q : MultiVar 2)
    (fibers : List (β × List (Fin 2 → Real))) (A B : Nat)
    (hA : fibers.length ≤ A) (hB : ∀ f ∈ fibers, f.2.length ≤ B)
    (sols : List (Fin 2 → Real)) (hpart : sols = fibers.flatMap (fun f => f.2))
    (_hsol : ∀ s ∈ sols, MultiVar.eval p s = 0 ∧ MultiVar.eval q s = 0) :
    sols.length ≤ A * B := by
  rw [hpart]; exact bezout_skeleton fibers A B hA hB

end MultiVarMod
end MachLib
