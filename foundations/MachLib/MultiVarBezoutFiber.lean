import MachLib.MultiVarBezout
import MachLib.MultiVarToPoly

/-!
# Consolidated polynomial Bezout for `MultiVar 2`, modulo the resultant (Gate 2d, Rung 0.5)

Stitches the two proven halves — `bezout_skeleton` (the fibers × fiber-size counting core) and
`fiber_count` (each fiber `≤ deg`) — into a single statement, so the whole polynomial-Bezout bound
reduces to **one** named obligation: producing the fibration (the resultant, obligation A).

`bezout_of_fibration`: given a fibration of the solution set by `x`-coordinate — `≤ A` fibers, each a
list of `y`-values solving `p = 0` on that vertical line, each line non-degenerate (`p` not vanishing
identically on it) — the total solution count is `≤ A · deg_y p`. The `y`-value form (rather than
solution-point form) lets `fiber_count` apply directly, no `Nodup`-of-map bookkeeping.

**What remains for full polynomial Bezout is now a single hole:** obligation A = *"the `x`-coordinates of
common zeros of `{p, q}` are covered by `≤ deg·deg` values"* — the roots of the resultant `Res_y(p,q)`.
Feed such a fibration to `bezout_of_fibration` and Bezout closes. (The bound `A · deg_y` is the effective
— not sharp — count: `A = deg(Res_y) ≈ deg·deg`, so `A · deg_y` is a `deg`-polynomial ceiling, which is
all a Khovanskii-style effective bound needs; the sharp `deg·deg` would require multiplicity/projective
refinement.)
-/

namespace MachLib
namespace MultiVarMod

/-- Flat-concatenation length bound, arbitrary payload type (the general form of `length_flatMap_le`). -/
theorem length_flatMap_le' {α γ : Type} (B : Nat) :
    ∀ fibers : List (α × List γ),
      (∀ f ∈ fibers, f.2.length ≤ B) →
      (fibers.flatMap (fun f => f.2)).length ≤ fibers.length * B
  | [], _ => by simp
  | f :: fs, h => by
      have h0 : f.2.length ≤ B := h f (List.mem_cons_self f fs)
      have hrest := length_flatMap_le' B fs (fun x hx => h x (List.mem_cons_of_mem f hx))
      show (f.2 ++ fs.flatMap (fun f => f.2)).length ≤ (fs.length + 1) * B
      rw [List.length_append, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add h0 hrest) (by omega)

/-- **Consolidated polynomial Bezout, modulo the resultant.** A fibration of the solution set of `p = 0`
by `x`-coordinate: `fibers` lists `(x₀, ys)` where each `y ∈ ys` solves `p = 0` on the line `x = x₀`.
If there are `≤ A` fibers, each line is non-degenerate (`p ≢ 0` on it) and its `ys` are `Nodup`
solutions in `(a,b)`, then the total solution count is `≤ A · deg_y p`. Combines `fiber_count` (each
`ys.length ≤ degVar 1 p`) with `length_flatMap_le'` (`Σ ≤ #fibers · B`). The single remaining Bezout
obligation is bounding `A` by the resultant. -/
theorem bezout_of_fibration (p : MultiVar 2) (a b : Real) (hab : a < b)
    (fibers : List (Real × List Real)) (A : Nat) (hA : fibers.length ≤ A)
    (hfib : ∀ f ∈ fibers,
      (∃ t, MultiVar.eval p (fun j => if j = (1 : Fin 2) then t else f.1) ≠ 0)
      ∧ f.2.Nodup
      ∧ (∀ y ∈ f.2, a < y ∧ y < b
          ∧ MultiVar.eval p (fun j => if j = (1 : Fin 2) then y else f.1) = 0)) :
    (fibers.flatMap (fun f => f.2)).length ≤ A * MultiVar.degVar (1 : Fin 2) p := by
  refine Nat.le_trans
    (length_flatMap_le' (MultiVar.degVar (1 : Fin 2) p) fibers ?_)
    (Nat.mul_le_mul hA (Nat.le_refl _))
  intro f hf
  obtain ⟨hne, hnd, hys⟩ := hfib f hf
  exact fiber_count (1 : Fin 2) (fun _ => f.1) p a b hab hne f.2 hnd hys

end MultiVarMod
end MachLib
