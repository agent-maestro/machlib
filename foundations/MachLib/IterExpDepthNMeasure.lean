import MachLib.LexProd
import MachLib.ChainExp2Reducer

/-!
# The depth-generic nested-measure backbone (∀N)

The depth-2 and depth-3 Khovanskii capstones each pull a MultiPoly through a **nested lexicographic
`Nat` measure** and cite a hand-built well-foundedness keystone for that specific arity
(`natTripleLex_wf` for depth 2, `natQuadLex_wf` for depth 3). Those are the `n = 2, 3` instances of a
single family. To run the tower's induction on depth we need that family *uniformly* — the measure
codomain, its order, and its well-foundedness, all indexed by depth and proven for **every** `n`.

This file supplies exactly that backbone, and nothing analytic — it is pure order theory over `Nat`,
so it closes cleanly from `LexProd.lexProd_wf` by induction on depth:

* `NestedNat n` — the codomain of the depth-`(n+2)` canonical measure: an `(n+1)`-deep right-nested
  `Nat` product (`NestedNat 0 = Nat`; `NestedNat (k+1) = Nat × NestedNat k`).
* `nestedOrder n` — the nested lexicographic order on it. Definitionally, `nestedOrder 2` is exactly the
  depth-2 `ChainExp2Reducer.nestedLT`, and `nestedOrder 3` its depth-3 lex core — so the concrete
  measures are the `n = 2, 3` slices of this family.
* `nestedOrder_wf n` — **well-founded for every `n`**, the depth-generic keystone. `natPairLex_wf`,
  `natTripleLex_wf`, `natQuadLex_wf` are its `n = 1, 2, 3` instances.
* `nestedOrder_of_fst` / `nestedOrder_of_snd` — the two descent-lifting lemmas the capstone's arms need
  (drop the top component, or tie it and drop the tail), generic in depth.

No `sorry`; no analytic axiom — this is the well-founded skeleton the ∀N descent will hang on.
-/

namespace MachLib.IterExpDepthN

/-- `NestedNat n`: an `(n+1)`-deep right-nested `Nat` product — the codomain of the depth-`(n+2)`
canonical measure. Reducible so `NestedNat 0` is transparently `Nat` (base-case `<` synthesises). -/
@[reducible] def NestedNat : Nat → Type
  | 0 => Nat
  | k + 1 => Nat × NestedNat k

/-- The nested lexicographic order on `NestedNat n`: plain `<` at the base, `lexProd` of `<` with the
tail order at each successor. -/
def nestedOrder : (n : Nat) → NestedNat n → NestedNat n → Prop
  | 0 => fun a b => a < b
  | k + 1 => LexProd.lexProd (· < ·) (nestedOrder k)

/-- **Well-founded at every depth.** Induction on `n`: base is `Nat`'s `<`, the successor step is the
`lexProd` well-foundedness combinator applied to the inductive hypothesis. The depth-generic keystone —
`natPairLex_wf` / `natTripleLex_wf` / `natQuadLex_wf` are its `n = 1, 2, 3` instances. -/
theorem nestedOrder_wf : ∀ n, WellFounded (nestedOrder n) := by
  intro n
  induction n with
  | zero => simp only [nestedOrder]; exact Nat.lt_wfRel.wf
  | succ k ih => simp only [nestedOrder]; exact LexProd.lexProd_wf Nat.lt_wfRel.wf ih

/-- Descent by strictly dropping the top component (generic `lexProd`-of-first). -/
theorem nestedOrder_of_fst {n : Nat} {a b : NestedNat (n + 1)} (h : a.1 < b.1) :
    nestedOrder (n + 1) a b := by
  simp only [nestedOrder, LexProd.lexProd]; exact Or.inl h

/-- Descent by tying the top component and dropping the tail (generic `lexProd_of_snd`). -/
theorem nestedOrder_of_snd {n : Nat} {a b : NestedNat (n + 1)}
    (h1 : a.1 = b.1) (h2 : nestedOrder n a.2 b.2) : nestedOrder (n + 1) a b := by
  simp only [nestedOrder]; exact LexProd.lexProd_of_snd h1 h2

end MachLib.IterExpDepthN
