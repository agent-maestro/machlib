import MachLib.PfaffianChain

/-!
# The order-2 chain format (general Pfaffian explicit bound, base instantiation)

The general base's explicit bound is `Ngen(order, deg p, α)` with `α` the chain's Khovanskii format —
the degrees of its relation polynomials (design §3′). At order 2 the "max over `Fin n` of relation
degree" that `α` denotes is simply `Nat.max` of the two relations, so the format and its discharge
lemmas (feeding the degree towers `degreeX/Y_chainTotalDeriv_le_format`) are clean and Mathlib-free.
-/

open MachLib.MultiPolyMod

namespace MachLib.PfaffianChainMod.PfaffianFn

/-- The order-2 `degreeX` format: `max` of the two relations' `degreeX`. -/
def formatX2 (c : PfaffianChain 2) : Nat :=
  Nat.max (MultiPoly.degreeX (c.relations ⟨0, by omega⟩))
          (MultiPoly.degreeX (c.relations ⟨1, by omega⟩))

/-- The order-2 `degreeY i` format at level `i`: `max` of the two relations' `degreeY i`. -/
def formatY2 (c : PfaffianChain 2) (i : Fin 2) : Nat :=
  Nat.max (MultiPoly.degreeY i (c.relations ⟨0, by omega⟩))
          (MultiPoly.degreeY i (c.relations ⟨1, by omega⟩))

/-- Every relation's `degreeX` is `≤ formatX2` — the `h_fmt` the degree towers consume, at order 2. -/
theorem relations_degreeX_le_formatX2 (c : PfaffianChain 2) :
    ∀ k : Fin 2, MultiPoly.degreeX (c.relations k) ≤ formatX2 c
  | ⟨0, _⟩ => Nat.le_max_left _ _
  | ⟨1, _⟩ => Nat.le_max_right _ _

/-- Every relation's `degreeY i` is `≤ formatY2 c i` — the `h_fmt` the degree towers consume, per level. -/
theorem relations_degreeY_le_formatY2 (c : PfaffianChain 2) (i : Fin 2) :
    ∀ k : Fin 2, MultiPoly.degreeY i (c.relations k) ≤ formatY2 c i
  | ⟨0, _⟩ => Nat.le_max_left _ _
  | ⟨1, _⟩ => Nat.le_max_right _ _

end MachLib.PfaffianChainMod.PfaffianFn
