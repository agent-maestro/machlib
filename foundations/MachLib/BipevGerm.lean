import MachLib.BipevNonzeroCoeff

/-!
# The germ form

`proper_relation_impossible` is stated for `S` *literally* `pev P · (1/pev Q)`. Every place in this
arc that mentioned the gap said a germ merely agreeing with it on a tail would be carried by
`hasDerivAt_of_agrees_on_tail` — the derivative transfer built in `BipevTail`.

**It is not needed.** `EvRel S Ls` mentions `S` exactly once, as `exp (S x)`, pointwise. Two
functions that agree on a tail therefore have the same relations, by intersecting two tails and
nothing else. The derivative never enters, because the differentiation in the argument happens
*after* the relation has been moved onto the literal rational function, where `hasDerivAt_ratFn`
already applies.

That is the **fourth** time in this arc a step was predicted to need a heavier tool than it did, and
the first where the predicted tool turned out to be unnecessary rather than merely oversized.
`hasDerivAt_of_agrees_on_tail` remains a correct lemma; the arc simply does not consume it.
-/

namespace MachLib

open Real

/-- Two functions agree on a tail. The relation form of `EvZeroF`, which is the `g = 0` case. -/
def EvEqF (f g : Real → Real) : Prop := ∃ X : Real, 1 ≤ X ∧ ∀ x : Real, X ≤ x → f x = g x

/-- **Relations only see `S` pointwise.** One tail intersection; no derivative, no continuity. -/
theorem evRel_congr {S T : Real → Real} {Ls : List (List Real)}
    (h : EvEqF S T) (hrel : EvRel S Ls) : EvRel T Ls := by
  obtain ⟨X₁, hX₁, hEq⟩ := h
  obtain ⟨X₂, hX₂, hR⟩ := hrel
  obtain ⟨X, hX, hXa, hXb⟩ := two_bounds' hX₁ hX₂
  refine ⟨X, hX, fun x hx => ?_⟩
  rw [← hEq x (le_trans hXa hx)]
  exact hR x (le_trans hXb hx)

/-- Properness transfers with it: the second clause never mentions `S`. -/
theorem properRel_congr {S T : Real → Real} {Ls : List (List Real)}
    (h : EvEqF S T) (hrel : ProperRel S Ls) : ProperRel T Ls :=
  ⟨evRel_congr h hrel.1, hrel.2⟩

/-- **The germ form of the top-level theorem.** No relation holds eventually for *any* function
agreeing with `P/Q` on a tail — the germ, not the formula, is what the statement is about. -/
theorem germ_relation_impossible {P Q q : List Real}
    (hq : PIrred q)
    (hchar : ∀ r : Nat, DerivCoprime q r)
    (hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q)))
    (hPd : ¬ Pdvd q P) (hPn : PNormal P)
    (hQn : PNormal Q) (hQne : Q ≠ []) (hQd : Pdvd q Q)
    (hQz : ¬ EvZeroF (pev Q))
    {S : Real → Real} {Ls : List (List Real)}
    (hagree : EvEqF S (fun y => pev P y * (1 / pev Q y)))
    (hrel : ProperRel S Ls) :
    False :=
  proper_relation_impossible hq hchar hcharN hPd hPn hQn hQne hQd hQz
    (properRel_congr hagree hrel)

end MachLib
