import MachLib.RelCoeffsEqCase

/-!
# Trimming a bipoly's trailing zero coefficients

The three readings all want `Cd = As ++ [α]` with `pnorm α ≠ []`. Nothing supplies that: `Cd` arrives
through `hCs : Cs = Cs₀ ++ [Cd]`, and the relation's properness says only that the **germ**
`x ↦ bipev Cd x (e^(S x))` is not eventually zero — not that the top `E`-coefficient survives.

This is `pnorm` one level up, with the coefficient ring's zero test being `pnorm _ = []` rather than
`_ = 0`, and it transcribes from `pconsN`/`pnorm`/`PNormal` the same way `BipolyLead` transcribed
from `PolyMulDegree`.

## Trim before the identity, not after

`bipev (bitrim L) = bipev L` pointwise, so `expCoeffs S (Cs.map bitrim) = expCoeffs S Cs` as a list
of **functions** — and `expCoeffs` is exactly a `map` into functions. The relation, its minimality
and its length all transfer untouched, so the trim can happen at the point `Cs` is chosen, before
`minimal_expRel_identity` is ever invoked.

Doing it afterwards would mean transporting the germ identity through the trim, which is the same
fact plus a derivative: `dbipevExp` would have to be shown insensitive to a trailing zero coefficient
as well. Trimming first costs one evaluation lemma; trimming last would cost two, and the second one
is about a derivative rather than a value.

## The transfer itself is not in this module

`expCoeffs S (Cs.map bitrim) = expCoeffs S Cs` is the statement the caller actually uses, and it is
two lines — but `expCoeffs` mentions `exp`, so stating it here would carry `MachLib.Real.exp` into a
module the algebra spine checks for field axioms only. It lives with the assembly instead, which is
outside the spine anyway. Same trade as `BipolyLead` refusing the `dcoeffs` shape lemmas: **the
layer stays algebraic and the caller pays the one line of transport.**
-/

namespace MachLib

open Real

-- the zero test is classical equality, exactly as in `PolyCanonical`
attribute [local instance] Classical.propDecidable

/-- Prepend a coefficient to an already-trimmed tail. The only place the zero test happens, and it
tests `pnorm A = []` — the coefficient ring's zero, not `Real`'s. -/
noncomputable def biconsN (A : List Real) : List (List Real) → List (List Real)
  | []      => if pnorm A = [] then [] else [A]
  | B :: Bs => A :: B :: Bs

/-- Strip trailing coefficients that are the zero polynomial. -/
noncomputable def bitrim : List (List Real) → List (List Real)
  | []      => []
  | A :: As => biconsN A (bitrim As)

/-- Empty, or the last coefficient is not the zero polynomial. -/
def BiNormal (L : List (List Real)) : Prop :=
  ∀ A : List Real, L.getLast? = some A → pnorm A ≠ []

theorem biNormal_nil : BiNormal [] := by intro A hA; exact absurd hA (by simp)

theorem biconsN_normal (A : List Real) : ∀ t : List (List Real), BiNormal t →
    BiNormal (biconsN A t) := by
  intro t
  cases t with
  | nil =>
      intro _
      by_cases hA : pnorm A = []
      · show BiNormal (if pnorm A = [] then [] else [A])
        rw [if_pos hA]; exact biNormal_nil
      · show BiNormal (if pnorm A = [] then [] else [A])
        rw [if_neg hA]
        intro B hB
        have hBA : A = B := by simpa using hB
        rw [← hBA]; exact hA
  | cons B Bs =>
      intro ht
      show BiNormal (A :: B :: Bs)
      intro C hC
      exact ht C (by simpa using hC)

theorem bitrim_normal : ∀ L : List (List Real), BiNormal (bitrim L) := by
  intro L
  induction L with
  | nil => exact biNormal_nil
  | cons A As ih => exact biconsN_normal A (bitrim As) ih

/-! ## Trimming does not change the value -/

/-- The zero polynomial evaluates to zero. -/
theorem pev_eq_zero_of_pnorm_nil {A : List Real} (h : pnorm A = []) (x : Real) : pev A x = 0 := by
  rw [← pev_pnorm, h]; rfl

theorem bipev_biconsN (A : List Real) : ∀ (L : List (List Real)) (x y : Real),
    bipev (biconsN A L) x y = pev A x + y * bipev L x y := by
  intro L
  cases L with
  | nil =>
      intro x y
      by_cases hA : pnorm A = []
      · show bipev (if pnorm A = [] then [] else [A]) x y = _
        rw [if_pos hA]
        show (0 : Real) = pev A x + y * 0
        rw [pev_eq_zero_of_pnorm_nil hA x]; mach_ring
      · show bipev (if pnorm A = [] then [] else [A]) x y = _
        rw [if_neg hA]
        rfl
  | cons B Bs => intro x y; rfl

/-- **The trim is invisible to evaluation.** This is what lets it happen before the identity rather
than after. -/
theorem bipev_bitrim : ∀ (L : List (List Real)) (x y : Real),
    bipev (bitrim L) x y = bipev L x y := by
  intro L
  induction L with
  | nil => intro x y; rfl
  | cons A As ih =>
      intro x y
      show bipev (biconsN A (bitrim As)) x y = pev A x + y * bipev As x y
      rw [bipev_biconsN A (bitrim As) x y, ih x y]

/-- **The shape the readings consume**: a trimmed list is empty, or ends in a coefficient that is
genuinely not the zero polynomial. -/
theorem bitrim_split (L : List (List Real)) :
    bitrim L = [] ∨ ∃ (As : List (List Real)) (α : List Real),
      bitrim L = As ++ [α] ∧ pnorm α ≠ [] := by
  cases hc : bitrim L with
  | nil => exact Or.inl rfl
  | cons A As =>
      have hne : (A :: As) ≠ [] := by simp
      refine Or.inr ⟨(A :: As).dropLast, (A :: As).getLast hne,
        (List.dropLast_concat_getLast hne).symm, ?_⟩
      have hn := bitrim_normal L
      rw [hc] at hn
      exact hn _ (List.getLast?_eq_some_getLast hne)

end MachLib
