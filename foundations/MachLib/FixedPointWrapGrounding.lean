import MachLib.FixedPointRange
import MachLib.Decimal

/-!
# Grounding `WrapAdd` — where the abstract model meets integer arithmetic

`FixedPointRange.WrapAdd`'s out-of-range branch says the machine value differs from the true sum
by `n · Span` for some `1 ≤ |n|`. **That was a hypothesis SHAPE, not a derivation** — the file
asserted what a wrap looks like and proved consequences, but nothing connected it to arithmetic.

This file supplies the connection: **two's-complement wrapping displaces by a WHOLE NUMBER of
spans**, and a whole number that is not zero has magnitude at least one. That is the entire content
of the `1 ≤ abs n` side condition, and it is now derived from `Nat` rather than assumed.

## ▸ What this does NOT do, stated plainly

**It does not reach bit vectors.** `MachLib.Real`'s `floor` is `Real → Real` with only bracketing
axioms — its own docstring records that *"since `floor` is collapsed to `Real → Real` (no integer
codomain) the integer-valued fact `⌊0⌋ = 0` is not derivable"*. **So the modular reduction cannot
be defined through `floor` without adding an integrality axiom, and adding one to close a modelling
gap would widen the trust boundary to buy a convenience.** It is not done.

**The route taken instead goes through `natCast`**, which is already in the corpus and already
carries induction-proved arithmetic. The displacement is quantified as `natCast k` with `1 ≤ k` in
`Nat` — **integrality by construction, no new axiom.**

**The remaining gap, named:** `FixedPointSat`'s `List Bool` layer is unsigned and about
*saturation*; connecting it to a *signed wrapping* story is a separate development and is not
attempted here. **So the chain is grounded from `WrapAdd` down to integer displacement, and remains
a model below that.**

No new axioms. No `sorry`.
-/

namespace MachLib
namespace Real

/-- `natCast 1 = 1`, from the successor axiom. -/
theorem natCast_one : natCast 1 = 1 := by
  rw [show (1 : Nat) = 0 + 1 from rfl, natCast_succ, natCast_zero]
  mach_mpoly []

/-- **A nonzero `Nat` casts to at least one.** This is the integrality fact the whole grounding
rests on: there is nothing strictly between `0` and `1` in the image of `natCast`. -/
theorem one_le_natCast {k : Nat} (h : 1 ≤ k) : (1 : Real) ≤ natCast k := by
  have := natCast_le_of_le h
  rwa [natCast_one] at this

/-- **The mathematical content of a two's-complement wrap: displacement by a WHOLE number of
spans**, in either direction. `k ≥ 1` because a wrap that moved by zero spans did not wrap. -/
def ShiftsBySpans (Span a b w : Real) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ (w = a + b - natCast k * Span ∨ w = a + b + natCast k * Span)

/-- **THE GROUNDING.** An out-of-range result that differs from the true sum by a whole number of
spans satisfies `WrapAdd`. The `1 ≤ abs n` side condition — previously assumed — is now *derived*,
from `1 ≤ k` in `Nat` through `one_le_natCast`.

Both directions are covered: a positive overflow subtracts spans, a negative one adds them, and the
`+` case supplies `n = −natCast k`, whose magnitude is the same. -/
theorem wrapAdd_of_shiftsBySpans {Span M a b w : Real}
    (hnf : ¬ Fits M (a + b)) (hs : ShiftsBySpans Span a b w) :
    WrapAdd Span M a b w := by
  obtain ⟨k, hk, hcase⟩ := hs
  have hk1 : (1 : Real) ≤ natCast k := one_le_natCast hk
  have hkabs : (1 : Real) ≤ abs (natCast k) := by
    rwa [abs_of_nonneg (natCast_nonneg k)]
  refine Or.inr ⟨hnf, ?_⟩
  rcases hcase with hminus | hplus
  · exact ⟨natCast k, hkabs, hminus⟩
  · refine ⟨-(natCast k), ?_, ?_⟩
    · rwa [abs_neg]
    · rw [hplus]; mach_mpoly [a, b, natCast k, Span]

/-- **In range, nothing moves.** The other half of `WrapAdd`, stated for symmetry so a caller can
build the predicate from machine-observable facts in either case. -/
theorem wrapAdd_of_exact {Span M a b w : Real}
    (hf : Fits M (a + b)) (he : w = a + b) : WrapAdd Span M a b w :=
  Or.inl ⟨hf, he⟩

/-- **The catastrophe result, now resting on integrality rather than on an assumption.**

Composing the grounding with `wrap_error_catastrophic`: a whole-span displacement out of range puts
the machine value at least a full span from the truth. **This is the same conclusion the earlier
file reached, but its `1 ≤ abs n` premise is no longer taken on trust.** -/
theorem shift_error_catastrophic {Span M a b w : Real}
    (hnf : ¬ Fits M (a + b)) (hs : ShiftsBySpans Span a b w) (hspan : 0 ≤ Span) :
    Span ≤ abs (w - (a + b)) :=
  wrap_error_catastrophic (wrapAdd_of_shiftsBySpans hnf hs) hnf hspan

end Real
end MachLib
