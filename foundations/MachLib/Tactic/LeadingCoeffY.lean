import MachLib.MultiPoly

/-!
# MachLib.Tactic.LeadingCoeffY — `mach_leading_coeff_y` tactic

A simp-style closer for goals involving `MultiPoly.leadingCoeffY` and
`MultiPoly.degreeY` on syntactic AST positions. Bundles the existing
case-analysis lemmas into a single tactic call so structural-induction
proofs (lemma 1 in the chain-Khovanskii Step 3b, plus dozens of
similar identities) don't have to do the bookkeeping by hand.

## What it handles

Given a goal that's an equation or inequality involving
`leadingCoeffY i (add p q)`, `leadingCoeffY i (sub p q)`,
`leadingCoeffY i (mul p q)`, or `leadingCoeffY i (const c)`, etc., the
tactic:

1. Unfolds via the curated case-analysis lemmas (`leadingCoeffY_mul_const`,
   `leadingCoeffY_sub_of_lt`, `leadingCoeffY_sub_of_eq`).
2. Simplifies `degreeY` of constructor applications via `degreeY_const`,
   `degreeY_varX`, `degreeY_leadingCoeffY`.
3. Falls through to `mach_ring` (which now includes `omega` for Nat
   residues) to close any remaining arithmetic.

## What it does NOT handle

- `leadingCoeffY i (add p q)` when degreeY p and degreeY q are
  unequal — the user must case-split on which side dominates BEFORE
  calling the tactic.
- Full structural induction — this is a closer, not an inducter.
- Cross-Fin-index reasoning.

## Usage

```lean
example (a b : MultiPoly 1) (h : degreeY ⟨0, _⟩ a = degreeY ⟨0, _⟩ b) :
    leadingCoeffY ⟨0, _⟩ (sub a b)
    = sub (leadingCoeffY ⟨0, _⟩ a) (leadingCoeffY ⟨0, _⟩ b) := by
  mach_leading_coeff_y
```

## Implementation

The tactic is a `simp only` against an explicit lemma list, followed
by `mach_ring` (which now dispatches to `omega` for Nat-arithmetic
residues). The lemma list is intentionally inline rather than tagged
`@[simp]` globally — the structural lemmas (e.g. `leadingCoeffY_sub_of_lt`)
have side conditions like `degreeY i p < degreeY i q` that simp can't
always discharge cleanly, so we keep them as opt-in ingredients of
this tactic only. -/

namespace MachLib
namespace Tactic

open MachLib.MultiPolyMod.MultiPoly

/-- Closes goals about `leadingCoeffY i (...)` on syntactic MultiPoly
constructor positions. See module docstring for scope.

The implementation is `simp only` with the curated lemma list followed
by `mach_ring`. The `try` wrappers prevent "no goals" errors when one
phase already closes the goal. -/
macro "mach_leading_coeff_y" : tactic => `(tactic|
  (try simp only [
        MachLib.MultiPolyMod.MultiPoly.degreeY_const,
        MachLib.MultiPolyMod.MultiPoly.degreeY_varX,
        MachLib.MultiPolyMod.MultiPoly.degreeY_leadingCoeffY,
        MachLib.MultiPolyMod.MultiPoly.degreeY_mul_const,
        MachLib.MultiPolyMod.MultiPoly.leadingCoeffY_mul_const,
        MachLib.MultiPolyMod.MultiPoly.degreeY_sub_of_lt,
        MachLib.MultiPolyMod.MultiPoly.degreeY_sub_of_eq,
        MachLib.MultiPolyMod.MultiPoly.leadingCoeffY_sub_of_lt,
        MachLib.MultiPolyMod.MultiPoly.leadingCoeffY_sub_of_eq
       ]
   try mach_ring
   try rfl))

end Tactic
end MachLib
