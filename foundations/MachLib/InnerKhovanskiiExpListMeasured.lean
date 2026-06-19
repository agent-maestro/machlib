import MachLib.InnerKhovanskiiExp

/-!
# MachLib.InnerKhovanskiiExpListMeasured — list-level descent framework

## Why this file exists (2026-06-19, Fix B follow-up)

`InnerKhovanskiiExpMeasured` (in `InnerKhovanskiiExp.lean`) requires
**per-element strict descent**:

```lean
coeffStep_lt : ∀ t : T, measure t > 0 →
    measure (add (derivative t) (scalarMul 0 t)) < measure t
```

For SingleExp this holds: `chainTotalDeriv` strictly decreases
`polyTrueDegreeStrict` of the y_0-leading coefficient.

For chain-2 it FAILS at `g := varY 1`: `chainTotalDeriv g` raises
`degreeY 0` strictly, so per-element strict descent is impossible.

But chain-2 might still admit **LIST-LEVEL strict descent**:
`scaledReductionAux` operates on a LIST of coefficients of length k.
At chain-2, ONE coefficient (the y_1-leading) has its measure raised
by 1 under `chainTotalDeriv`. The other (k-1) coefficients are
operated on via `scalarMul k g` with `k ≠ 0`, where the scaledReduction
subtraction cancels the chain-rule mass injection (per the
analogous SingleExp cancellation). So those (k-1) coefficients each
drop measure by ≥1.

**Net change**: +1 (leading) - (k-1) (rest) = -(k-2).

For k ≥ 2, list-level sumMeasure strictly decreases. The k = 1 case
falls back to `length_one_bound` (the recursion base case).

This file ships the **list-level measured framework**:
`InnerKhovanskiiExpListMeasured` that demands list-level strict
descent INSTEAD of per-element strict descent. The chain-2 instance
can plug into this framework once the list-level descent is proven
in a follow-up file.

## What this file ships

1. `InnerKhovanskiiExpListMeasured` — the framework structure with
   list-level descent obligation.

2. `measured_to_listMeasured` — bridge from
   `InnerKhovanskiiExpMeasured`. Uses the existing
   `sumMeasure_scaledReductionAux_lt` (which holds for SingleExp via
   per-element strict descent) to discharge list-level descent.

3. Documentation of the chain-2 path forward.

## What this file does NOT do

It does NOT close chain-2. The list-level descent for chain-2 is
genuine mathematical work that requires:

- Identifying the chain-2 measure (probably the existing
  `chain2Measure` lex-3 collapsed to a Nat via `2^a · 3^b · 5^c` or
  similar)
- Proving `chainTotalDeriv` + scaledReduction cancellation works the
  same way at chain-2 as at SingleExp for non-leading coefficients
- Proving the +1 on leading coefficient is dominated by the -(k-1)
  on the rest, when k ≥ 2

That's a separate file. This file is the FRAMEWORK SCAFFOLD.

## Axioms

Zero new axioms. Zero `sorry`. Builds on `InnerKhovanskiiExp` (no new
axioms) + Lean stdlib + MachLib.Real foundations.
-/

namespace MachLib
namespace InnerKhovanskiiExpListMeasuredMod

open MachLib.Real
open MachLib.InnerKhovanskiiExpMod
open MachLib.InnerKhovanskiiExpMod.InnerKhovanskiiExp
open MachLib.InnerKhovanskiiExpMod.InnerKhovanskiiExpMeasured

/-! ## The list-level measured framework -/

/-- The list-level descent generalisation of
`InnerKhovanskiiExpMeasured`. Per-element strict descent (`coeffStep_lt`)
is REPLACED by list-level strict descent of `scaledReductionAux` on
non-trivial inputs.

Use case: chain-2 and higher chains where per-element strict descent
fails but list-level descent holds (one coefficient's measure rises,
others fall by more in aggregate). -/
structure InnerKhovanskiiExpListMeasured extends InnerKhovanskiiExp where
  /-- Per-element Nat measure. Same shape as `InnerKhovanskiiExpMeasured`. -/
  measure : T → Nat
  /-- Length-one bound, unchanged from `InnerKhovanskiiExpMeasured`. -/
  length_one_bound : ∀ t : T, ∀ a b : Real, a < b →
    (∃ x : Real, eval t x ≠ 0) →
    ∀ zeros : List Real, zeros.Nodup →
    (∀ z ∈ zeros, a < z ∧ z < b ∧ eval t z = 0) →
    zeros.length ≤ measure t
  /-- Per-element non-strict descent (still required for the
  recursion to make progress). -/
  coeffStep_le : ∀ k : Real, ∀ t : T,
    measure (add (derivative t) (scalarMul k t)) ≤ measure t
  /-- **List-level strict descent**: `scaledReductionAux` strictly
  decreases the sum-of-measures on non-empty input lists whose last
  coefficient has positive measure.

  This is the KEY axiom of this framework. For SingleExp, it follows
  from per-element strict descent. For chain-2 and higher, it can
  be proven directly via the cancellation argument outlined in the
  file docstring above. -/
  list_scaledReduction_lt :
    ∀ (coeffs : List T) (offset : Nat) (hne : coeffs ≠ []),
    measure (coeffs.getLast hne) > 0 →
    let listSum : List T → Nat := fun cs => cs.foldr (fun t acc => measure t + acc) 0
    listSum (scaledReductionAux toInnerKhovanskiiExp
              (natCast (offset + coeffs.length - 1)) coeffs offset)
    < listSum coeffs

/-! ## Bridge: `InnerKhovanskiiExpMeasured` ⟶ `InnerKhovanskiiExpListMeasured`

The existing Measured framework's `sumMeasure_scaledReductionAux_lt`
proves exactly the list-level descent obligation. This bridge makes
every Measured-framework user automatically a List-Measured-framework
user.
-/

/-- Bridge from `InnerKhovanskiiExpMeasured` to
`InnerKhovanskiiExpListMeasured`. The list-level descent is
discharged via the existing `sumMeasure_scaledReductionAux_lt`. -/
noncomputable def measured_to_listMeasured
    (IKEM : InnerKhovanskiiExpMeasured) :
    InnerKhovanskiiExpListMeasured where
  toInnerKhovanskiiExp := IKEM.toInnerKhovanskiiExp
  measure := IKEM.measure
  length_one_bound := IKEM.length_one_bound
  coeffStep_le := IKEM.coeffStep_le
  list_scaledReduction_lt := by
    intro coeffs offset hne hlast_pos
    -- IKEM.sumMeasure is the same as foldr-based listSum (definitionally).
    -- We unfold both to the common Nat form.
    have h := sumMeasure_scaledReductionAux_lt IKEM coeffs offset hne hlast_pos
    -- h : sumMeasure IKEM (scaledReductionAux ... coeffs offset)
    --     < sumMeasure IKEM coeffs
    -- The let-bound listSum is the same as sumMeasure (both are
    -- foldr-style sum-of-measures). Show this by induction on the list.
    show (scaledReductionAux IKEM.toInnerKhovanskiiExp
            (natCast (offset + coeffs.length - 1)) coeffs offset).foldr
            (fun t acc => IKEM.measure t + acc) 0
        < coeffs.foldr (fun t acc => IKEM.measure t + acc) 0
    -- sumMeasure is defined as: nil → 0; cons t rest → measure t + sumMeasure rest.
    -- foldr (fun t acc => measure t + acc) 0 expands to the same thing.
    have eq_listSum : ∀ l : List IKEM.T,
        l.foldr (fun t acc => IKEM.measure t + acc) 0 = sumMeasure IKEM l := by
      intro l
      induction l with
      | nil => rfl
      | cons head tail ih =>
        show IKEM.measure head + tail.foldr (fun t acc => IKEM.measure t + acc) 0
            = IKEM.measure head + sumMeasure IKEM tail
        rw [ih]
    rw [eq_listSum, eq_listSum]
    exact h

/-! ## Why this is the framework for chain-2 (Fix B path)

The chain-2 `chainTotalDeriv` raises `degreeY 0` by 1 on the
y_1-leading coefficient when the y_1-degree is positive. This breaks
the per-element strict descent that `InnerKhovanskiiExpMeasured`
demands.

But `scaledReductionAux` at a `length`-long list operates on each
coefficient with a DIFFERENT scalar:
  - First coefficient: `scalarMul (0 - (length-1))`     (= -(length-1))
  - Second coefficient: `scalarMul (1 - (length-1))`    (= -(length-2))
  - ...
  - Last coefficient: `scalarMul ((length-1) - (length-1))` (= 0)

For the LAST coefficient (k = 0), the step is just `chainTotalDeriv`.
This is where chain-2 raises the measure by 1.

For the NON-LAST coefficients (k ≠ 0), the step includes the
subtraction `chainTotalDeriv g + k·y_0·g`. With negative k, this is
`chainTotalDeriv g - |k|·y_0·g`. The `chainTotalDeriv g`'s
y_0-degree raise is CANCELLED by the subtraction (the algebra: the
y_0·∂g/∂y_0 term in chainTotalDeriv has degree d_0+1; the subtraction
removes the leading-y_0 part). So each non-last coefficient sees
chain-rule cancellation analogous to SingleExp's leading-coefficient
reduction.

If the non-last coefficients each drop measure by ≥ 1 (via
chain-rule cancellation + the SingleExp-style `polyTrueDegreeStrict`
descent on the resulting polynomial), and the last coefficient raises
by ≤ 1, then for `length ≥ 2`:

  net change ≤ +1 - (length - 1) · 1 = -(length - 2)

This is < 0 for length ≥ 2. The list-level descent obligation is
discharged.

For length = 1, the recursion is at the base case
(`length_one_bound`) and doesn't recurse further.

## Next-session work

To plug chain-2 into this framework:

1. Define `chain2NatMeasure : MultiPoly 2 → Nat` (collapse the lex-3
   measure to a Nat via, e.g., `2^a · 3^b · 5^c` or a polynomial
   evaluation at a base larger than the per-component max).

2. Prove `chain2NatMeasure_coeffStep_le`: for any `k ∈ Real` and any
   `g ∈ MultiPoly 2`, `chain2NatMeasure (chainTotalDeriv g + k·y_0·g)
   ≤ chain2NatMeasure g`. The collapse function needs to be chosen so
   that BOTH the +1 raise (at k=0) and the cancellation (at k≠0) fit
   within ≤.

3. Prove `chain2_list_scaledReduction_lt`: for any non-empty list of
   `MultiPoly 2` whose last coefficient has positive measure,
   `scaledReductionAux` strictly decreases the list-level sum.

(2) is the structural argument; (3) is the integration.

Both are substantive mathematical work — ~200-300 more lines per the
WFR memo's estimate. This file is the FRAMEWORK SHIM that makes that
work plug in cleanly.

## Comparison to the precondition-aware WFR framework

This file's `InnerKhovanskiiExpListMeasured` is a SISTER framework
to `InnerKhovanskiiExpWFRPrecond` (in `InnerKhovanskiiExpWFRPrecond.lean`):

- WFRPrecond: per-element WFR + user-supplied precondition on the
  strict descent.
- ListMeasured: per-element non-strict descent + list-level strict
  descent obligation.

Both are valid framework redesigns. WFRPrecond keeps the per-element
strict descent shape (just guarded). ListMeasured changes the level
at which strict descent is demanded.

For chain-2, ListMeasured might be the more natural fit because the
cancellation argument naturally operates at the list level (the
scaledReductionAux's c parameter ties together all elements'
scalars).

The chain-2 instance can attempt EITHER framework. ListMeasured is
the cleaner target if the list-level cancellation works.
-/

end InnerKhovanskiiExpListMeasuredMod
end MachLib
