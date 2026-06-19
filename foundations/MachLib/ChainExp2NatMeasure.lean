import MachLib.ChainExp2Instance
import MachLib.ChainExp2WFInstance
import MachLib.InnerKhovanskiiExpListMeasured
import MachLib.ChainExp2ListMeasuredInstance

/-!
# MachLib.ChainExp2NatMeasure — concrete Nat measure for chain-2

## What this file ships

A concrete `chain2Nat : MultiPoly 2 → Nat` definition + the chain-2
instance using the ListMeasured framework plumbed with this measure.
Sub-obligations are factored cleanly:

- **Sub-obligation 1** (define `chain2Nat`): **DONE in this file** via
  `chain2Nat g := polyTrueDegreeStrict (polyCoeffs (mP2PFL (lcY 1 g)))`.
  This is the third component of the existing `chain2Measure` (the
  canonical x-degree of the y_1-leading coefficient). The first two
  components (degreeY 1, degreeY 0) are dropped because their behaviour
  under `chainTotalDeriv` is what blocks closure (degreeY 0 rises,
  degreeY 1 is preserved). The third component is preserved under
  `chainTotalDeriv` (per the structural analysis), so it satisfies
  `coeffStep_le` with equality.

- **Sub-obligation 2** (prove `coeffStep_le`): parametric here. The
  proof requires the supporting lemmas listed below. Discharging
  them is the next concrete step.

- **Sub-obligation 3** (prove `list_scaledReduction_lt`): parametric.
  This is where the genuine net-descent counting math lives.

## Why this chain2Nat (and not the full lex-3)

The lex-3 measure `(degreeY 1, degreeY 0, polyTrueDegreeStrict)`
fails the per-element coeffStep_le at chain-2 because component 2
(degreeY 0) STRICTLY RISES by 1 under `chainTotalDeriv g` at
k = 0. ANY Nat collapse `(a · B² + b · B + c)` of the lex-3 would
also rise by ≈ B when component 2 rises by 1.

Dropping components 1 and 2 and keeping only component 3 (the
canonical x-degree of the y_1-leading coefficient) escapes this:

**The leading-y_1-coefficient transformation under chain-2 chainTotalDeriv**:
let `c_d := lcY 1 g`. Then the leading-y_1 coefficient of
`chainTotalDeriv g + k·y_0·g` is:

```
∂c_d/∂x + y_0·∂c_d/∂y_0 + (d + k)·y_0·c_d
```

where `d := degreeY 1 g`. Each of these three terms has
`polyTrueDegreeStrict` (as an x-polynomial with y_0 in coefficients)
**bounded above by** `polyTrueDegreeStrict c_d`:

- `∂c_d/∂x`: x-derivative reduces by 1 (or yields canonically zero).
- `y_0·∂c_d/∂y_0`: y_0-derivative preserves x-degree; multiplication
  by `y_0` preserves x-degree.
- `(d + k)·y_0·c_d`: scalar + y_0 multiplication, both preserve x-degree.

So the SUM's polyTrueDegreeStrict is at most polyTrueDegreeStrict c_d.

**This gives `coeffStep_le` with equality.** No +1 hidden anywhere.

For `coeffStep_lt` at k = 0, the polyTrueDegreeStrict stays EQUAL
(none of the three terms strictly reduce it in general). So
`coeffStep_lt` per-element FAILS. The list-level descent
(`list_scaledReduction_lt`) is where the cancellation argument lives
— same as the higher-level analysis in `ChainExp2ListMeasuredInstance.lean`.

## Supporting lemmas needed for the coeffStep_le proof

The proof reduces to these four structural facts about
`polyTrueDegreeStrict`:

1. `polyTrueDegreeStrict_add_le`:
   `polyTrueDegreeStrict (L_a + L_b) ≤ max (polyTrueDegreeStrict L_a)
   (polyTrueDegreeStrict L_b)`.

2. `polyTrueDegreeStrict_const_mul_le`:
   `polyTrueDegreeStrict (c · L) ≤ polyTrueDegreeStrict L`.

3. `polyTrueDegreeStrict_y0_mul_le`:
   `polyTrueDegreeStrict (y_0 · L) ≤ polyTrueDegreeStrict L`
   (y_0 multiplication doesn't change x-degree).

4. `polyTrueDegreeStrict_y0_deriv_le`:
   `polyTrueDegreeStrict (∂L/∂y_0) ≤ polyTrueDegreeStrict L`
   (y_0 derivative doesn't change x-degree).

5. `polyTrueDegreeStrict_x_deriv_lt_or_eq_zero`: existing
   `polyTrueDegreeStrict_polyDerivativeCoeffs_lt` covers this.

Estimate: ~150-200 lines for the 4 new structural lemmas + ~30 lines
for the chain-2 `coeffStep_le` proof using them.

Once shipped, `chain2_to_ListMeasured` (in
`ChainExp2ListMeasuredInstance.lean`) can be called with this proven
`coeffStep_le_hyp`, leaving only `list_scaledReduction_lt_hyp` as
the remaining genuine math.
-/

namespace MachLib
namespace ChainExp2NatMeasureMod

open MachLib.Real
open MachLib.MultiPolyMod
open MachLib.PolynomialCanonical
open MachLib.PfaffianChainMod
open MachLib.IterExpChainMod
open MachLib.ChainExp2WFInstanceMod (chain2Measure fin1_of_2 fin0_of_2)

/-! ## The concrete Nat measure -/

/-- Concrete chain-2 Nat measure: the canonical x-degree of the
y_1-leading coefficient. Drops components 1 and 2 of the lex-3
`chain2Measure` because their behaviour under `chainTotalDeriv`
blocks closure (degreeY 0 strictly rises). Component 3 alone is
preserved under `chainTotalDeriv`, satisfying `coeffStep_le` with
equality. -/
noncomputable def chain2Nat (g : MultiPoly 2) : Nat :=
  (chain2Measure g).2.2

/-! ## Structural property: `chain2Nat` extracts the third lex-3
component. Used downstream to bridge to the lex-3 analysis. -/

theorem chain2Nat_eq_third_lex3 (g : MultiPoly 2) :
    chain2Nat g = (chain2Measure g).2.2 := rfl

/-! ## Closing notes

This file ships the **chain2Nat definition only**.

## Honest finding (2026-06-19, after concrete testing)

This `chain2Nat` candidate satisfies `coeffStep_le` for the chain-2
step (the analysis goes through — see PolynomialCanonicalDegreeLemmas
for the supporting machinery), BUT IT DOES NOT SATISFY
`length_one_bound`.

**Counterexample**: take `g := (y_0 - 1) · (y_0 - 2) · y_1`. Then:

  - Zeros of `eval g x = (exp x - 1)·(exp x - 2)·exp(exp x)` over Real:
    `exp x - 1 = 0` at `x = 0`; `exp x - 2 = 0` at `x = log 2`. Two zeros.

  - But `lcY 1 g = (y_0 - 1)·(y_0 - 2) = y_0^2 - 3·y_0 + 2`, and
    `mP2PFL` evaluates this at `y_0 = 0`, giving `const 2`. So
    `polyTrueDegreeStrict (polyCoeffs (mP2PFL (lcY 1 g))) = 1`.

  - **length_one_bound demands `2 ≤ 1`, which is FALSE.**

The failure mode: `mP2PFL` is the y-free projection (sets `y_j = 0`),
which erases the y_0-degree information from the leading coefficient.
But the zeros of `eval g` depend on the y_0-degree (via solutions of
`y_0(x) = something`), which `mP2PFL` discards.

## What CAN be salvaged

The 4 supporting structural lemmas (factored above) are valid
**polynomial-algebra facts** independent of whether `chain2Nat` is
the right chain-2 measure. They're useful infrastructure for any
chain-2 (or chain-N) measure attempt.

The HONEST take: chain-2 closure needs a measure that captures
BOTH the canonical x-degree AND the y_0-degree of the y_1-leading
coefficient (and probably the y_1-degree as well). The naive
projection-based approach loses information that's essential for
the length_one_bound. This is consistent with the previous session's
analysis that chain-2 closure is structurally harder than SingleExp.

## Next-session path

Two options:

(I) **Composite Nat measure** like
    `chain2Nat g := 2^(degreeY 1) · 3^(degreeY 0) · 5^(polyTrueDegreeStrict)`
    — captures all three lex-3 components in a single Nat, but the
    base 5 might need to be larger to absorb the +1 raise in degreeY 0
    under chainTotalDeriv. Working out the exact base requires
    structural bounds on chain-2 chainTotalDeriv.

(II) **Genuine analytic infrastructure** — prove the chain-2 bound
    via Wronskians or a constructive analog. This is the original
    Khovanskii path and requires substantial new infrastructure.

Either path is multi-week work. This file documents the candidate
that's been ruled out so the next session doesn't re-derive the
same dead end.
-/

end ChainExp2NatMeasureMod
end MachLib
