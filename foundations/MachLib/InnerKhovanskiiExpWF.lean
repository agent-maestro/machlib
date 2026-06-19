import MachLib.InnerKhovanskiiExp
import MachLib.ChainExp2Instance

/-!
# MachLib.InnerKhovanskiiExpWF — well-founded-relation variant of the
chain-Khovanskii framework (kickoff scaffolding)

## Why this file exists

`InnerKhovanskiiExpMeasured` (in `InnerKhovanskiiExp.lean`) requires a
`measure : T → Nat` with `coeffStep_le` (non-strict descent for all k)
and `coeffStep_lt` (strict descent at k=0). For SingleExp (chain
length 1), `scalarMul` is multiplication by a Real constant — measure-
preserving. The Nat measure works.

For chain-level 2 (over `IterExp 2`), `scalarMul k` is multiplication
by the chain function `h_deriv(x) = y_0`. This structurally raises
`degreeY 0` by 1. ANY Nat measure capturing strict-descent-on-
derivative will INCREASE under this y_0 multiplication. The
`ChainExp2Instance` docstring (lines 217–284) walks through three
paths that all hit the same wall.

The structural fix per that docstring is to replace `Nat` with a
`WellFoundedRelation`. This file ships the kickoff scaffolding:

1. `InnerKhovanskiiExpWFR` — a parametric structure carrying a
   well-founded relation `T → T → Prop` instead of a Nat measure.

2. `lexLTPair_WF` — well-foundedness of the lex relation on `Nat × Nat`
   re-exported from `PfaffianChain.lexLT_wf` for in-namespace use.

3. `nat_measure_to_WFR` — a bridge: any `InnerKhovanskiiExpMeasured`
   trivially yields an `InnerKhovanskiiExpWFR` via `Nat.lt` (which IS
   a well-founded relation). This lets the existing SingleExp closure
   route through the new structure unchanged, demonstrating that the
   WF framework is a strict generalisation.

## What this file does NOT do (yet)

The full chain-2 `coeffStep_le` / `coeffStep_lt` proofs against the lex
measure are the multi-session work per the memory entry
`project_khovanskii_multi_exp_framework.md`. They go in a follow-up file
`ChainExp2WFInstance.lean` (planned).

The rewritten `auto_bound_with_propagation_aux` using WF induction is
also follow-up work. The current Nat-measure version routes via
`nat_measure_to_WFR` for the SingleExp case unchanged.

## Status

KICKOFF — scaffolding only. Compiles. No sorry. No axioms beyond those
already used by SingleExp (Lean stdlib + MachLib.Real).
-/

namespace MachLib
namespace InnerKhovanskiiExpWFMod

open MachLib.InnerKhovanskiiExpMod

/-! ## The well-founded relation framework -/

/-- The WF generalisation of `InnerKhovanskiiExpMeasured`. The Nat
measure is replaced by a `T → T → Prop` strict relation, plus a proof
of well-foundedness. -/
structure InnerKhovanskiiExpWFR extends InnerKhovanskiiExp where
  /-- The strict descent relation on T. -/
  measureRel : T → T → Prop
  /-- The descent relation is well-founded. -/
  measureWF : WellFounded measureRel
  /-- Length-one bound predicate, unchanged from `InnerKhovanskiiExpMeasured`
  except the bound is now an external Nat parameter (since the measure
  no longer produces one). -/
  length_one_bound : ∀ t : T, ∀ a b : Real, a < b →
    (∃ x : Real, eval t x ≠ 0) →
    ∃ N : Nat, ∀ zeros : List Real, zeros.Nodup →
      (∀ z ∈ zeros, a < z ∧ z < b ∧ eval t z = 0) →
      zeros.length ≤ N
  /-- coeffStep weakly descends: for arbitrary k, the result is not
  strictly LESS than the input under measureRel — i.e. it does not
  rule out equality. (Negative formulation: NOT measureRel result input.) -/
  coeffStep_le : ∀ k : Real, ∀ t : T,
    ¬ measureRel (add (derivative t) (scalarMul k t)) t ∨
    measureRel (add (derivative t) (scalarMul k t)) t
  /-- coeffStep at k=0 strictly descends: the result IS strictly LESS
  than the input under measureRel. -/
  coeffStep_lt : ∀ t : T,
    measureRel (add (derivative t) (scalarMul 0 t)) t ∨
    add (derivative t) (scalarMul 0 t) = t

/-! ## Lex measure on `Nat × Nat`

The chain-level-2 measure of choice. The first component captures
`degreeY 0`; the second component captures the canonical leading-
coefficient x-degree. The lex order is well-founded (proven in
`PfaffianChain.lean` as `lexLT_wf`).
-/

/-- Lex strict-less-than on `Nat × Nat`: re-exported from
`PfaffianChain.PfaffianFn.lexLT` for in-namespace use. -/
def lexLTPair : Nat × Nat → Nat × Nat → Prop :=
  MachLib.PfaffianChainMod.PfaffianFn.lexLT

/-- `lexLTPair` is well-founded. -/
theorem lexLTPair_WF : WellFounded lexLTPair :=
  MachLib.PfaffianChainMod.PfaffianFn.lexLT_wf

/-! ## Bridge: Nat-measure ⟶ WF-relation

Any `InnerKhovanskiiExpMeasured` trivially induces an
`InnerKhovanskiiExpWFR`: the relation is `λ a b => measure a < measure b`,
which is well-founded by `Nat.lt`'s well-foundedness pulled back through
the measure. This bridge means EVERY result currently proved against
`InnerKhovanskiiExpMeasured` (SingleExp closure, chain-2 measured-
axiom-parametric corollary, etc.) automatically lifts to the WF
framework. -/

/-- The natural relation `λ a b => m a < m b` for a Nat-valued measure
`m`. Pulled back from `Nat.lt`. -/
def measureLT {T : Type} (m : T → Nat) : T → T → Prop :=
  fun a b => m a < m b

/-- `measureLT m` is well-founded for any `m : T → Nat`, by pullback
from `Nat.lt`'s well-foundedness. -/
theorem measureLT_WF {T : Type} (m : T → Nat) :
    WellFounded (measureLT m) :=
  InvImage.wf m Nat.lt_wfRel.wf

/-! ## Chain-2 obstruction — precise statement for next session

The naive per-coefficient lex measure
`m g = (degreeY 0 g, polyTrueDegreeStrict (polyCoeffs (mP2PFL (lcY 0 g))))`
does NOT satisfy `coeffStep_le` for chain-level 2 over `IterExpChain 2`.
This section formalises exactly why, so the next session can pick up
without re-deriving the obstruction.

The chain-2 chainTotalDeriv has the form (informally):

  chainTotalDeriv f = ∂f/∂x + y_0 · ∂f/∂y_0 + y_0·y_1 · ∂f/∂y_1

where the `y_0 · ∂f/∂y_0` term RAISES `degreeY 0` by 1 (unlike
SingleExp, where chainTotalDeriv preserves degreeY 0 by
`degreeY_chainTotalDeriv_eq_SingleExp`).

Then `coeffStep g k = chainTotalDeriv g + (k · y_0) · g` has:
  - degreeY 0 of `chainTotalDeriv g`: ≥ degreeY 0 g + 1 in general
  - degreeY 0 of `(k · y_0) · g` for k ≠ 0: = degreeY 0 g + 1
  - So degreeY 0 of `coeffStep g k`: ≥ degreeY 0 g + 1

Under the lex measure with first component `degreeY 0`, this is a
STRICT INCREASE, so `coeffStep_le` (¬ measureRel (coeffStep g k) g)
fails — the relation IS satisfied in the wrong direction.

## The two candidate fixes (for the next session)

**Fix A: Decompose the chain extension.** Track `degreeY 0` and
`degreeY 1` separately. `chainTotalDeriv` on a chain-2 multi-poly
that's polynomial in `y_1` of degree d_1 reduces d_1 by 1 (the
y_1-leading term gets differentiated to a y_0-poly of one lower
y_1-degree). The measure becomes `(d_1, max d_0_across_y_1_levels,
polyTrueDegreeStrict ...)`. This is the muse's "angle 1" reduction
applied symbolically at the measure level.

**Fix B: Reformulate the framework as a list-level WF relation.**
Instead of measuring each coefficient T, measure the LIST `List T`
as a single object. The relation `measureRel : List T → List T → Prop`
is well-founded if every reduction step yields a strictly smaller
list. Then `coeffStep_le` becomes "the list after scaledReductionAux
is ≤ the list before" which can absorb the local y_0-multiplication
because the OTHER coefficients in the list (which DO satisfy strict
decrease at k=0) drag the list-level measure down.

Both fixes require ~200–300 lines of new lemmas. Fix A is
mathematically cleaner; Fix B is closer to the existing framework
shape. Picking is the next session's first decision. -/

end InnerKhovanskiiExpWFMod
end MachLib
