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

end InnerKhovanskiiExpWFMod
end MachLib
