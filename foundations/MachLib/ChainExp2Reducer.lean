import MachLib.KhovanskiiReduction
import MachLib.ChainExp2Measure
import MachLib.LexProd

/-!
# Path B — the chain-2 reducer interface (the chain-aware `StepwiseDecreaseReducer`)

`docs/chain2_closure_scope.md` Path B: a chain-2-specific reducer/capstone built on the chain-aware
measure (`ChainExp2Measure.chain2Measure`) and its well-foundedness (`chain2Order_wf`), so the closed,
audited single-exp framework is never touched.

This module defines the **interface** (Phase-3 contract): the chain-2 analog of the framework's
`ReduceStep` / `StepwiseDecreaseReducer`, but with `lex_decrease` stated in the *chain-aware* nested
measure rather than the flat `lexMeasure` (which provably can't descend at `(degreeY₁>0, second=0)`).

The single field `lex_decrease` is exactly **Phase 2** — "the reduce step strictly decreases
`chain2Measure`" — the one deep theorem of the closure; everything else (Phase 4: build the reducer,
extract the bound) mirrors the framework's `buildReducer`/`witness_via_sdr` over `chain2Order_wf`.
-/

namespace MachLib.ChainExp2Reducer

open MachLib.MultiPolyMod MachLib.PfaffianChainMod MachLib.ChainExp2Measure

/-- The lex order on the chain-aware nested measure (`Nat × (Nat × Nat)`). -/
abbrev nestedLT : Nat × (Nat × Nat) → Nat × (Nat × Nat) → Prop :=
  LexProd.lexProd (· < ·) (LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·))

/-- The chain-aware measure of a *chain-2* Pfaffian function — `chain2Measure` of its underlying
`MultiPoly 2` (cast from `MultiPoly f.n` via `f.n = 2`). -/
noncomputable def fnMeasure (f : PfaffianFn) (hn : f.n = 2) : Nat × (Nat × Nat) :=
  chain2Measure (hn ▸ f.poly)

/-- **The chain-2 reduce step (Path B).** Mirrors `PfaffianFn.ReduceStep`, but `lex_decrease` is the
strict descent of the *chain-aware* measure `fnMeasure` — i.e. **Phase 2**. -/
structure Chain2ReduceStep (f : PfaffianFn) (hn : f.n = 2) where
  result : PfaffianFn
  result_hn : result.n = 2
  counter : Nat
  /-- **Phase 2 lives here.** -/
  lex_decrease : nestedLT (fnMeasure result result_hn) (fnMeasure f hn)
  witness : PfaffianFn.IsKhovanskiiReducible f result counter

/-- **The chain-2 stepwise-decrease reducer (Path B).** Given a chain-2 function whose top-variable
degree is positive (`(fnMeasure f hn).1 > 0`), produce a `Chain2ReduceStep`. Supplying this — with the
`lex_decrease` of Phase 2 — is what closes chain-2 (then Phase 4 assembles it over `chain2Order_wf`). -/
abbrev Chain2SDR : Type :=
  ∀ (f : PfaffianFn) (hn : f.n = 2), 0 < (fnMeasure f hn).1 → Chain2ReduceStep f hn

/-- The chain-2 reduction order on functions is well-founded — pulled back from the keystone
`natTripleLex_wf` along the measure. (`fnMeasure` over the fixed `hn : f.n = 2`.) This is the
well-founded backbone the Phase-4 reducer recursion will run on, independent of the flat framework
measure. -/
theorem nestedLT_wf : WellFounded nestedLT := LexProd.natTripleLex_wf

end MachLib.ChainExp2Reducer
