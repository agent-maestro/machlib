import MachLib.KhovanskiiReduction
import MachLib.ChainExp2Measure
import MachLib.ChainExp2SDR
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

/-! ## Phase 2 — the reduce-step descent, structural half

The chain-2 reduce step is `chainTotalDeriv (IterExpChain 2)` (the `c = 0` `scaledReduction`). Phase 2
must show it strictly decreases `chain2Measure` in `nestedLT`. The measure is the nested lex
`(degreeY₁, singleExpMeasure(lcY₁))`. This section discharges the **structural half**: the first
component (`degreeY₁`) is *preserved* by the reduce, so the nested-lex descent collapses to a descent
of the *second* component alone (`singleExpMeasure(lcY₁ ·)`). That second-component descent is the
single deep seam left — the single-exp reduce descending its own measure on `lcY₁` — isolated here as
the hypothesis `hsnd`. -/

open MachLib.ChainExp2SDR
open MachLib.PfaffianChainMod.PfaffianFn
open MachLib.IterExpChainMod

/-- The underlying `MultiPoly 2` of the `c = 0` `scaledReduction` for the canonical chain-2 chain — i.e.
`PfaffianFn.scaledReduction 0`'s `poly` (`f' − 0·f`). Stated directly on the poly so the structural
descent reasoning is independent of the `PfaffianFn`/`hn`-cast plumbing (which Phase 3 threads back in).
This is the *exact* shape the proven seam `chain2_polyTrueDegreeStrict_scaledReduction_zero_lt` operates
on — `sub (cTD p) (mul (const 0) p)`, **not** bare `cTD p`. -/
noncomputable def reducePoly (p : MultiPoly 2) : MultiPoly 2 :=
  MultiPoly.sub (chainTotalDeriv (IterExpChain 2) p) (MultiPoly.mul (MultiPoly.const (0 : Real)) p)

/-- **First component preserved (real reduce poly).** The top-chain-variable degree `degreeY₁` — the
first component of `chain2Measure` — is unchanged by the chain-2 reduce `reducePoly`. Both summands of
`reducePoly` keep the `y₁`-degree: `cTD` preserves it (`degreeY1_chainTotalDeriv_eq_IterExp2`) and the
`mul (const 0)` term contributes `0 + degreeY₁`, so the `Nat.max` over the `sub` is `degreeY₁ p`. -/
theorem chain2Measure_fst_reducePoly (p : MultiPoly 2) :
    (chain2Measure (reducePoly p)).1 = (chain2Measure p).1 := by
  show Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (chainTotalDeriv (IterExpChain 2) p))
               (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) (MultiPoly.mul (MultiPoly.const (0:Real)) p))
     = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
  rw [degreeY1_chainTotalDeriv_eq_IterExp2 p]
  show Nat.max (MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
               (0 + MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p)
     = MultiPoly.degreeY (⟨1, by omega⟩ : Fin 2) p
  rw [Nat.zero_add]; exact Nat.max_self _

/-- **Phase 2 reduced to the second-component descent.** Given that the chain-2 reduce strictly
decreases the *second* component of `chain2Measure` (`singleExpMeasure(lcY₁ ·)`), the full `nestedLT`
descent follows, because the first component (`degreeY₁`) is preserved (`chain2Measure_fst_reducePoly`).
This is the exact poly-level content of the `Chain2ReduceStep.lex_decrease` field; the open obligation is
the hypothesis `hsnd`.

NOTE (the seam is *not* a clean unconditional `hsnd`): `singleExpMeasure(lcY₁ p) = (degreeY₀(lcY₁ p),
trueDeg(…))`, and `degreeY₀(lcY₁ ·)` can *increase* under this reduce when `lcY₁ p` is a constant in the
chain values — e.g. `p = y₁`: `lcY₁ p = 1` (inner measure `(0,0)`), but `lcY₁ (reducePoly p) = y₀` (inner
`(1,…)`), so the second component goes *up*. So `hsnd` does **not** hold for the naive `reducePoly` on
every `p` with `degreeY₁ > 0`; the reducer must case-split on whether `lcY₁ p` is non-constant
(seam-style reduce descends the inner `trueDeg`) vs constant (a distinct degreeY₁-lowering move). The
proven seam `chain2_polyTrueDegreeStrict_scaledReduction_zero_lt` moreover descends the *flat-projection*
`trueDeg(mP2PFL(lcY₁ ·))`, which differs from the nested `singleExpMeasure`'s inner `trueDeg(mP2PFL(lcY₀
(lcY₁ ·)))` — bridging that flat↔nested gap is part of the remaining seam. -/
theorem chain2_reduce_nestedLT_of_snd (p : MultiPoly 2)
    (hsnd : LexProd.lexProd (· < · : Nat → Nat → Prop) (· < ·)
              (chain2Measure (reducePoly p)).2 (chain2Measure p).2) :
    nestedLT (chain2Measure (reducePoly p)) (chain2Measure p) :=
  LexProd.lexProd_of_snd (chain2Measure_fst_reducePoly p) hsnd

/-! ## Phase 2 — machine-checked OBSTRUCTION: the c=0 reduce does NOT descend the nested measure

The structural half collapses Phase 2 to the second-component obligation `hsnd`. **But `hsnd` is *false*
for the naive `reducePoly`** (the c=0 `scaledReduction`). Reason: the chain-2 total derivative injects a
`y₀` factor into the `y₁`-leading coefficient (because `y₁' = y₀·y₁`), so `degreeY₀(lcY₁ ·)` — the inner
*first* component of `singleExpMeasure` — strictly *increases* rather than ties/decreases.

Witness `p = y₁`: `lcY₁ p = 1` (inner `degreeY₀ = 0`), but `cTD p = y₀·y₁` so `lcY₁ (reducePoly p) =
y₀·1 − 0·1` (inner `degreeY₀ = 1`). With `degreeY₁` preserved, the nested-lex descent therefore *cannot*
hold. The two numeric facts and the no-go are machine-checked below (all `rfl`/elementary).

**Consequence (the real Phase-2 finding):** the correct chain-2 reduce must reduce `lcY₁` *as a single-exp
object* — without injecting `y₀` — which the chain total derivative does not do; the framework has no such
operation yet (and `dropLeadingY` is `MultiPoly 1`-only, so the trim arm doesn't port for free either).
Phase 2's reduce arm is thus genuine new construction, not mechanical mirroring. -/

/-- The `y₁`-monomial obstruction witness `p = y₁`. -/
private def yOne : MultiPoly 2 := MultiPoly.varY ⟨1, by omega⟩

/-- Inner first component (`degreeY₀` of `lcY₁`) of the original `p = y₁` is `0` (`lcY₁ (y₁) = 1`). -/
theorem chain2_inner_degreeY0_yOne : (chain2Measure yOne).2.1 = 0 := rfl

/-- Inner first component of the reduced `p = y₁` is `1` — it strictly *increased* (`lcY₁` picked up a
`y₀` from `y₁' = y₀·y₁`). -/
theorem chain2_inner_degreeY0_reduce_yOne : (chain2Measure (reducePoly yOne)).2.1 = 1 := rfl

/-- **The obstruction, machine-checked.** The naive c=0 reduce `reducePoly` does *not* strictly decrease
`chain2Measure` at `p = y₁`: the first component (`degreeY₁`) ties (`chain2Measure_fst_reducePoly`) while
the inner second component (`degreeY₀(lcY₁)`) goes `0 → 1`. Hence Phase 2's `hsnd` is unprovable for
`reducePoly` — the chain-2 reduce must be a genuinely different operation. -/
theorem chain2_reducePoly_not_nestedLT :
    ¬ nestedLT (chain2Measure (reducePoly yOne)) (chain2Measure yOne) := by
  intro h
  rcases h with h1 | ⟨_, h2⟩
  · -- first component preserved ⇒ `a < a` impossible
    rw [chain2Measure_fst_reducePoly yOne] at h1
    exact Nat.lt_irrefl _ h1
  · -- inner second component went 1 vs 0 ⇒ neither `1 < 0` nor `1 = 0`
    rcases h2 with h2a | ⟨h2eq, _⟩
    · rw [chain2_inner_degreeY0_reduce_yOne, chain2_inner_degreeY0_yOne] at h2a; omega
    · rw [chain2_inner_degreeY0_reduce_yOne, chain2_inner_degreeY0_yOne] at h2eq; omega

end MachLib.ChainExp2Reducer
