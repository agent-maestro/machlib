# certcom Theorem A — scoping the rounding frontier (2026-07-10)

A decomposition pass on the EML→C correctness stack, to find the **smallest honest next theorem**.
Everything below was verified by `#print axioms` on the real artifact, not read off docstrings.

## Headline finding

The rounding/accumulation model is **not unbuilt — it is proved, sorryAx-free, cancellation
included.** The frontier is not "build the forward-error model." It is **grounding** it: the entire
tower is proved `∀ toR, FPBridge toR → …`, and `FPBridge` (the standard model of floating-point) is
inhabited only by the degenerate `toR = fun _ => 0`. The smallest honest step is to name + register
the `FPBridge` grounding and instantiate the already-proved tower on a real kernel.

## What's proved (verified `#print axioms`, all sorryAx-free)

| Layer | Certificate | Footprint |
|---|---|---|
| **T1** translation validation | `Certcom.runProg_correct` (EMLToC) | emitted C ≡ EML source through calls/while/state |
| **T2** runtime discharge | `Certcom.runProg_correct_std` (EMLToCRuntime) | `[propext, Quot.sound]` — exact Float, no rounding; `mg_*` reduced to a shared primitive basis |
| **T3** composite error | `cosh/eml_fwd_reduces_to_*` (CompositeRuntimeError) | composites inherit ULP error from primitives |
| **Fold: arithmetic** | `Certcom.pipeline_arith` (AbsoluteFold) | **every** lit/var/+/−/× tree, **cancellation included, no sign hypothesis** |
| **Fold: cancelling kernel** | `Certcom.pipeline_det` (AbsoluteBridge) | the 2×2 determinant `x·y − z·w` |
| **Fold: log/sqrt** | `Certcom.pipeline_pos_over_arith` (AbsoluteFoldPos) | one-sided domain, positive-lower-bound hypothesis |
| **Fold: local transcendental** | `pipeline_{exp,log}_of_arith` (AbsoluteFoldLocal) | one exp/log layer over arithmetic |
| **Fold: nested glob-Lipschitz** | `pipeline_nested_glob/std` (CertifyNested) | fully recursive sin/cos/tanh/atan/abs |
| **Float↔Real interface** | `FPBridge` + `length_sq2_bridge` (FloatRealBridge) | the bridge + a worked `x²+y²` end-to-end certificate |

All fold certificates rest on: the `MachLib.Real` field/order axioms (witnessed against ℝ by
Theorem B / the axiom-ledger), the roundoff constants `u`/`u_nonneg`/`u_le_one`, and — as a
**discharged hypothesis, not an axiom** — `FPBridge toR`.

> **Stale docstring flagged:** `FloatRealBridge.lean`'s header still calls general cancelling
> accumulation "the remaining CompCert-scale T3 work, not claimed here." `AbsoluteFold.pipeline_arith`
> has since closed exactly that for the arithmetic fragment (cancellation included, sorryAx-free).
> Update that header when next in the file.

## The trust base — where it actually bottoms out

`FPBridge toR` (FloatRealBridge.lean) is the keystone:

```lean
structure FPBridge (toR : Float → MachLib.Real) : Prop where
  add : ∀ a b : Float, RoundsW u (toR (a + b)) (toR a + toR b)   -- correctly rounded, rel err ≤ u
  sub : ∀ a b : Float, RoundsW u (toR (a - b)) (toR a - toR b)
  mul : ∀ a b : Float, RoundsW u (toR (a * b)) (toR a * toR b)
  neg : ∀ a : Float, toR (-a) = -(toR a)                          -- IEEE neg is EXACT
```

Its **only inhabitant is the consistency witness** `example : FPBridge (fun _ => 0)`. No faithful
`toR : Float → Real` (the value a double denotes) is inhabited. Lean's `Float` is opaque/`@[extern]`,
so `FPBridge` for the real `toR` **cannot be proved inside Lean** — it is the IEEE-754 standard model,
and must be a hypothesis or a disclosed axiom. This is the precise, honest location of the
"measured, not proved" boundary from the blog.

## The honest open pieces (ranked)

1. **[Keystone] Ground `FPBridge` for a faithful `toR`.** Makes the whole proved tower bite on real
   floats. Two routes:
   - *(hard, Flocq-scale)* formalize binary64 with in-Lean rounding semantics and **prove**
     `FPBridge` — multi-month; needs an FP formalization Lean/Mathlib lacks.
   - *(bounded, honest)* name `realToR : Float → Real` + `real_fpbridge : FPBridge realToR` as a
     single **disclosed axiom** — the standard model, same trust status as `erf` (declared,
     un-witnessable because `Float` is opaque). Then instantiate the proved tower at `realToR`.
2. **[Small proof win] the `neg` node in the closed-form `absErr` fold.** `FPBridge` already carries
   the exact-`neg` field; wiring it into `AbsoluteFold` closes the arithmetic fragment fully (it is
   currently +/−/× ; unary neg is the one missing node). Pure Lean, additive.
3. **[Medium] `tr1`/`tr2` nodes in the closed-form (`absErr`) fold.** The existential-`E`
   `AbsoluteFoldNest` already does glob-Lipschitz `tr1`; port it to the closed-form fold.
4. **[Hard, named] full recursive local-Lipschitz nesting** (exp/log of subtrees that themselves
   contain local transcendentals) — needs interval arithmetic with directed rounding (range and
   error co-propagated). The genuinely-harder piece, named in `AbsoluteFoldLocal`'s scope note.
5. **[Deep] libm primitive grounding** — the `RoundsW u (toR (mg_f x)) (Real.f (toR x))` specs for
   exp/log/sin/… (the 11 libm calls, the "irreducible trust"). Same status as `FPBridge`.

## ✅ Update (2026-07-10) — keystone executed

The recommended keystone below is **done** (`MachLib/FPGrounding.lean`):
`Certcom.realToR` + `Certcom.real_fpbridge` (the disclosed IEEE-754 axioms) + the theorem
`Certcom.pipeline_det_grounded` — an **unconditional** forward-error certificate on the actual
emitted-C determinant `x·y − z·w`, `#print axioms` resting on exactly `{realToR, real_fpbridge, the
ℝ-witnessed MachLib.Real axioms, u, u_nonneg}`, no `FPBridge` hypothesis, no `sorryAx`. Registered in
`AxiomLedger` under a new `disclosedTrusted` category (distinct from the inert `disclosedUnwitnessed`):
254 axioms pinned, 5 headline footprints ⊆ trusted (66), and a dead-disclosure check confirms the two
axioms are load-bearing in the Theorem-A headline. Next: `tr1` nodes in the closed-form fold, or a
second grounded kernel (e.g. PID), or the Flocq-scale grounding that would derive `real_fpbridge`.

## Recommended first target — the keystone, bounded route

**Name `realToR` + the single disclosed `FPBridge realToR` axiom, instantiate `pipeline_arith` (and
the `x²+y²` / PID kernel) at it, and register the axiom in the AxiomLedger.**

Result: the **first unconditional end-to-end forward-error certificate about actual `Float`
computations** — converting the whole `∀ toR, FPBridge toR → …` tower from "conditional, only a
degenerate witness" into "applies to the real artifact, modulo one honest, universally-accepted,
explicitly-disclosed axiom." Why this beats the pure-proof wins as a *first* step:

- It is the single keystone: one axiom grounds the entire proved tower at once.
- It completes the trust-boundary narrative — `FPBridge` is *the* axiom that structurally cannot be
  witnessed (opaque `Float`), the honest floor under everything, disclosed exactly like `erf`.
- It connects Theorem A to the ledger/witness machinery already built: Theorem A's footprint becomes
  auditable alongside the Khovanskii headlines, and the AxiomWitnessBridge gains a disclosed-but-
  un-witnessable entry with a stated reason (Float opaqueness) — not a hidden gap.
- Scope: ~1–2 sessions, mostly instantiation wiring + one axiom + ledger registration.

Optional warm-up: close the `neg` node (item 2) first — a small pure-Lean proof that fully closes the
arithmetic fragment, satisfying before the keystone.

## Files

`machlib/foundations/MachLib/`: `EMLToC.lean` (T1), `EMLToCRuntime.lean` (T2),
`CompositeRuntimeError.lean` (T3), `FloatRealBridge.lean` (the `FPBridge` interface + worked kernel),
`AbsoluteFold.lean` / `AbsoluteBridge.lean` / `AbsoluteFoldPos.lean` / `AbsoluteFoldLocal.lean` /
`AbsoluteFoldNest.lean` / `CertifyNested.lean` (the fold family). Trust constants: `FPModel.lean`
(`axiom u`, `RoundsW`). Ledger: `machlib/foundations/AxiomLedger.lean`; witness bridge:
`monogate-lean/MonogateEML/AxiomWitnessBridge.lean`.
