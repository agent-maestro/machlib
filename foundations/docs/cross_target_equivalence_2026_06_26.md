# Toward proven cross-target equivalence — a verified f64 forward-error bound

*2026-06-26*

Forge's competitive position rests on a span — one EML source → software,
GPU, FPGA, and machine-checked proof — and on **cross-target equivalence**:
the claim that all those targets compute the *same function*. Until now that
claim has been **regression-tested**, not proven: the engine's conformance
harness samples `WGSL ≈ Rust` at `1e-6` over random inputs (176 `assert_close`
calls). Sampling can miss a discrepancy; a proof cannot.

This note records the first rung of *proving* it: a verified forward-error
bound relating a kernel's IEEE-754 `f64` evaluation to its exact `Real`
semantics, in [`MachLib.FPModel`](../MachLib/FPModel.lean) — Mathlib-free,
`sorryAx`-free.

## Why this is tractable (and not CompCert)

General compiler verification (CompCert, CakeML) is a multi-year effort
because the source language has loops, mutable memory, and aliasing — the
correctness statement is a semantics-preservation theorem over an imperative
trace. **EML has none of that.** A kernel is straight-line scalar math with a
bounded chain order. So "all targets compute the same function" is not a
semantics-preservation theorem — it is a **closed-form expression bound**. The
restriction of the source language is exactly what makes equivalence provable.

## The model — one axiom, the standard model of FP arithmetic

We adopt the *standard model* (Higham, *Accuracy and Stability of Numerical
Algorithms* §2.2): a correctly-rounded operation returns the exact result
perturbed by a relative error of at most one unit roundoff `u` (for IEEE
binary64, `u = 2⁻⁵³`). We axiomatize exactly that — three lines (`u`,
`0 ≤ u`, `u ≤ 1`) — in the same single-axiom, Mathlib-free spirit MachLib
already uses for `abs_add` / `abs_mul`:

```
Rounds fl e  :=  ∃ δ, -u ≤ δ ∧ δ ≤ u ∧ fl = e · (1 + δ)
```

A kernel's `f64` evaluation is any value obtained by rounding at each node;
the theorems quantify over *every* such rounding (a universal forward bound,
not a sampled one).

## The result

For `length_sq` — `x² + y²` and the full `vec3` `x² + y² + z²` — every `f64`
evaluation (round each product, then each sum) satisfies

> `|fl(length_sq) − length_sq| ≤ ((1+u)ⁿ − 1) · length_sq`

with `n` the rounding depth (`2` and `3`). That is the *tight* relative bound;
to first order it is `n·u ≈ 2⁻⁵²`. Proven by two-sided propagation of the
per-op bound through the expression tree, closed with MachLib's `mach_mpoly`
normal-form tactic for the polynomial glue. `#print axioms` shows only
`propext`, MachLib's `Real` arithmetic base, and the three `u` axioms — no
`sorryAx`, no Mathlib.

`length_sq` is the clean case **on purpose**: all summands are `≥ 0`, so there
is no catastrophic cancellation and the relative bound stays small. That is
also the honest scope boundary — for cancellation-prone kernels (a difference
of nearly-equal large quantities) the *relative* bound degrades, and a
different (conditioned, or interval) statement is required. We claim the
straight-line nonneg-accumulation fragment, not all of numerics.

## What it buys, concretely

MachLib already proves `vec3_length_sq_nonneg` — the **exact `Real`** value is
`≥ 0`. This bound says the **shipped `f64`** value is within `≈ 3u` of that
exact value. Chained: the Rust output a user actually runs is non-negative up
to three unit roundoffs of a quantity *proven* non-negative — a statement no
amount of `assert_close` sampling can make.

This is the second leg of the moat next to binding integrity. Binding
integrity (the `tree_hash` gate) proves the Lean obligation is *about the same
expression* every target lowers. This proves that the lowered `f64`
*evaluates within a bound* of that expression's exact value. Together they
move "Forge regression-tests its targets" toward "Forge **proves** them
equivalent" — for the fragment where that is honestly provable.

## Next rungs

- More kernels: `dot`, `lerp`, the `mat4`/`quat` algebra (all straight-line,
  mostly nonneg or well-conditioned).
- A `WGSL`/`f32` instance (`u = 2⁻²⁴`) — the GPU leg, same model, larger `u`.
- The harder, honest frontier: a *conditioned* bound for cancellation-prone
  kernels, and eventually the EML→RTL leg (`Formal equivalence proofs: EML
  source = synthesized gates`, roadmap Phase 3).

## Reproduce

```bash
git clone https://github.com/agent-maestro/machlib
cd machlib/foundations
lake build MachLib.FPModel
lake env lean -e '#print axioms MachLib.Real.length_sq3_fwd_error'   # no sorryAx
```
