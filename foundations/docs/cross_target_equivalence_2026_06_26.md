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

## Update — the conditioned (mixed-sign) case, precision-generic

`length_sq` is the clean case because every summand is `≥ 0`. The follow-up
handles the cancellation-prone case and decouples the precision:

- **`RoundsW w`** — the standard model parameterized by the precision's unit
  roundoff `w` (f64 `= 2⁻⁵³`, f32/WGSL `= 2⁻²⁴`, bf16 `= 2⁻⁸`). One theorem,
  every target. `#print axioms` on the `w`-parameterized results shows *no* `u`
  axiom at all — they rest only on `propext` + the `Real` base.
- **`dot2_fwd_error`** — the `f64`/`f32` evaluation of `a·b + c·d` (a *mixed-sign*
  sum) is within `(1+w)² − 1 ≈ 2w` of the exact value, **measured against the
  conditioning quantity `|a·b| + |c·d|`**, not `|result|`. This is the honest
  statement: if the result cancels to ≈ 0, the *relative* error is unbounded,
  but the *absolute* error stays bounded by the (uncancelled) magnitudes. Proven
  by abs-propagation (`roundsW_abs`, `abs_le_one_add`, triangle inequality).

The split is the point: nonneg-accumulation kernels (`length_sq`, attenuation,
energies) get a *relative* bound; mixed-sign kernels (`dot`, residuals) get an
*absolute* bound against their condition number. Both are honest; neither is a
blanket "verified."

## The kernel set so far

Five forward-error theorems, the complete `vec3` scalar algebra:

| kernel | bound | form |
| --- | --- | --- |
| `length_sq2` / `length_sq3` | `(1+u)ⁿ − 1` × `length_sq` | **relative** (nonneg summands) |
| `dot2` / `dot3` | `(1+w)ⁿ − 1` × `Σ|aᵢ·bᵢ|` | **conditioned** (mixed sign) |
| `lerp` | `(1+w)³ − 1` × `(|a| + |(b−a)·t|)` | **conditioned** (subtraction) |

`dot3` *reuses* `dot2` for its inner subtree, and `lerp` reuses the same
`roundsW_abs` + `abs_le_one_add` + triangle machinery — the conditioned method
composes. `dot2/dot3/lerp` are precision-generic (parameterized by `w`; `#print
axioms` shows no `u`), so each is simultaneously the f64 and the f32/WGSL bound.

## The loop closed — `cross_target`

Everything above bounds *target vs exact* (`f64 ≈ Real`, `f32 ≈ Real`). The
thing the conformance harness actually samples is *target vs target* —
`assert_close(gpu_f32, cpu_f64)`. That now follows in one line by the triangle
inequality:

```
cross_target : |r1 − e| ≤ B1  →  |r2 − e| ≤ B2  →  |r1 − r2| ≤ B1 + B2
```

`dot3_cross_target` applies it: the Rust **f64** and WGSL **f32** evaluations of
the same `vec3` dot agree within `B(2⁻⁵³) + B(2⁻²⁴)` — the sum of their
forward-error bounds. The `1e-6` the harness checks empirically is now a
*theorem*, parameterized over both precisions. (Deriving it also added the
standard abs toolkit MachLib was missing — `le_abs_self`, `neg_le_abs`,
`le_of_abs_le`, `abs_le_of`, `cross_target`.)

That is the moat sentence, earned: **Forge does not just regression-test that
its targets agree — it proves a bound on their disagreement.**

## Next rungs

- `mat4`/`quat` algebra (matrix-multiply cells are short dot products — the
  `dot` machinery applies) and the longer accumulations.
- A concrete numeric `f32`/`f64` instance (instantiate `w := 2⁻²⁴ / 2⁻⁵³` and
  evaluate the bound) once the `Real` pow/division lemmas are in.
- The EML→RTL leg (`Formal equivalence proofs: EML source = synthesized gates`,
  roadmap Phase 3) — the hardware end of the same chain.

## Reproduce

```bash
git clone https://github.com/agent-maestro/machlib
cd machlib/foundations
lake build MachLib.FPModel
lake env lean -e '#print axioms MachLib.Real.length_sq3_fwd_error'   # no sorryAx
```
