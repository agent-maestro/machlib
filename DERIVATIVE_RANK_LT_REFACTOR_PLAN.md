# derivative_rank_lt closure: scoping doc

**Status:** axiom in `MachLib/KhovanskiiLemma.lean:580` (last remaining
KhovanskiiLemma structural axiom). Materially false as stated:
`exp_atom.derivative = exp_atom` ⇒ rank unchanged ⇒ strict `<` unprovable.

## Why no in-place patch works

Worked through all 9 `PfaffianExpr` constructors checking whether *any*
rank function defined on the current representation could decrease under
differentiation:

| Constructor | derivative | rank-decrease possible? |
|---|---|---|
| `const c` | `const 0` | vacuous (rank 0, hypothesis fails) |
| `var` | `const 1` | YES (rank 1 → 0) |
| `exp_atom` | `exp_atom` | **NO** — identical structure |
| `log_atom` | `inv var` | NO (both rank 1·1M+1 with current formula) |
| `add f g` | `add f' g'` | depends on subexpressions; not in general |
| `sub f g` | `sub f' g'` | same |
| `mul f g` | `add (mul f' g) (mul f g')` | usually **grows** under sum-based chainOrder |
| `comp f g` | `mul (comp f' g) g'` | similarly grows |
| `inv g` | compound w/ `inv g · inv g` | grows |

The exp_atom case is structurally irreducible: it's an atom with no
internal structure that can shrink. Mathematically, `(e^x)' = e^x` is
the *defining* relation of exp; there is no rank function on the bare
atom that distinguishes "exp before differentiation" from "exp after".

This isn't a formula choice issue — *any* rank function `R : PfaffianExpr → Nat`
satisfies `R(exp_atom.derivative) = R(exp_atom)`, since they're the
same term.

## Why this matters

`pfaffian_zero_count_bound_constructive` uses strong-induction-on-rank
with `derivative_rank_lt` as the well-founded measure. Without rank
decrease, the induction doesn't terminate. So the entire Khovanskii
closure chain inherits this axiom's gap.

The bound *conclusion* is classically true. It's the *induction
strategy* that fails on the current representation.

## What classical Khovanskii actually does

Khovanskii's 1991 proof uses induction on **chain length** n, not on
the derivative. The argument has structure:

1. A Pfaffian function is a polynomial `P(x, y_1, ..., y_n)` where
   each `y_i` satisfies `y_i' = P_i(x, y_1, ..., y_i)` (triangular
   chain relations).
2. Base case (n=0): polynomial in x; FTA bound.
3. Inductive step (n→n-1): for fixed `(y_1, ..., y_{n-1})`, the
   1-parameter family `P(x, y_1, ..., y_{n-1}, t)` is a polynomial in
   `t = y_n`. Apply Rolle iteratively with the chain relation
   `y_n' = P_n(...)` to bound zeros of `P(x, y_1, ..., y_n)` by zeros
   of a function with strictly smaller `(n-1)`-chain.

The reduction is NOT "differentiate and recurse on derivative". It's
"compose with chain relation, project to smaller chain, recurse".

Our `PfaffianExpr.derivative` matches the *symbolic* differentiation
rules but lacks the chain-projection operation. The representation
doesn't expose `(y_1, ..., y_n)` as discrete variables — exp_atom is
opaque, you can't "substitute its chain relation" structurally.

## What the refactor needs

A representation that exposes:

1. **Chain structure**: a list of n chain variables `y_1, ..., y_n`
   with their relations `y_i' = P_i(x, y_1, ..., y_i)`.
2. **Multivariate polynomials**: `MultiPoly` over `(n+1)` variables
   (x plus chain vars), with degree tracking per variable.
3. **Chain reduction**: an operation `reduce_chain : PfaffianFn → PfaffianFn`
   that projects to a smaller chain, with documented degree growth.

Proposed new representation:

```lean
-- New types
inductive MultiPoly (n : Nat) : Type where
  | const : Real → MultiPoly n
  | varX  : MultiPoly n           -- the independent variable x
  | varY  : Fin n → MultiPoly n   -- chain variable y_i
  | add   : MultiPoly n → MultiPoly n → MultiPoly n
  | sub   : MultiPoly n → MultiPoly n → MultiPoly n
  | mul   : MultiPoly n → MultiPoly n → MultiPoly n

structure PfaffianChain where
  n         : Nat
  -- relations[i] : MultiPoly i represents P_i(x, y_1, ..., y_i)
  relations : (i : Fin n) → MultiPoly i.val.succ
  -- evals[i] : the actual function for y_i (= exp x, log x, 1/x, ...)
  evals     : Fin n → (Real → Real)
  -- coherence: ∀ i, evals i satisfies y' = relations i applied
  ...

structure PfaffianFn where
  chain : PfaffianChain
  poly  : MultiPoly chain.n
```

The bound theorem then inducts on `chain.n`, with chain-projection
as the reduction step.

## Effort estimate

| Phase | Lines | Sessions |
|---|---|---|
| MultiPoly type + ops (add, mul, eval, degree) | 150–250 | 0.5–1 |
| PfaffianChain + PfaffianFn + coherence | 100–200 | 0.5 |
| Conversion from old PfaffianExpr → PfaffianFn | 100–150 | 0.5 |
| Update eml_pfaffian + EMLPfaffian | 100–150 | 0.5 |
| New bound proof via chain-length induction | 250–400 | 1–2 |
| Update consumers (sin barrier etc.) | 50–100 | 0.5 |
| **Total** | **750–1250** | **3.5–5** |

This is a real chunk. The closure path is well-understood but
the execution is multi-session.

## Phased approach

If we don't want to commit to all 5 sessions at once, a phased path:

**Phase 1 (1 session):** define `MultiPoly` and its basic ops as a
new module. Don't change anything else yet. Net: zero axiom drop,
but type infrastructure ready.

**Phase 2 (1 session):** define `PfaffianChain` + `PfaffianFn`,
prove eval/degree machinery. Net: zero axiom drop.

**Phase 3 (1 session):** prove the conversion `PfaffianExpr → PfaffianFn`
for the cases that arise from `eml_pfaffian`. The conversion expands
`exp_atom` into a polynomial in `y_1 = exp x` with explicit chain
structure.

**Phase 4 (1–2 sessions):** prove the new bound theorem via
chain-length induction. Replace `pfaffian_zero_count_bound_constructive`'s
proof with the new strategy. `derivative_rank_lt` axiom can be
deleted at this point.

**Phase 5 (0.5 session):** update sin barrier and other consumers
to use the new bound theorem (signature may change slightly).

After phase 4, `derivative_rank_lt` is fully closed and the
PfaffianExpr inductive type can be retired or kept as a
"legacy/simpler" representation.

## Alternatives considered

**(a) Different rank function:** ruled out per the table above.
No rank function on the current PfaffianExpr distinguishes exp_atom
from its derivative.

**(b) Add hypothesis "no exp_atom" to `derivative_rank_lt`:** breaks
sin barrier (eml_pfaffian uses exp_atom for every `eml t1 t2` subtree).

**(c) Axiomatize `PfaffianFunction.zero_bound` directly:** regresses
to the pre-sprint state. The whole point was to eliminate that black
box.

**(d) Skip Khovanskii induction, use a closed-form bound directly:**
the closed-form bound's proof IS the Khovanskii induction. Can't
get one without the other.

## Recommendation

The chain-explicit refactor is the only path that genuinely closes
`derivative_rank_lt`. It's worth doing because:

1. It eliminates the last structural axiom in the Khovanskii closure.
2. It aligns MachLib's Pfaffian formalization with the classical
   literature, making future reviewers' job easier.
3. The conversion is mechanical once `MultiPoly` exists.
4. EMLPfaffian's structure already separates concerns nicely; the
   new representation should fit without disrupting it.

Sequencing: phases 1–3 produce zero axiom drop but build the
infrastructure. Phase 4 is the payoff. The user can pause between
any two phases.

**Estimated to landing:** 3.5–5 focused sessions, ~750–1250 lines.

## Status as of 2026-06-12

- Khovanskii closure chain: 3/4 structural axioms discharged
- `derivative_rank_lt` remains as the last axiom in `KhovanskiiLemma.lean`
- This refactor is scoped but not started

Prior commits in this thread:
- `e432c20` close derivative_eval via inv + IsValidAt
- `f401a4e` close sin barrier sorry via ValidOn bridge + analytic axiom
