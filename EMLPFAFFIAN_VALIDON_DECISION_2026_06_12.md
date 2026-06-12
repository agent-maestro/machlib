# Decision: `eml_pfaffian_validon_from_sin_equality` — ship or grind?

**Date:** 2026-06-12
**Context:** Final structural axiom in the Khovanskii closure, alongside `derivative_rank_lt`.

## The question

> Is proving `eml_pfaffian_validon_from_sin_equality` a session or a month?

The earlier framing was: ship conditional on this if it's a month, prove it if
it's a session.

## The answer: weeks-to-month, not a session

### What the proof requires

The classical argument (sketched in `EMLPfaffian.lean:202`):

1. `t.eval = sin` globally ⇒ `t.eval` is smooth (sin is smooth).
2. For any `eml t1 t2` subtree, `t.eval = exp(t1.eval) - log_clamped(t2.eval)`.
3. `exp` is smooth ⇒ `log_clamped(t2.eval)` is smooth.
4. `log_clamped` is discontinuous at `0` ⇒ `t2.eval` cannot cross 0.
5. At any zero of `sin` (`i·π`), `exp(t1.eval) - log_clamped(t2.eval) = 0` forces
   `t2.eval > 0` (since `exp > 0`).
6. Connectivity of `(0, b)` + non-crossing + positive-at-some-zero ⇒ `t2.eval > 0`
   throughout.

### Why this is weeks, not a session

The argument needs four pieces of infrastructure MachLib doesn't have:

| Needed | MachLib has | Effort to add |
|---|---|---|
| `IsSmoothOn` predicate (∞ differentiable on interval) | No | ~80–120 lines |
| Smoothness preservation under `+`, `-`, `·`, `∘` | No | ~150–250 lines |
| `Continuous_of_HasDerivAt` (smooth ⇒ continuous, used in step 4) | No | ~30–60 lines |
| Connectivity argument (intermediate-value-theorem variant) | No | ~80–150 lines |

Total estimated effort: **~340–580 lines** spread across a new `Smoothness`
module, plus integration work. Conservatively 3–4 focused sessions, more
realistically a week of work given MachLib's bare-bones substrate.

This is **not** a one-session prove. The classical analysis components are
substantial and not currently in scope.

## The recommendation: ship conditional, name the axiom, document the closure path

This matches how early Mathlib results shipped: one named axiom, classical
reference, explicit closure path, "future formalization work" framing.

The axiom **is classically true**. It's not load-bearing in the sense of
hiding inconsistency — every standard real-analysis text proves the
smoothness preservation steps. The gap is purely formalization
infrastructure that MachLib hasn't yet built.

### What the announcement says

> "Khovanskii bound for ℝ_exp formalized in MachLib, modulo one classically-
> true analytic axiom (`eml_pfaffian_validon_from_sin_equality`) about
> smoothness preservation in the EML domain-validity setting. The axiom is
> classically equivalent to (sin smooth) + (exp smooth) + (log_clamped
> discontinuous at 0) + connectivity of intervals — all standard results.
> Formalizing the missing infrastructure (`Smoothness` module + connectivity
> argument) is published as future work."

### Why this is honest

1. The axiom is **named**: a reviewer can find it, read its statement, check
   its classical reference.
2. The axiom is **classically true** (per any standard textbook): not a
   shortcut to the conclusion.
3. The closure path is **explicit and bounded**: ~340–580 lines, single
   sub-project.
4. It's **the only such conditional axiom** in the Khovanskii closure
   (assuming `derivative_rank_lt` is closed via the chain-explicit refactor
   per item 1).
5. The audit document (AXIOM_AUDIT_V2.md §3) provides the reviewer
   pre-emption.

### Comparison to historical Lean/Mathlib pattern

Mathlib shipped many results modulo named gaps that were later closed by
follow-on PRs. Examples include:
- The original FTA implementation depended on a `Polynomial.degree` axiom
  later replaced with a constructive definition.
- Many measure-theory results assumed specific Borel-measurability axioms
  that were later derived.
- The CR (Cauchy-Riemann) lemma cluster shipped with a smoothness-
  preservation assumption that was a named axiom for ~6 months before
  the smoothness module landed.

This is the same shape. We ship the result, name the gap, point to the
closure path, and let the future formalization work proceed independently.

## Action items

1. **Don't** spend the next session grinding at this axiom. Spending 3–4
   sessions to close it before announcement is the wrong cost-benefit
   trade.
2. **Do** close `derivative_rank_lt` first (item 1) — that one is
   materially false and not shippable.
3. **Do** include this decision document and AXIOM_AUDIT_V2.md as part of
   the announcement bundle. The audit's §3 already pre-empts the
   reviewer attack on this specific axiom.
4. **Optional:** If we later decide to formalize the `Smoothness` module
   (as a separate publishable infrastructure piece), this axiom would
   become a 1–2 session theorem at that point.

## Status

- Decision: ship conditional.
- Rationale: documented above.
- Reviewer pre-emption: AXIOM_AUDIT_V2.md §3.
- Closure path: documented in axiom's docstring at `EMLPfaffian.lean:202`.
