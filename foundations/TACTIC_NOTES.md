# Tactic notes — what's NOT available in this Mathlib-free codebase

MachLib is intentionally Mathlib-free (Lean 4 core + this project's own axioms/lemmas only). Some
tactics that exist in vanilla Lean 4 or that read as "obviously standard" are actually **Mathlib**
tactics and are not available here. Each entry below cost a failed build to discover once; recorded
so the next session doesn't pay that cost again.

## Confirmed unavailable (Mathlib tactics, not Lean 4 core)

- **`by_contra`** — use `Classical.byContradiction (fun h => ...)` instead, or an explicit
  `rcases lt_total ... with h | h | h`-style case split when the negation has a concrete shape.
- **`push_neg`** — no automated negation-pushing. Unfold negations by hand (`intro`, `rcases` on
  `lt_total`/`le_iff_lt_or_eq`, or a small private `lt_of_not_le`-style helper — see
  `CertcomTotalErrorFloor.lean` for a worked example).
- **`set x := e with hx`** — no local-definition-with-equation tactic. Either inline the expression
  `e` everywhere instead of naming it, or use a plain term-level `let` (which Lean 4 core does
  support, but its bindings are only definitionally — not propositionally — transparent, so
  `rw` often can't see through it; inlining is usually less friction than fighting that).

Found across: `sin_not_tailSign`-era work (pre-dates this list), `CertcomTotalErrorFloor.lean`
(`by_contra`/`push_neg`, 2026-07-22), `ContinuityDivergenceBarrier.lean` (`set`, 2026-07-22).

## Confirmed bug — `mach_mpoly` fails on lambda-bound atoms (3 data points, diagnosed)

`mach_mpoly [atoms...]` fails with `unknown identifier` / `unknown free variable` whenever an atom
in the list is a variable bound WITHIN the tactic proof itself — via `intro`, `fun` (including a
`refine ⟨.., fun y hy => ?_⟩` binder), or similar — rather than declared in the theorem's own
top-level parameter list. It works FINE when every atom is a plain theorem-level parameter
(`theorem foo (a b : Real) ...`). Confirmed three times now, same failure mode each time:
`ContinuityDivergenceBarrier.lean` (2026-07-22), and twice more in `CompactIntervalNonApproximation.
lean` (2026-07-22) — `continuousAt_neg`'s `mach_mpoly [f y, f x]` inside a `refine ⟨δ, hδ, fun y hy
=> ?_⟩` body (`y` is the `fun`-bound variable), and `induced_zero_of_eps_close'`'s `hclose'`'s
`mach_mpoly [g x, TARGET x]` inside an `intro x hxa hxb` body (`x` there is `intro`-bound, not the
theorem's own `x1`/`x2` parameters). By contrast, `neg_lt_neg'`'s `mach_mpoly [a, b]` succeeded
immediately, using `{a b : Real}` straight from the theorem's own binder list.

**Workaround / rule of thumb:** use `mach_mpoly` only for goals built entirely from theorem-level
parameters; use `mach_ring` for anything touching an `intro`/`fun`/`refine`-bound local instead.
`mach_ring` has its own separate, milder failure mode (leaves an associativity-shaped residual on
some goals rather than erroring outright) — when that happens on a theorem-parameter-only goal,
switching to `mach_mpoly` with the same parameters has closed it cleanly every time so far
(`neg_lt_neg'` is the example). Diagnosed enough to act on directly now rather than rediscover
per-file. A genuine upstream fix belongs in `mach_mpoly`'s custom `elabTerm` call
(`MPolyRing.lean`) — worth doing if a future round needs `mach_mpoly` specifically (not just
`mach_ring`) inside a lambda-bound scope; not yet needed since `mach_ring`/explicit algebra have
covered every such case so far.
