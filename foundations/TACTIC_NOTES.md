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

## Watch list — not a confirmed bug, but a pattern with 2 data points

- **`mach_mpoly [atoms...]`** has failed twice now in ways `mach_ring`/manual algebra didn't:
  (1) the `sub_sub_cancel_shift` case (cont. 71, `WitnessResidualContinuousTargetMetaLemma.lean`) —
  `mach_ring` failed the moment an unrelated `Real → Real`-typed variable sat in the local context;
  `mach_mpoly` succeeded there. (2) `ContinuityDivergenceBarrier.lean` (2026-07-22) — the reverse:
  `mach_mpoly [x0, yy]` failed with a confusing `unknown identifier` / `unknown free variable` error
  on a specific local-context shape, where plain `mach_ring` had *partially* worked (left an
  associativity-shaped residual) and explicit `add_assoc`/`add_left_comm`/`add_neg`/`add_zero`
  closed it cleanly. Root cause NOT identified either time — both were worked around locally, not
  debugged. Two data points in *different directions* (one favors `mach_mpoly` over `mach_ring`,
  one the reverse) is a pattern-candidate, not yet a diagnosis. **If a third local-context shape
  trips either tactic, stop working around it and treat it as a genuine context-sensitivity bug in
  the tactic's implementation (`MPolyRing.lean`/`Linarith.lean`) — the fix belongs upstream in the
  tactic, not in another call-site workaround.**
