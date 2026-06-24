# `mach_linarith` / `mach_nlinarith` — scoping (2026-06-24)

## Why this doc exists

The Forge `@verify(lean)` → MachLib close-rate buildout reached **69%**
substantive on the eml-stdlib corpus (195/282) using only cheap closers:
clamp floors (`le_min`), `domain:`-clause hypotheses, and arms wiring
already-existing bound lemmas (`exp_pos`, `sin/cos/tanh ∈ [-1,1]`, `sqrt_pos`,
`erf`). Those are now **exhausted**. The remaining ~87 open obligations are
dominated by a single shape class that `mach_positivity` fundamentally cannot
close, and the obvious next tool — a linear-arithmetic tactic (`linarith`) — is
**insufficient**. This doc records exactly why, and what a real solution needs,
so the investment decision is made with eyes open rather than by grinding
bespoke axioms (current yield: ~2 obligations per axiom batch).

## The three representative obligations (emitted, verbatim math)

```
smoothstep(t) = 3·t·t − 2·t·t·t          goal: 0 ≤ smoothstep t   given 0≤t≤1
ease_out(t)   = 1 − (1−t)·(1−t)           goal: 0 ≤ ease_out t     given 0≤t≤1
bangbang      = mid + s·amp               goal: u_min ≤ bangbang   given u_max≥u_min
  where s = clamp(error·1e30, −1, 1),  mid = 0.5·(u_max+u_min),  amp = 0.5·(u_max−u_min)
```

What each actually requires:

- **smoothstep** `0 ≤ 3t² − 2t³`. Factor `t²·(3 − 2t)`; `t² ≥ 0` (`sq_nonneg`)
  and `3 − 2t ≥ 0`. The second needs `2t ≤ 2` (scale `t ≤ 1` by 2) **and**
  `2 ≤ 3` (a **decimal-literal comparison**). The factoring itself needs ring
  normalisation. → **nonlinear + literal arithmetic + ring**.
- **ease_out** `0 ≤ 1 − (1−t)²`. Equivalent to `(1−t)² ≤ 1`; true because
  `0 ≤ 1−t ≤ 1`, so squaring is monotone. → **square-monotonicity on an
  interval** (nonlinear) + the interval facts.
- **bangbang** `u_min ≤ mid + s·amp`. The clean proof rearranges to
  `0 ≤ amp·(1 + s)`: `amp = ½(u_max−u_min) ≥ 0` (from `u_max ≥ u_min`) and
  `1 + s ≥ 0` (from the clamp lower bound `s ≥ −1`). → **product of two
  nonnegatives** (nonlinear) + **ring rearrangement** + **`0.5` literal**.

None is linear. `linarith` (even a perfect one) closes **zero** of them. The
real requirement is `nlinarith`-class reasoning (find a nonneg combination of
**products** of hypotheses) over a Real type that supports decimal-literal
order.

## The two hard sub-problems

### A. Decimal-literal arithmetic over an opaque Real
`MachLib.Basic` routes every decimal (`0.5`, `2.0`, `3.0`) through the **opaque**
axiom `realOfScientific`. There is intentionally no concrete model, so
`(2.0 : Real) ≤ (3.0 : Real)` is **not derivable** — only a handful of
hand-written bridges exist (`lit_zero_eq`, `lit_one_eq`,
`realOfScientific_two_dot_zero`, …). linarith/nlinarith both need general
`literal ⊕ literal` comparison and normalisation. Options:
  1. **Axiom family** `realOfScientific_le` keyed on the literals' numeric
     value (clearly true, but a large/looser axiom surface — against the
     "minimise axioms" posture).
  2. **A `norm_num`-style decision procedure** for Real decimals — sound,
     no new axioms beyond a single evaluation lemma, but real metaprogramming.
  3. **Give `realOfScientific` a rational model** (~the omitted Cauchy
     construction) — biggest, but makes all literal facts `decide`-able.
Recommendation: (2) — a focused `mach_norm_num` over `realOfScientific`.

### B. Nonlinear-combination engine
`linarith` = Fourier–Motzkin over linear atoms. These goals need the
`nlinarith` preprocessing step: multiply pairs of hypotheses/atoms (and add
squares `0 ≤ x·x`) to produce new nonneg facts, then run the linear engine.
That is genuine tactic metaprogramming (inspect context, synthesise products,
call a Positivstellensatz-lite search). It also needs ring normalisation
(`mach_ring`, which exists at v1.5 but leaves AC residue — see
[[feedback_machlib_ac_rfl_unlocks_simp_residual]]).

## Phased plan (each phase independently shippable + measurable)

- **Phase 1 — `mach_norm_num` (literal arithmetic).** Decide `a ⊕ b` for Real
  decimal literals. Unblocks the literal halves of every band obligation.
  Closes ~0 alone (needs the engine), but is the prerequisite and is testable
  in isolation. ~1–2 days.
- **Phase 2 — `mach_linarith` (linear engine).** Hypothesis-driven linear
  combination + the `0 ≤ b−a` materialisation from comparison hyps. Closes the
  genuinely-linear stragglers (cancellation shapes like
  `ldo_output_voltage_above_reference`). ~3–5 days.
- **Phase 3 — `mach_nlinarith` (products + squares).** The `nlinarith`
  preprocessing on top of Phases 1–2. Closes smoothstep / ease / bangbang /
  trig×variable bands — the bulk of the remaining ~87. ~1–2 weeks, highest risk.

## Estimated payoff
Phases 1–3 would plausibly take eml-stdlib substantive close-rate from 69% to
the high-80s/low-90s (the residue then = genuinely deep analytic facts:
`silu`'s minimum, `planck`, domain-dependent `density_humid`). But it is a
multi-week, correctness-critical effort — **not** a bolt-on. Decide explicitly
before starting; do not approximate it with unsound shortcuts.

## Phase 3 scoping update (2026-06-24, after reaching 77%)

The polynomial bands (smoothstep, ease, ricochet) were validated end-to-end and
the blocker is now pinned precisely.

**The certificate is Bernstein form, and it works.** A polynomial nonneg on
[0,1] has nonneg Bernstein coefficients, giving a sum-of-nonneg-products:
`smoothstep = 3t² − 2t³ = 3·t²(1−t) + t³`. Each term closes by `mul_nonneg`
(`t² ≥ 0`, `1−t ≥ 0` from `t ≤ 1`, `t ≥ 0`). HAND-PROVED green this way.

**Two sub-techniques confirmed working:**
1. Decimal→sum bridge by DEFEQ COERCION, not `rw`: `rw [realOfScientific_
   three_dot_zero]` fails (`3.0` is `OfScientific.ofScientific 30 true 1`
   syntactically, not `realOfScientific 30 true 1`), but
   `have e3 : (3.0:Real) = 1+1+1 := realOfScientific_three_dot_zero` typechecks
   (defeq) and then `rw [e3]` works. Bridges exist only for 1.0/2.0/3.0 —
   higher literals (6,10,15 for smootherstep) need more, or a general
   `realOfScientific (n*10) true 1 = natCast n` lemma.
2. `mach_norm_num` discharges the `0 ≤ 3.0` coefficient side.

**THE BLOCKER — mach_ring v2.** The SOS rewrite `3t²−2t³ = 3t²(1−t) + t³`
(even after substituting integer 1+1+1 / 1+1 for the decimals) is NOT closed by
`mach_ring` v1.5 — it leaves additive-cancellation residue (the `3t² − 3t³ + t³
= 3t² − 2t³` step). mach_ring is simp/AC-based; this needs a true
monomial-normalising `ring` (Horner form), the long-flagged "ring v2". So:

  **Phase 3 critical path = mach_ring v2** (monomial normalisation), THEN the
  Bernstein-coefficient certificate generator (mechanical once ring v2 exists),
  THEN literal-bridge generalisation. ring v2 is the substantial piece; without
  it the SOS certificates cannot be discharged. Everything else is validated.

## What NOT to do
- Do not ship a `mach_linarith` that only `apply`s a fixed lemma list (the
  current v1 stub) and call it linarith — it closes none of the real backlog.
- Do not add per-kernel bound axioms for these (smoothstep_nonneg, …): that is
  the bespoke-axiom grind this doc exists to stop. ~2 obligations per axiom,
  unbounded surface, no reuse.
