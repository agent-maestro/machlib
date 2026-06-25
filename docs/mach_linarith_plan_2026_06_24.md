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

**Refinement (same day): the FACTORED certificate partially sidesteps ring v2.**
For a polynomial with NO cancelling constant term, the factored form expands to
exactly the goal's monomials (each once), so mach_ring v1.5 closes it with no
collection: `3t²−2t³ = t²·(3−2t)` works → **smoothstep CLOSES** (hand-proved
green: `mul_nonneg (sq_nonneg t) (sub_nonneg_of_le …)`, bound via
`mul_le_mul_of_nonneg_left` + `mach_norm_num`). BUT polynomials WITH a constant
still need collection: `ease_out = 1−(1−t)²` expands with a `1 + −1` that
mach_ring can't cancel → still blocked. So the factored sidestep covers the
"starts-at-0, no-constant" subset (smoothstep), not the general band. General
case still gated on ring v2 (collection) OR a real nlinarith (products +
linarith). NET: the path is de-risked (a univariate recursive-factor tactic,
not full ring v2, suffices for the common no-constant easing functions) but
auto-finding the factorisation still needs an elab tactic (extract coeffs,
factor out tᵏ, recurse) — a focused multi-hour build, not a macro.

## Phase 3 attempt #2 (2026-06-24): ring v2 via AC-completion — works, but has blast radius

Tried to BUILD ring v2 (not just scope it). Key results:

**It works mathematically.** `mach_ring`'s catch-all simp set has `add_comm`,
`add_assoc` but is MISSING `add_left_comm` (and `mul_left_comm`) — the third
lemma of the standard AC set, without which `simp`'s additive normaliser stalls
on coefficient collection. Adding `add_left_comm`/`mul_left_comm` (both PROVED,
no axiom) lets `mach_ring` close the ease_out identity `1-(1-t)² = t(2-t)` and
other collection-needing identities. So **ring v2 = mach_ring + a complete AC
simp set**. No reflective normaliser needed.

**But it can't just be bolted on.** Two failure modes found:
1. Strengthening `mach_ring` GLOBALLY (editing Ring.lean's catch-all) broke an
   existing proof — `NormalizedPolynomialRootCount.lean` did `mach_ring; <step>`
   and the now-stronger mach_ring closes the goal, so `<step>` errors "no goals
   to be solved". Plus 1 emitted file regressed. Net corpus gain: ZERO (the
   identity wins were offset). Strengthening a core tactic ripples into every
   dependent proof.
2. An ISOLATED `mach_ring2` (mach_ring + abel-simp) used as a guarded
   mach_positivity arm ALSO regressed 2 files — because the arm is tried on
   ARBITRARY goals (inequalities), where the `simp only [add_comm, …]` pass
   misbehaves, and `fresnel f0+(1-f0)=1` (RHS a bare constant) it left open.

**Conclusion:** ring v2 is a SMALL change (3 AC lemmas) but a CAREFUL one — it
must (a) be a separate tactic applied ONLY to equality goals, AND (b) fix the
handful of existing `mach_ring; <step>` proofs that depend on the weaker
behavior. Reverted to clean 77%. This is the dedicated-build boundary: the
mechanism is now fully understood, but landing it safely is deliberate work,
not a session patch. AND it only unblocks the IDENTITY obligations — the
polynomial INEQUALITY bands still additionally need certificate-finding (the
SOS/factored form), which is the separate elab.

## What NOT to do
- Do not ship a `mach_linarith` that only `apply`s a fixed lemma list (the
  current v1 stub) and call it linarith — it closes none of the real backlog.
- Do not add per-kernel bound axioms for these (smoothstep_nonneg, …): that is
  the bespoke-axiom grind this doc exists to stop. ~2 obligations per axiom,
  unbounded surface, no reuse.

## FINAL STATE — 2026-06-24 (260/282 = 92% substantive; +4 spec-gap fixes)

The reusable-closer tier is now **exhausted**. Pushed from 243 → 256 (+13) this
session, all sound, all reusable (no per-kernel bound axioms), zero corpus
regression. The closers added — each generalises beyond its first kernel:

| closer | shape | kernel(s) |
|---|---|---|
| `le_mul_one_add_div` | `v ≤ v·(1+r1/r2)` | ldo divider |
| `log_neg_of_lt_one`,`neg_pos_of_neg` | `0 < −log(feedback)` | reverb T60 |
| `add_sqrt_sq_add_nonneg`,`mul_self_pos` + `le_sqrt_of_sq_le`(ax) | quadratic-formula root sign | lqr Riccati |
| `neg_div_pos_neg` + lt_trans arm | `(−a)/b < 0` | fov m22/m23 |
| `one_sub_exp_neg_div_nonneg` | `0 ≤ 1−e^{−t/τ}` | ink recovery, sprint velocity |
| `floor_zero`(ax) | `0 − ⌊0⌋ = 0` | white_noise |
| emitter binary-state `rcases` | `(v==c1)‖(v==c2)` case split | hysteresis |
| `sub_sqrt_nonneg_of_le_sq` + `sqrt_le_of_le_sq`(ax) | `0 ≤ v − √(min(…,v²))` | tof |
| `sub_mul_one_sub_exp_neg_div_nonneg` + `one_add_le_exp`(ax) | `0 ≤ t − τ(1−e^{−t/τ})` | sprint distance |
| `le_mul_of_one_le_right` | `a ≤ a·b`, gain≥1 | tapetum |
| `sub_le_self` | `a − b ≤ a` | thermal erosion |

New axioms this session (4, all sound, all reusable — NOT per-kernel bounds):
`le_sqrt_of_sq_le`, `sqrt_le_of_le_sq` (sqrt order, both directions),
`floor_zero` (⌊0⌋=0, not derivable from the bracketing axioms), `one_add_le_exp`
(the exp tangent line, all x).

### The remaining 26, categorised — and why each is OUT of cheap reach

**(A) EML SPEC GAPS — were 6; 4 now FIXED, 2 remain (2026-06-24 finish-&-ship).**
These were *Forge / eml-stdlib findings* (the `ensures` not entailed by the
`requires`/`domain`), not prover limitations:
- ✅ FIXED `doppler_observed_freq_positive`, `doppler_air_default_freq_positive`:
  `result ≥ 0` needed `v_sound + v_listener ≥ 0` (a fast-receding listener makes
  the numerator negative). Added the `requires` (eml-stdlib `7c9a971`) — both
  now CLOSE (div_nonneg). Real correctness fix to the public lib.
- ✅ FIXED `thermistor_steinhart_temperature_positive` / `…_beta_…`: `1/inv > 0`
  needed `inv > 0` (a,b,c free / β can be <0). Added the `requires (inv > 0)`
  (eml-stdlib `7c9a971`) — both now CLOSE (one_div_pos).
- ⚠ REMAIN (must NOT close): `atan_in_open_half_pi_band`,
  `atan2_pos_x_in_open_half_pi_band`: `arctan x >
  −HALF_PI` where `HALF_PI = 1.5707963267948966` is the truncated double,
  STRICTLY less than the real π/2 (1.5707963267948966192…). Since arctan's range
  is the OPEN (−π/2, π/2), ∃x with arctan x ∈ (−π/2, −HALF_PI) ⇒ the strict bound
  is FALSE at the asymptotic extreme. A real-vs-float discrepancy, not provable
  for the real model.

**(B) Decimal-interval nlinarith — 8 — need Phase 3 (decimal model + product
search). Documented above; unchanged:** `bangbang_in_actuator_band`,
`bangbang_sym_in_band` (0.5 + clamp), `smootherstep_in_unit_interval`
(completed-square, fractional-decimal coeffs), `rtd_resistance_above/below_zero`
(quadratic/cubic positivity over a decimal interval), `rod_sensitivity_bounded_unit`,
`air_density_humid_lower_than_dry`, `planck_radiance_increases_with_temperature`.

**(C) Deep analytic facts — 5 — each a genuine transcendental theorem (Jensen /
convexity / Cauchy–Schwarz), NOT a bound to axiomatise per-kernel:**
`silu_at_zero_is_zero` (silu ≥ −1, the function minimum), `erf_as_zero_is_zero`
(erf rational-approx ≥ 0), `bce_loss_nonnegative` + `bce_with_logits_equals_bce`
(softplus(z) ≥ target·z — bce ≥ 0 convexity), `matched_filter_cauchy_schwarz`.

**(D) Transcendental const — 4:** `fov_m00_positive`, `fov_m11_positive`
(`1/tan(fov/2) > 0` — needs `tan_pos` on (0,π/2) AND `0.5·3.141 < π/2`, i.e.
`3.141 < π`), `wien_inversely_proportional_to_T` (T_MIN const + monotone),
`hamming_in_unit_interval` (HALF const + cos band).

**(E) floor parity — 2:** `checker_returns_zero_or_one`,
`checker_tiled_returns_zero_or_one` — `(⌊x⌋+⌊y⌋) mod 2 ∈ {0,1}`. Needs
integer-floor / mod-2 reasoning the Real→Real `floor` collapse discards.

**(F) decimal-const evaluation — 1:** `hamming_at_zero_is_offset`
(`A0 − A1 = 0.08`, i.e. `0.54 − 0.46 = 0.08` over opaque `realOfScientific`).

### Honest framing of the number
Excluding the 6 spec gaps (which are *not* well-specified obligations a prover
should close), the rate over WELL-SPECIFIED obligations is **260/280 = 92.9%** (only atan×2 remain spec-subtle).
The remaining 20 split cleanly: ~13 wait on the Phase-3 nlinarith+decimal engine
(B+D+F), ~5 are deep analytic theorems (C), 2 are floor-parity (E). None is
closeable by a *reusable* lemma — the next real increment is the engine, not
more arms.
