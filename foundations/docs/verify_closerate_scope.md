# Scoping: closing the remaining `@verify` obligations — does it need a real nlinarith?

**Question.** After `mach_sign` + the ordering layer reached **70% per-obligation (116/165)** on the
Forge positivity/ordering corpus, the remaining ~30% (49 obligations) were described as "needing a real
nlinarith + a domain-lemma library." This document scopes that work — grounded in the *actual* 49
failures, not an imagined engine.

**TL;DR.** The "nlinarith" framing is mostly wrong. ~75% of the remaining failures are **more
structural arms** (transcendental-bound lemmas + a few ordering arms) — the same proven methodology as
this arc, derivable from existing axioms, **no new engine**. Only ~10–12 are genuine **domain `a−b`**
inequalities, and those need *bespoke domain-math lemmas* (Black-Scholes no-arbitrage, energy balance)
that **a general nlinarith would not supply anyway**. Recommendation: **do Phase 1 (arms); do NOT build
a general Mathlib-free nlinarith** — it's a multi-week engine for ~10 obligations that still need hand
math. Hand-prove the handful of domain cases worth proving instead.

---

## The data (the 49 failures, categorized by reasoning actually needed)

Method: per-obligation harness — swap each `sorry` for `(first | mach_sign | sorry)`, `#print axioms`
per theorem; no `sorryAx` = a real close. Baseline 116/165 closed, **49 fail**.

### Phase-1 tractable (more structural arms) — ~37 of 49

| Sub-class | Count (approx) | Example | What closes it |
|---|---|---|---|
| **log positivity / monotone** | ~7 | `shannon = B·LN2_INV·log(1+snr) ≥ 0` | `log_nonneg : 1 ≤ x → 0 ≤ log x` (derivable from `log`/`exp` axioms) |
| **exp-vs-one** | ~4 | `binomial up_factor = exp(vol·√dt) > 1` | `one_lt_exp : 0 < x → 1 < exp x` (from `exp_lt` + `exp_zero`) |
| **transcendental positivity** (exp/exp10/√) | ~9 | `eyring = KB·T·exp(…) > 0`, `stefan/wien/planck` | bound-transitivity (built) + `sqrt_pos` (have) + `exp_pos`/`exp10_pos` (have) |
| **tanh-affine** | ~3 | `sigmoid_alt = tanh(x·½)·½ + ½ ≥ 0` | normalize to `½·(1+tanh)` then `one_add_tanh_pos` (have) |
| **div with positive denominator** | ~6 | `doppler`, `bet`, `humidity`, `rc_time` | `div_pos`/`div_nonneg` (have) once the denom's sign is closed from hyps |
| **additive / interval ordering** | ~5 | `carbon: a+b+c ≥ a`, lorentz `≥ 1` | `le_add_of_nonneg_right` (have) + an additive `mach_le` arm; sqrt/√(1−β²) bounds |
| **bounded-coeff squares** | ~3 | `rmsprop/adam: (1−ρ)g² + ρ·prev ≥ 0` | `ρ ∈ [0,1]` from refinement + `sq_nonneg` + bound-trans |

These need **~6 new derivable lemmas** (`log_nonneg`, `log_monotone`, `one_lt_exp`, a couple sqrt
bounds) + **~4 new arms** (log, exp-vs-one, tanh-affine, additive-ordering). **No new axioms.** Same
shape of work as `abs_mul_self` / `one_add_tanh_pos` this arc. Estimated close: **~25–35 of 37**, taking
per-obligation close-rate to **~85–90%**.

### Genuine domain `a−b` (need bespoke math) — ~12 of 49

| Obligation | Why it's hard |
|---|---|
| `black_scholes_call/put ≥ 0`, `rho_put ≤ 0`, `put_delta ≥ −1` | `spot·σ₁ − strike·e^{−rT}·σ₂ ≥ 0` is the **no-arbitrage** inequality — a finance theorem, not structural |
| `energy_budget` equilibrium `T > 0` | `(1−α)·S·¼ − ε·σ·T⁴ > 0` at equilibrium — energy-balance domain fact |
| `euler_buckling` Johnson `≥ 0` | `σ_y − (σ_y·λ)²/(4π²E) ≥ 0` — needs the slenderness-range domain bound |
| `friis`, `cross_entropy`, `huber`, `compressor` | `a − b ≥ 0` where `b ≤ a` depends on a domain identity / a case split |

No general tactic closes these without the **domain fact itself** as a lemma. That is true *whether or
not* a nlinarith exists.

---

## What a real Mathlib-free nlinarith would actually require (and why ROI is low)

`nlinarith` = linarith + a preprocessing step that multiplies hypothesis pairs and adds square terms,
then runs a Positivstellensatz/Fourier–Motzkin search for a nonnegative combination that contradicts
the negated goal. A Mathlib-free version needs:

1. **A linarith core** over MachLib's ordered field (Fourier–Motzkin or simplex on linear `≤`/`<`
   atoms). MachLib has a `mach_linarith` *stub* only.
2. **Nonlinear preprocessing** — products of hypotheses, square completions — to feed the linear core.
   This is the genuinely hard, heuristic part.
3. **A certificate checker** — turn the found combination into a checked Lean proof term (no `sorry`).
4. **The domain-lemma library anyway** — even with 1–3, `black_scholes_call ≥ 0` needs the no-arb
   identity *supplied*; nlinarith finds combinations of *given* facts, it doesn't invent finance.

Effort: **weeks** (a real engine + certificate layer), high risk (the heuristic search is where
nlinarith's reputation for "works until it doesn't" comes from). Payoff: **~10 obligations**, several of
which *additionally* need bespoke domain lemmas. **ROI is poor.**

---

## Recommendation

1. **Phase 1 — build the arms (do this).** ~6 derivable lemmas + ~4 arms. Days, low risk, proven
   methodology, **closes ~25–35 obligations → ~85–90% per-obligation**. This is the continuation of the
   current arc, not a new project.
2. **Phase 2 — the ~12 domain `a−b`: do NOT build a general nlinarith.** Instead, **hand-prove the few
   worth proving** with targeted domain lemmas (e.g. a `bs_call_nonneg` lemma stating the no-arb fact),
   and **honestly mark the rest out-of-automated-scope** in the kernel docs. A general nlinarith is a
   multi-week engine whose unique contribution here (~10 obligations) is dominated by the bespoke
   domain math those obligations need regardless.

The honest end state: **structural automation tops out around ~90%**; the last ~10% is *domain
mathematics*, which is a per-kernel authoring task, not a tactic. Naming that boundary is itself a
result — it says exactly where machine structure ends and domain expertise begins.
