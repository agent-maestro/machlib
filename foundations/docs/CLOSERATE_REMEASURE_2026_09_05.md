# The 164 residual `@verify` obligations, classified — and what actually blocks them

**Measured 2026-09-05** by a per-obligation sweep of `MachLib/Discovered/` under Lean v4.32.2
(`lake env lean` per file, one line per `declaration uses \`sorry\`` warning; 290 of 292 files
compile, 2 do not, matching `scripts/closerate.sh`'s 553/717 = 77.1 % of 2026-08-01, re-run the same
day with the identical figure).

## The data

164 residual obligations in 102 files. By the relation in the goal: 142 are `≤`/`≥`, 11 are `<`/`>`,
11 are `=`. By what the goal *means* once the kernel's `def` is unfolded:

| kind | n | typical example |
|---|---|---|
| non-negativity / positivity of a kernel value | 83 | `auc_inf coef_a rate_alpha coef_b rate_beta ≥ 0` |
| a band `lo ≤ f ∧ f ≤ hi` or an `abs` bound | 40 | `demosaic_green_at_red … ≥ PIX_MIN ∧ … ≤ PIX_MAX` |
| a comparison between two kernel values under hypotheses | 14 | `hill_monotone_in_substrate` |
| an algebraic identity | 11 | `translate_then_transform_x_witness tx x = ZERO` |
| other inequality | 16 | `fov_m00_positive` |

By the operators present **after unfolding the definitions** (a goal can carry several):

| feature | n of 164 |
|---|---|
| a decimal literal (`0.25`, `1e-06`, `65535.0`, …) | 133 |
| subtraction | 106 |
| division | 83 |
| `abs` | 33 |
| `exp` | 29 |
| `sin`/`cos`/`tan`/`atan` | 24 |
| `sqrt` | 19 |
| `min` / `max` | 19 each |
| a power | 17 |
| `tanh` | 8 |
| `log` | 6 |

The first row is the finding. The residue is not "needs nlinarith" and not mostly transcendental; it
is dominated by **decimal constants that reach the closers folded behind a name** and by **division by
a quantity whose positivity is a folded decimal lower bound**.

## Four obligations, read to the bottom

1. `pk_two_compartment.lean : auc_inf_finite_for_positive_rates` — `coef_a / rate_alpha + coef_b /
   rate_beta ≥ 0` with `0 ≤ coef_a` and `RATE_MIN ≤ rate_alpha`, where `RATE_MIN : Real := 1e-06` is
   a module constant. The emitted proof unfolds `auc_inf` and nothing else, so `mach_positivity`
   sees `RATE_MIN ≤ rate_alpha` and cannot conclude `0 < rate_alpha`. With the constants unfolded at
   every location, `ofScientific_pos` gives `0 < 1e-06`, transitivity gives `0 < rate_alpha`, and
   `div_nonneg_of_nonneg_pos` twice plus `add_nonneg` close it. **Verified by hand in a scratch
   file; `#print axioms` clean.**
2. `mat4.lean : mat4_translate_then_transform_shifts_x` — `((ONE·x + ZERO·ZERO) + ZERO·ZERO + tx)
   − (x + tx) = ZERO`. An identity. The cascade has no ring arm; `rfl` fails because `ONE`, `ZERO`
   are `def`s. `unfold … ; mach_ring` closes it, **verified, clean footprint**. Eleven obligations
   have this shape.
3. `aqi_epa.lean : aqi_within_band_bounds` — a linear interpolation `lo + (hi−lo)/(Δ+TINY)·(c−c_lo)`
   stays in `[lo, hi]`. Needs one lemma the corpus does not have: `(c − c_lo)/(Δ + TINY) ≤ 1` from
   `c − c_lo ≤ Δ < Δ + TINY`, then the convex-combination arms. A structural arm, not analysis.
4. `bayer_demosaic.lean : demosaic_g_at_r_in_pixel_range` — `0.25·(a+b+c+d) ≤ 65535` from four
   inputs each `≤ 65535`. Needs decimal arithmetic: `0.25 · 4 = 1`. `realOfScientific_clears` and
   `NatCastArith` supply the mechanism; nothing in the cascade tries it.

## What changed, and where

The two cheapest classes are blockers in the **emitter**, not in MachLib. Forge's
`LeanBackend` now (a) unfolds every module constant at every location before
the closers run — `try unfold C at *`, one line per constant, so an absent constant does not cancel
the others — and (b) adds a `(mach_ring; done)` arm before `rfl`. The `done` is load-bearing:
`mach_ring` is all-`try` and leaves an out-of-fragment goal open rather than failing, and an open
goal at the end of a `by` block becomes a synthetic `sorry` in a file that still compiles.

The corpus was regenerated from the current emitter (`tools/scripts/regen_discovered.py`; 192 of
the 249 top-level files have a `.eml` source under `forge/industries/`, 56 do not and are left as
they were, one is ambiguous and skipped).

## Result

Re-measured with `scripts/closerate.sh` at machlib HEAD under Lean v4.32.2, after the two emitter
changes and one MachLib change (`mach_sign` now splits conjunction hypotheses — Forge emits a
refinement type `x : Real[lo, hi]` as ONE hypothesis `lo ≤ x ∧ x ≤ hi`, and `assumption` does not
look inside a conjunction, so the bound-transitivity arms never fired on them):

```
files:     292  (290 compiled, 2 build-error)
theorems:  720  (717 in compiled files, 3 in error files)
CLOSED:    573
sorry:     144
close-rate (of compiled): 79.9%  (573/717)
```

The last obligation of those came from a third emitter change, made after this document's first
draft and measured on its own: `try mach_split_hyps` is now emitted **before the whole cascade**,
not only inside `mach_sign`. Every `convex_comb*` arm and `lo_le_clamp`'s discharge their side
goals with a bare `assumption`, which cannot see inside the conjunction a refinement type
`x : Real[lo, hi]` is emitted as — so a convex blend in a band failed for a reason that had
nothing to do with convexity. **It closed one obligation.** The shape-count had suggested six;
the other five turned out to differ in ways the arm does not match. Recorded because the
prediction was wrong and the measurement is the record.

| | 2026-08-01 | 2026-09-05 (before) | 2026-09-05 (after) |
|---|---|---|---|
| closed | 553 | 553 | **572** |
| residual `sorry` | 164 | 164 | **145** |
| close rate of compiled | 77.1 % | 77.1 % | **79.8 %** |
| build-error files | 4 | 4 | 2 (see below) |

**What was learned on the way, because it cost a run each.** (1) An unconditional
`(mach_ring; done)` arm broke four previously-compiling files (`black_scholes`, `sabr`, `diffuse`,
`additive_voice`): on a large inequality `mach_ring`'s AC-simp hits the heartbeat limit, and a
timeout is an *error*, which `first` cannot backtrack out of — the trap CLAUDE.md already records
for nested `by` blocks, met in a new costume. The arm is now emitted only for `==` obligations.
(2) Unfolding the constants alone closed **nothing**: the literal was visible but sat inside a
conjunction. The gain came from the splitter. (3) The obvious splitter,
`repeat (rcases ‹_ ∧ _› with ⟨_, _⟩)`, diverges — the anonymous-hypothesis term unifies against
every hypothesis, and against a `Real` inequality with a decimal literal that is a `whnf` timeout.
It is an elaborator that walks the context by type instead (`mach_split_hyps`, `SignTactic`).
(4) `mat4.lean` and `quaternion.lean`, which hold the 11 identity obligations the ring arm was
written for, have no `.eml` source any more and were not regenerated; the arm is in place for the
next kernel with that shape, and those two files keep their sorries.

## What is left, priced

- **Decimal-literal arithmetic** (`0.25 · 4 = 1`, `0.2 ≤ 0.8`): a `mach_decimal` normaliser over
  `realOfScientific` via `NatCastArith` — the memory notes' "decimal-coeff bands". One tactic,
  reused by the band class; the largest remaining lever.
- **Interpolation-in-band** (`aqi_in_band`, `lerp`, `hard_knee`): one lemma family
  `lerp_in_band` plus a `div_le_one_of_le_of_pos` arm.
- **Sign of a division with a folded positive denominator** is now reachable once constants are
  unfolded, but only where `mach_positivity`'s hypothesis-weakening arm sees a literal; a small arm
  `pos_of_decimal_lower_bound` (`lit ≤ x → 0 < x` via `ofScientific_pos`) would cover the rest.
- **Transcendental bounds** (`tanh` in `(−1, 1)`, `sin`/`cos` bands, `exp` positivity products):
  the 2026-06-30 scoping note's Phase 1 arms still apply; ~30 obligations.
- **Domain `a − b` inequalities** (Black–Scholes, energy balance): hand mathematics, ~10; a general
  engine would not supply them either.

`mul_mat4.lean` and `vec3.lean`, two of the four "stale" files every sweep since August reported,
turned out to be **phantoms**: ignored, untracked leftovers that existed only on one machine and
were never in the repository. CI's copy of the corpus never had them, which is why the
`check_discovered_compiles` allowlist that named them failed in CI as stale on 2026-09-05. Deleted
locally and dropped from the allowlist; the corpus is 292 files and the two files that genuinely
do not compile, `shadow_pcf.lean` and `autopilot.lean`, both have `.eml` sources and are the
emitter's to fix. The figures above are the re-run on the true corpus; the close rate over
compiled files is unchanged by the deletion.
