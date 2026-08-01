# `@verify(lean)` close-rate — re-measurement, 2026-08-01

**Pre-registration written BEFORE the sweep ran. The number is appended below it, not above.**

## Why this was ordered, and why the stated reason turned out to be wrong

The re-measurement was ordered on the premise that the close-rate **inherited the `sorry`-detector
defect** fixed in `monogate-forge` 0.14.4 — where Lean's quoting change from `'sorry'` to
`` `sorry` `` made a literal match go permanently false, so `full_build_ok` reported True for proofs
containing `sorry`.

**That premise does not hold, and the error was mine.** I flagged the close-rate as "unquotable for
the same reason the by-actor ratio is — it was produced by the detector that was rubber-stamping."
**I never checked which instrument produced it.**

The close-rate comes from `foundations/scripts/closerate.sh`, a **machlib-side** harness that
compiles each `MachLib/Discovered/*.lean` independently and counts obligations with:

```bash
grep -cE "uses .sorry."
```

Those are wildcards, not straight quotes. Verified empirically against both real Lean outputs:

| matcher | `uses 'sorry'` | `` uses `sorry` `` |
|---|---|---|
| `closerate.sh`: `uses .sorry.` | ✅ | ✅ |
| forge's broken literal | ✅ | ❌ |

**The close-rate harness was version-tolerant by accident and never went blind.** It is a different
instrument from the one that broke, and it survived the quoting change the other did not.

> **This is the "a figure inherits the defect history of the instrument that produced it" rule
> applied correctly — and it EXONERATES the figure.** I applied it by association instead of by
> tracing the instrument, which is the same shortcut as attributing a failure to the nearest recent
> change. The rule is only worth having if it is run in both directions.

## The measurement is still worth taking

Not because the old number is tainted, but because it is **old**: a June snapshot with no instrument
version attached. A fresh number carrying its provenance is strictly better than an undated one,
and the sweep is cheap.

## PREDICTIONS, both recorded before the sweep

> **Orchestrator, stated when the re-measurement was ordered:** *"the honest rate comes in lower,
> and the delta is worth a line in the supply-chain writeup."*

**Recorded as made, and its premise is now falsified before scoring.** It was a reasonable inference
from a defect-corrected instrument. Since the instrument was never defective here, a defect-driven
drop has no mechanism behind it.

> **Mine, given the corrected premise:** the rate moves only by **corpus drift** — theorems added or
> changed since the June snapshot — not by defect correction. **Direction genuinely unknown**;
> per AMENDMENT 5 this is a straddle, and per AMENDMENT 6 the falsifiable content is the
> *mechanism*, not a bare existence claim.
>
> **Disconfirming observation, named:** a large drop (more than a few points) would mean something
> else is wrong that neither of us has identified, and would need chasing before the number is
> quoted.

---

# RESULT

```
=== Forge @verify(lean) close-rate (MachLib/Discovered) ===
files:     294  (290 compiled, 4 build-error)
theorems:  749  (717 in compiled files, 32 in error files)
CLOSED:    553
sorry:     164
close-rate (of compiled): 77.1%  (553/717)
```

| | |
|---|---|
| **figure** | **77.1% — 553 / 717 obligations closed** |
| **instrument** | `foundations/scripts/closerate.sh`, machlib `HEAD` 2026-08-01 |
| **toolchain** | Lean `v4.32.2` (the one that built the oleans — pinned, not the box default) |
| **corpus** | `MachLib/Discovered/`, 294 files, 749 theorems |
| **excluded** | 4 stale build-error files, 32 theorems — see residual below |

## The delta I was about to quote does not exist, because the numbers are not the same measurement

**The disconfirmer I pre-registered fired, and then un-fired on inspection.** Against the 93.6% I
had in mind, 77.1% is a 16.5-point collapse — "a large drop that would mean something else is
wrong." Before quoting it I checked what 93.6% measured. **It measures something else.**

| figure | what it actually is | source |
|---|---|---|
| **93.6%** (264/282) | `mach_linarith` **substantive** close rate, a different corpus | `docs/mach_linarith_plan_2026_06_24.md` |
| **76%** (126/165) | per-obligation close rate, and the documented **structural ceiling** | `docs/verify_closerate_scope.md` |
| **77.1%** (553/717) | this sweep, `MachLib/Discovered`, 2026-08-01 | here |

**Against the comparable figure — 76% — today's 77.1% is consistent and marginally above, on a
corpus 4.3× larger (717 obligations vs 165).** There is no collapse and there is no defect-driven
movement, which is what the corrected premise predicted.

> **This is the compare-on-the-semantic-key rule earning its place twice in one measurement.** The
> first near-miss was attributing the figure to the wrong instrument; the second was comparing it
> to the wrong baseline. Both would have produced a confident, precise, wrong story — the first that
> a defect had been flattering the corpus by 16 points, the second that something unknown had just
> broken. **Neither happened.**

## Predictions, scored

* **Orchestrator's — *"the honest rate comes in lower"*: NOT SCORED.** Its premise (a
  defect-corrected instrument) was falsified before the sweep ran. Scoring a prediction whose
  mechanism was removed would measure luck, not judgement — the same reason AMENDMENT 5 refuses to
  force a binary on a straddle.
* **Mine — *"moves only by corpus drift, direction unknown"*: CORRECT on mechanism**, which is the
  falsifiable content per AMENDMENT 6. The disconfirmer (large drop) appeared to fire and was
  resolved as a metric mismatch, not a measurement.

## Residual, named rather than dropped

**4 files fail to build at all — 32 theorems, 4.3% of the corpus**: `mul_mat4.lean`, `vec3.lean`,
`autopilot.lean`, `shadow_pcf.lean`. The harness labels them *stale* and excludes them from the
denominator.

**Excluding them is defensible and worth stating out loud, because it flatters the number.** A file
that does not compile has no closed obligations, so folding all 32 into the denominator gives
**553/749 = 73.8%**. Both are true; they answer different questions — *"of the obligations we can
assess, how many close"* versus *"of everything the corpus claims, how many close"*. **The second is
the one an outsider means**, so it is stated here alongside the first rather than left to be
discovered.

## Quotable form

> **`@verify(lean)` per-obligation close rate: 77.1% (553/717) of assessable obligations, or 73.8%
> (553/749) including 4 stale files that do not compile. Measured 2026-08-01 by
> `foundations/scripts/closerate.sh` at machlib HEAD under Lean v4.32.2.**

**Both denominators travel with the figure, and so does the instrument.** That is the
provenance-by-default tier of the rule: a number that names its instrument can be re-checked when
that instrument's record changes, which is exactly the check I failed to run before flagging this
figure as tainted.
