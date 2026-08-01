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

*(appended after the sweep; see below)*
