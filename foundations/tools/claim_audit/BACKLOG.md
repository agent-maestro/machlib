# Claim-audit backlog

Items found by use, not by design review. Each records a defect the current system could not have
caught, so that the cost of building the check can be weighed against a real specimen rather than a
hypothetical.

---

## 1. Cross-theorem premise agreement — the sharpness-witness relation

**Found:** 2026-08-19, while drafting §5 of the finite-depth-tameness manuscript.
**Specimen:** machlib `486b8a62`.

### The defect

`superlinear_subexp_not_depth_le_three` excludes functions satisfying **four** conditions.
`band_exclusion_fails_at_depth_four` was the sharpness witness for it, and certified `x + 1` against
only **three** — the conditions of the *depth-2* version of the same theorem.

Both theorems were individually valid and both passed every gate. The **composition** was invalid:
refuting a three-condition claim does not refute a four-condition one. The pair had been used to
assert sharpness for as long as both existed.

Two things followed, one visible and one not. The sharpness argument did not close; and because the
exclusion needs all four conditions to be *instantiated*, `x + 1` could not be fed to it at all, so
`d(x + 1)` stood recorded as open when it was one easy conjunct away from being settled. It is now
settled: `d(x + 1) = 4` exactly.

### Why no gate saw it

The registry checks properties of **one theorem at a time**:

```
    conclusion_mentions   statement_mentions   hypotheses_count   proof_uses   forbid_axioms
```

Every one of these is intra-theorem. `hypotheses_count` was pinned correctly on both sides —
correctly, and uselessly, because nothing asserted that the two counts had to *agree*, or that the
witness had to establish the exclusion's actual premise. The relation being violated was

> `Y` is the sharpness witness for `X`, therefore `Y` must establish `X`'s premise.

which is a statement about a **pair**, and the vocabulary has no pairs in it.

### Two ways to build it, and they cost very differently

**(a) A new relation kind — expensive, and correctly so.** Something like

```
    relation:            witnesses_failure_at_next_depth
    target:              superlinear_subexp_not_depth_le_three
    witness:             xPlusOneTree
    premise_certificate: x_plus_one_band_hyps
```

with the checker verifying that the witness-side proposition *is* the predicate the exclusion
consumes, or at least has a typed implication into it. Note this is not merely a new template: every
existing relation's obligations (`conclusion_mentions`, `hypotheses_count`, `proof_uses`) range over
a single theorem, so this needs a **new obligation kind**, not a new row. Per `README.md`, extending
the vocabulary is a ceremony requiring `--bless-relations`, and that ceremony exists for good
reasons. This should not be done casually.

**(b) Cheap version, available now, using only the existing vocabulary.** The repair for this defect
introduced `IntermediateBand` — the four conditions as one named proposition (`EMLDepthTameness`).
Once the premise is an *object* rather than an argument list, the pair check collapses into two
intra-theorem checks the registry can already express:

```
    exclusion  →  statement_mentions:  ["IntermediateBand"]
    witness    →  conclusion_mentions: ["IntermediateBand"]
```

If both hold, the witness concludes exactly what the exclusion consumes, and a three-quarters
certificate is a type error rather than a reading error. This is not as strong as (a) — it does not
verify the *pairing* is declared, only that both sides speak the same predicate — but it costs two
registry rows and no ceremony.

**Recommendation:** do (b) when next touching `claims.json`; hold (a) until a second specimen
appears that (b) would not have caught. One specimen does not justify a new obligation kind.

### The general lesson, which outlives this specimen

> Locally valid facts do not compose into a valid argument, and a gate suite that only checks facts
> locally will report green on an invalid composition.

The structural cause here was that a shared premise was **inlined** in one theorem, so the other
could neither reuse nor be compared against it. Any premise consumed by more than one result should
be an object. Where it is not, expect drift, and expect it to be invisible.
