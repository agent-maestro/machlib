# MachSig Doctrine

> **MachSig tells you whether a formal result changed in what it claims, how it is proved, or what
> it trusts.**

That sentence replaces "structural fingerprinting" everywhere. It is what the system does, and it
is falsifiable in a way the old phrasing was not.

---

## 1. Three layers, because they answer three questions

| layer | question |
|---|---|
| `StatementSig` | **what does it claim?** |
| `ProofSig` | **how is it proved?** — did the proof *representation* change |
| `TrustSig` | **what does it rely upon?** — did the *dependency closure* change |

Trust was nested under proof until `v0.2`, and that was wrong. Two proofs can be syntactically
unalike while resting on an identical trusted base; more importantly, a statement and most of its
proof can look unchanged while **a new axiom quietly enters the closure**. Nesting hides exactly the
case worth catching.

Representation views (`EMLTree`, `Certcom EML`, …) are optional annotation, never a fourth pillar —
Phase 1b measured them as near-degenerate on this corpus.

## 2. `CanonicalSig: UNAVAILABLE` is a result, not a gap

There is no canonicalizer in MachLib with an extractable input for the dominant representation
(`CANONICALIZER_BRIDGE.md`). MachSig therefore reports the canonical layer as unavailable on every
object and refuses to fill it with the source form.

This is **evidence that the schema will not fabricate an answer to look complete**, and it is what
makes the other two layers worth believing. A system that invents a canonical form when it lacks one
would invent other things too.

The corollary is enforced in `diff.py`: the roadmap's "source SAME, canonical CHANGED" state is
**unreachable here and is not carried as a dormant branch**. A category that can never fire reads as
"checked and clean".

## 3. The testing hierarchy

```
        unit test   <   known-answer test   <   fault-injection test
```

* **Unit test** — the code did what the test expected. Says nothing about whether the analysis is
  measuring the intended thing.
* **Known-answer test** — the analysis distinguishes two objects whose relationship you already
  understand. Catches *plausible wrong analysis*, which no unit test will.
* **Fault-injection test** — the gate actually turns red when the forbidden condition is
  deliberately introduced. The only evidence a gate convicts.

For instrumentation the last two matter most, because **plausible-looking wrong analysis is more
dangerous than a crash**. A crash announces itself.

### The case that established this

`ConstantInfo.value?` returns `none` for theorems in Lean v4.32.2. Every proof-layer feature was
computed over *absence*: `proof_len = 0` and one shared fingerprint — the hash of the empty string —
across all 7,569 theorems.

The program ran. Nothing crashed. The numbers looked reasonable. The output was **byte-for-byte
reproducible**. Determinism confirmed only that it was consistently analysing nothing.

It was caught by one known-answer pair: `decayFloorUpTo_three` and `..._via_step` have the same
statement and different proofs *by construction*, and the tool reported their proofs identical. The
same bug was sitting in the Phase 1 census, where `value_direct_const_count` was null for every
theorem, and no gate would ever have found it.

## 4. No green gate without a demonstrated red path

**Every gate making an assurance claim must ship a way to make it fail on demand, and that way must
exercise the gate against its real subject.**

A `--selftest` that checks a predicate in isolation is a unit test wearing a gate's clothing. It
demonstrates that a comparison operator works, not that the gate convicts.

`tools/machsig/trust_gate.py --selftest` is the intended shape: it perturbs a copy of the **live**
baseline, runs the gate's **actual** comparison over the **real** signature set, and requires a red
result — plus two controls (a shrinking footprint and a changed statement must both stay silent).

Writing it that way immediately paid: it caught that `AX` had moved from `ProofSig` to `TrustSig` in
`v0.2` and the gate was reading an empty field. The gate failed closed (`UNAVAILABLE`, exit 2) rather
than passing, but only the injection revealed *why*.

**Audit note.** All 14 gates in `check_all.sh` carry some self-test. They are **not** all at the same
tier: several (`check_forge_certificates.sh`, `check_obligations.sh`'s 18 canaries,
`check_aggregator.sh`) inject real faults, while others — including
`tools/soundness_witness_audit.py`, written earlier in this same effort — only exercise predicates.
Upgrading those is outstanding work, recorded here rather than glossed.

## 5. What made this project work

Every phase ended in a measurement that contradicted the plan:

* no general canonical form exists
* component counts are propositions carrying a bound, not computed numbers
* redundancy is representation-scoped, not global
* the corpus reasons about *quantified* trees, so term structure is degenerate
* the 220/243 axiom question was a namespace boundary, not a disagreement

Each time the story got ahead of the evidence, the corpus corrected it. **That is the property to
preserve.** The temptation at every step was to add features until something looked useful; the
discipline was to measure first and report negative results as results.
