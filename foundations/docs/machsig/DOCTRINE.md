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

### 4a. Firing is not enough — the conviction must name the defect

A specimen that only asserts *the gate went red* accepts a gate that convicts **everything**. That
failure mode is not hypothetical in this repo: the register gate's staleness check convicted all
seven dated rows at once under a shallow clone, and a did-it-fire test would have called that a pass.

So each injection asserts three things: the gate fires, **exactly one** check fires, and the message
**names the constant that was perturbed**. Naming is what separates a working gate from an
indiscriminate one.

### 4b. Mutation testing — the tier above injection

Fault injection validates the gate. It does not validate the *selftest*. To close that, break the
gate deliberately and require the selftest to notice:

| mutant | caught by |
|---|---|
| toolchain comparison removed | skew specimen |
| unaccounted check removed | unwitnessed specimen |
| stale-excuse check removed | stale specimen |
| ledger parse fails **open** instead of closed | parse specimen |
| conviction stops naming the axiom | **naming specimen only** |

Reproduce with `python3 tools/soundness_witness_audit.py --mutate`, run from
`machlib/foundations`. The table above is generated by that command rather than transcribed — a
cited result nobody can re-run is a literal, not evidence.

The last row is the payoff. That mutant leaves every did-it-fire assertion green — only the
discrimination specimen sees it. Without rule 4a the selftest would have had a blind spot exactly
where gates fail most quietly.

A second, subtler harness bug sat underneath: every mutant anchor necessarily also appears in the
`MUTANTS` table itself, so a whole-file `replace(a, b, 1)` was correct only by the accident that
`analyze()` sits earlier in the file. Reorder the file and all five mutants would patch the dict
literal, leave the gate intact, and report MISSED together. Mutation is now confined to the source
*above* the table, which also lets a drifted anchor report `STALE` — "the test is broken" — instead
of `MISSED`, which means "the gate is broken". Those are different findings and must not share a label.

The same distinction governs a red subject: if the live ledger is already failing, `--selftest`
reports SKIPPED rather than convicting its own control, because an injection going red against an
already-red subject demonstrates nothing. The gate still fails on the real conviction.

*The first mutation run reported 5 of 5 MISSED.* The tell was that **all five failed at once**: the
mutant copy was written outside the tree, so `HERE` resolved elsewhere, the witness project was not
found, and every mutant exited `UNAVAILABLE` before reaching a single check. Same shape as the
shallow-clone bug, caught the same way — when everything fails together, suspect the harness, not
the subject.

### 4c. A wired-in check must be proven wired

Until this change, **no gate's `--selftest` was invoked by CI at all**. `check_all.sh --selftest`
tests the *runner's* ability to conduct a failure to its own exit code; it never runs the individual
gates' self-tests. Every selftest in this repo was therefore developer-only ceremony — present,
passing when someone remembered, and unable to catch a regression on its own.

`soundness` now runs with `--selftest` (line 86). That is safe because its injections operate on
in-memory copies and write nothing; `--mutate` is deliberately **not** wired in, since it writes a
temp file into `tools/` and would mutate the worktree mid-run, voiding the run's own tree fingerprint.

The wiring itself was then verified the same way as everything else — by a specimen that can only
fire if the wiring is live. A mutant disabled the toolchain comparison, which breaks the *selftest*
while leaving the gate's real verdict OK (the toolchains do agree). The suite returned `GATE_RC=1`
on `soundness`. Had the wiring been decorative, the suite would have stayed green and the added
`--selftest` would itself have been a silently disabled check — the exact defect this gate exists to
prevent, reintroduced by the act of hardening it. The tree was then restored from backup and
`sha256sum -c` confirmed it byte-identical to the state the green run certified.

**Audit note (updated 2026-09-04).** The suite is now **15 gates** and CI runs **7 selftests**, up
from 2. `soundness`, `machsig-trust`, `hypothesis` and `absence` run their selftest *and* their gate;
`aggregator-selftest` is a gate in its own right, because `--selftest` there **replaces** the
aggregator rather than adding to it — putting the flag on the gate's line would have swapped a real
check for a self-check and still printed green.

Three remain unwired **with reasons, not silence**: `forge-cert` replaces its gate *and* writes a
canary into the tree (mutating the worktree mid-run); `claims` does not finish its selftest in 240s;
`discovered`, `consistency` and `witness` have no selftest at all.

Wiring found a defect immediately: **`absence_audit`'s control canary had been failing silently** —
`check` was tightened to demand a `positive_control` and the canary was never updated, so the control
returned UNAVAILABLE while the gate passed green daily. A gate whose control fires discriminates
nothing. Nothing surfaced it because CI never ran the selftest.

**Keep the scoreboard honest:** wiring a selftest makes CI *run* it, not makes it *good*. Only
`soundness` and `absence` have a **demonstrated** red path end-to-end; the other five are verified to
run and pass, which is weaker.

They are **not** all at the same tier. At injection tier: `check_forge_certificates.sh`, `check_obligations.sh`'s 18 canaries,
`check_aggregator.sh`, `tools/machsig/trust_gate.py`, and now `tools/soundness_witness_audit.py`
(7 specimens, 4 perturbations of the live files, mutation-tested above — upgraded from the
predicate-only version written earlier in this same effort, whose weakness this document named
before it was fixed). The remainder still only exercise predicates. That is outstanding work,
recorded here rather than glossed.

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
