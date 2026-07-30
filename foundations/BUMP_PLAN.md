# Toolchain bump — destination, route, and the pass bar, fixed before the first step

**2026-07-29.** Written before any migration work, because the pass bar for a migration is a
pre-registered acceptance criterion like any other, and "it still builds" is not one.

## The three constraints do NOT intersect

| constraint | satisfied by |
|---|---|
| contains the #14577 kernel fix | **≥ v4.32.2** (confirmed in its release notes: *"This point release fixes a soundness bug in the kernel… nested inductive types with phantom type parameters was incomplete and bypassed the type checker"*) |
| a `lean4checker` tag exists (acceptance gate's far end, and the second opinion we already have) | **≤ v4.28.0** — enumerated: v4.9.0 … v4.28.0, that is the maximum |
| Lean4Lean pins it (genuine independence) | v4.16.0, v4.19.0, v4.20.1, v4.23.0, v4.26.0, **v4.29.0** |

```
fix ∩ lean4checker   = ∅      (32.2 > 28.0)
fix ∩ Lean4Lean      = ∅      (32.2 > 29.0)
lean4checker ∩ L4L   = {v4.16.0, v4.19.0, v4.20.1, v4.23.0, v4.26.0}   ->  newest v4.26.0
```

**And no `v4.14.x` patch release exists** — `v4.14.0` is the only tag on that line, so there is **no
backport**. The soundness exposure cannot be retired for pocket change; it requires the full bump.
The two motivations do *not* separate into two timelines after all.

## Destination: v4.26.0 first, then track to the fix

**v4.26.0 is the recommended first destination** — the newest version where **both** checkers exist.

The tradeoff is real and belongs stated, not buried: **v4.26.0's kernel still contains the #14576
bug.** What v4.26.0 buys instead is **genuine kernel independence** — Lean4Lean is a from-scratch
re-implementation, so a check-omission in the C++ kernel's phantom-parameter handling is an
*implementation artifact* it has no reason to share. If MachLib replays clean through **both**, that
is direct evidence the exploit class is **not present in our code**, whatever either kernel would
accept in principle.

> **Independence covers the class. The patch covers the instance.** Given they cannot be had together
> today, the class is worth more — but sitting deliberately on a known-unpatched kernel is a decision,
> not a default, and it is recorded here as one.

**Then track to v4.32+** when lean4checker and Lean4Lean reach it. That is a watch item, not work.

## Route: step the checkable intermediates, never jump

`v4.16.0 → v4.19.0 → v4.20.1 → v4.23.0 → v4.26.0` — every one has a lean4checker tag *and* appears in
Lean4Lean's own history, which is decent evidence they are stable points.

Replay at each. Two reasons, and the second matters more:

1. Custom-elaborator breakage arrives **attributed to a two-or-three-version window** instead of an
   eighteen-version haystack.
2. **Every clean intermediate is a fallback position.** A stalled stepwise bump leaves the repo at
   v4.23.0 with everything green; a stalled *jump* leaves it at v4.14.0 with a broken branch.

## THE PASS BAR — fixed now, before the first step

**Not artifact identity.** `.olean` format changes across versions, so hashes are meaningless here and
comparing them would fail for reasons that say nothing about correctness.

| # | criterion | why |
|---|---|---|
| 1 | `lean4checker` replay **exits 0 at both ends** | the acceptance gate, and it exists at every intermediate |
| 2 | **`#print axioms` footprint EQUALITY** for all **57** headline theorems the ledger pins | the strong one. Same theorems, same dependencies, different kernel. A footprint that *changes* means the migration altered what something rests on — which is the only thing a bump must never do |
| 3 | `check_ledger.py` PASS, count still **252** | the trust boundary did not move |
| 4 | `check_derivable.py` PASS, still **5**, retained-base clean | the derivations survive |
| 5 | **0 sorries, 0 `sorryAx`** across the library | table stakes |
| 6 | `check_artifact_drift.py` PASS after each step | stepping *will* orphan oleans as modules move; class 8 catches it |

**Criterion 2 is the one that makes this a verified migration rather than a hopeful one.** It is
mechanical: dump the 57 footprints before, dump them after, diff the sets.

## Scope guard

The deliverable is **the same theorems, checked by a newer kernel, replay-clean at both ends.** Not
modernised proofs, not eighteen versions of new tactics, not relaxing the austerity constraints.

**MachLib's Mathlib-free discipline is the asset here:** a base that axiomatises `Real` and forbids
`by_contra` exposes far less surface to elaborator drift than any Mathlib-dependent project. The cost
is concentrated in the custom machinery — `mach_ring`/`mach_mpoly` elaborators, `Nat` pattern-match
compilation, structure-instance syntax — and **anything else moving means the diff is doing something
criterion 2 cannot see.**

---

*Everything above was written before any migration work and is left unamended. Everything below was
appended the same day, after the destination was challenged and reaffirmed: the decision record the
choice needs in order to survive a cold reading, its expiry condition, the second leg's pass bar, and
what a failed step is allowed to do.*

---

# DECISION RECORD — why the destination is a kernel with a known soundness bug in it

**2026-07-29.** The v4.26.0 destination was challenged and **reaffirmed**. Recorded in full here
because someone reading the trust registry cold will ask the obvious question — *why did MachLib
deliberately migrate to a kernel containing #14576 when v4.32.2 exists?* — and the answer must be
available without reconstructing the reasoning from an intersection table.

## The choice was between two configurations, not between fixed and broken

| | patched, single kernel | unpatched, dual kernel |
|---|---|---|
| destination | v4.32.2 | **v4.26.0** ← chosen |
| #14576, the *instance* | **fixed** | still present |
| implementations that must **both** accept a false proof | **1** — lean4's C++ kernel | **2** — the C++ kernel *and* Lean4Lean |
| so a false proof must be… | a defect in **one codebase**, whose track record now includes #14576 and the earlier projection bug this month's news cycle was about | a defect in **the type theory as understood by two independent authors** |
| `lean4checker` at the destination | **absent** (max stable tag v4.28.0) | present, and at every intermediate |
| Lean4Lean at the destination | **absent** (max pin v4.29.0) | present — it pins v4.26.0 itself |

Read the middle rows as *what an exploit would have to be*, and the comparison stops being close. A
single kernel — even a freshly patched one — asks trust of one implementation. Two independent
implementations ask a false proof to be a defect they **share**, and Lean4Lean shares no code with
the C++ kernel: it re-derives the typing rules from the theory rather than inheriting them from an
implementation. **That is a categorically smaller surface, not a smaller quantity of the same risk.**

## And for *this* bug, independence probably covers the instance as well

#14576 is a **check omission on the phantom-parameter path**: when eliminating a nested occurrence
`I Ds is`, the parametric arguments `Ds` were dropped from the generated auxiliary types, so they
escaped type checking (#14577, *"missing check at kernel inductive declaration"*). That shape matters
for the decision — it is an **implementation artifact**, a missing call on one code path, not a
misreading of the theory. **A from-scratch re-derivation has no reason to omit the same check.**

So dual replay at v4.26.0 is *likely to detect the very instance it does not patch*, on our 68
inductives — which is the question we actually need answered:

> Not **"is this kernel sound?"** — unanswerable by anyone. But **"does MachLib contain the exploit
> class?"** — and that is answered by two independent checkers agreeing on *our* environment, never by
> a version number.

**Independence covers the class; the patch covers the instance. They cannot be had together today, so
take the class — and note that it very likely reaches the instance too.**

## EXPIRY CONDITION — this decision is calendar-contingent and says so

The entire argument rests on one empirical fact: **`fix ∩ lean4checker ∩ Lean4Lean = ∅` on
2026-07-29.** That is a fact about July 2026, not a fact about software. Both blocking projects are
alive: lean4checker tags mechanically, per release (stable v4.9.0 … v4.28.0, and its release-candidate
tags already reach **v4.29.0-rc8**); Lean4Lean's pin moved five times in the last year.

> **This configuration is preferred UNTIL `fix ∩ lean4checker ∩ Lean4Lean ≠ ∅`.**
> On the day that intersection opens, the two configurations above stop being alternatives, the
> tradeoff dissolves, and the destination becomes the newest member of the intersection.

A decision recorded as permanent when it is really calendar-contingent is a small version of the
stale-comment bug, and it rots in the **reassuring** direction: the record goes on reading
*"considered, with the tradeoff owned"* long after the consideration expired. So the expiry is
**monitored, not remembered**:

```
python3 tools/migration/watch_kernel_support.py      # exit 3 = the intersection has OPENED
```

Re-run **quarterly — next 2026-10-29** — and whenever the toolchain conversation reopens for any
reason. It reads lean4checker's tags and Lean4Lean's pin from the network and **fails loudly when it
cannot reach them**: an offline run must never be readable as *"still empty"*, which is the reassuring
direction a third time.

That is what turns *sitting on a known-unpatched kernel* from a standing posture into a **monitored
wait**, and it is the difference between the two that this record is defending.

---

# LEG 2, PRE-REGISTERED NOW: v4.26.0 → the fix, the leg that loses the far-end checker

Written while leg 1's pass bar is fresh, because leg 2's hard part is a *missing instrument*, and that
is exactly the thing a migration discovers at the end if nobody wrote it down at the start.

**At v4.32.2, criterion 1 has no far end.** lean4checker stops at v4.28.0 and Lean4Lean at v4.29.0, so
*"replay exits 0 at both ends"* — the acceptance gate that makes leg 1 verifiable — **cannot be
satisfied at the destination by anything that exists today.** Leg 2 therefore inherits a different
bar, and it is pre-registered as:

| # | leg-2 criterion | note |
|---|---|---|
| 1′ | replay clean at the **near** end (v4.26.0), through **both** checkers | the departure point is certified before departure; unchanged from leg 1 |
| 2′ | **57-footprint EQUALITY against the frozen v4.14.0 baseline** | the *same* baseline, not a v4.26.0 one — the invariant is end-to-end, and chaining it through intermediate baselines would let a drift launder itself across two comparisons |
| 3′ | **Lean4Lean replay at the far end, alone** | the only external kernel that can plausibly reach v4.32+ first; when it does, it *is* the gate, and the grade stays **independent kernel** |
| 4′ | criteria 3–6 unchanged | ledger, derivations, sorries, artifact drift |

**Launch condition = the expiry condition.** Leg 2 does not start until **at least one external
checker exists at the destination**. Migrating without one would silently downgrade the grade from
*dual kernel* to *single kernel, patched* — trading the class for the instance, i.e. reversing the
decision above without recording that it had been reversed. If the wait is the price of keeping the
grade, the wait is correct, and `watch_kernel_support.py` is what ends it.

**The cheaper path, and worth taking: contribute the lean4checker tag upstream.** Its tag history is
mechanical per release — bump `lean-toolchain` and `lake-manifest.json`, confirm the five negative
tests still fire, tag. Given that shape, *"lean4checker at v4.32.2"* is plausibly **a pull request
rather than a project**, and it is the intervention that opens the intersection from our side instead
of waiting for it. Pre-registered as the preferred way to reach leg 2.

---

# WHAT A FAILED STEP LOOKS LIKE — pre-registered, because surprises are expected

Eighteen versions of elaborator drift will produce at least one surprise. **The difference between a
migration and a mess is whether surprises halt the line or ride it**, and that is a rule that has to
exist before the first surprise, not after.

**A footprint that changes at v4.19 is a FINDING to be understood, not a diff to be accepted.** The
step does not advance until the delta is **attributed**: named cause, named version, written into
`MIGRATION_LOG.md`. Three outcomes are permitted for a halt, and there is no fourth:

1. **attributed, benign** — cause understood, invariant intact (e.g. a headline was *renamed*, so the
   footprint set is identical under the rename). Record the attribution, advance.
2. **attributed, real** — a proof now rests on something it did not before. Fix it *at that version*,
   or stop the migration at the last accepted stop. Both are acceptable; advancing is not.
3. **unattributed** — the line stays halted. "It only changed a little" is not an attribution, and
   "it still builds" was never the pass bar.

`checkpoint.py` has **no `--accept-anyway` flag**, deliberately. The only way past a footprint change
is to understand it and say so in the record.

**Rollback is a command, not a memory:** every accepted stop is committed and tagged
(`toolchain-stop/v4.19.0`, …), which is what makes *"every clean intermediate is a fallback position"*
true operationally rather than aspirationally.

**Expected surprises** (drift here is ordinary; the attribution is still mandatory): `mach_ring` /
`mach_mpoly` elaborators, `Nat` pattern-match compilation, structure-instance syntax, `simp`
normal-form changes, `Nat` literal handling, deprecation renames. **Anything outside that list moving
is itself the finding** — per the scope guard, it means the diff is doing something criterion 2 cannot
see.

---

# THE INSTRUMENT: one script captures every stop, and the "before" is frozen

`tools/migration/checkpoint.py` **is** the six-criterion pass bar, executable. The same instrument
captures the before and every after — a baseline measured by one tool and compared by another is two
tools, and the difference between them arrives disguised as a finding.

```
snapshots/v4.14.0-baseline/     # the migration's BEFORE: read-only, SHA256SUMS, --verify re-checks it
  verdict.json                  #   toolchain, lock, 6 gate exit codes, every count
  footprints.json               #   the 57 headline footprints
  logs/*.log                    #   including the replay log, verbatim
```

Every intermediate diffs against **that** directory, and `--verify` proves the before did not move
under the migration. A baseline that can be edited is not a baseline.

## House rule, third and final form: counts come from cross-derivation

The extractor incident of 2026-07-29 is the reason this is stated as a rule about *mechanisms* rather
than about care. A bracket-parse bug enumerated **122 garbage names** and still produced the **right
57 footprints** — the junk contributed none. The output was correct; the mechanism was broken; and the
only thing that could tell those apart was an *independently derived* 57 from the Lean-side gate.

> **A count is trustworthy when two derivations that share no code agree on it** — not when it looks
> right, and not when one careful reader checked it.

So `checkpoint.py` asserts the 57 **three** ways (Python bracket-parse of `headlines`, the kernel's own
`collectAxioms`, the Lean ledger gate's count) and treats disagreement as an **instrument failure that
halts the stop before any footprint is compared**. Every other count (252 axioms, 5 derivations, 2
allowlisted `sorryAx`) is parsed from the gate that derived it and compared to **the baseline's**
value — never to a literal in the script, which would just be a fourth place for the numbers to rot.

---

# AMENDMENT 1 — conditional **criterion 7**: dual replay at stops 3–5

**Recorded 2026-07-29, after stop 1 was accepted. Provenance: authorised in-session by the project
owner**, on the reasoning that the marginal cost is one command per stop and it front-loads the
destination configuration's debugging by three stops. It lives in *this* file rather than the log
because it changes the **pass bar**, and the pass bar's home is here. **Nothing above is amended** —
criterion 7 is *additive* and *conditional*, so the pre-registered bar stands unaltered for stops 1–2.

**Why it became available three stops early:** Lean4Lean pins `v4.16.0`. From stop 1 onward the
genuinely independent kernel can read our environment, which the plan did not expect until v4.26.0.

| | |
|---|---|
| **trigger** | Lean4Lean's maiden run at v4.16.0 fires **in both directions** — rejects a negative specimen *and* accepts `MachLib`. Protocol: `MIGRATION_LOG.md`, "Lean4Lean maiden run" |
| **if triggered** | **criterion 7** = *MachLib replays clean through Lean4Lean as well*, applied at stops **3 (v4.20.1), 4 (v4.23.0), 5 (v4.26.0)** |
| **if not triggered** | bar unchanged. `INSTRUMENT_UNVALIDATED` **outranks any replay result** — an unfired checker's PASS and its FAIL are equally uninformative |
| **stop 2 (v4.19.0)** | keeps the pre-registered bar **even if the trigger fires during it**. An instrument does not join a measurement midway; it joins at the next stop boundary — same rule that kept every stop-1 instrument change ahead of the pin |

**What it does NOT change:** the destination stays v4.26.0, the decision record stands, and the
expiry condition is untouched. Earning *"independent kernel"* earlier changes when the phrase can be
said — not which kernel carries the fix, which is what the expiry condition is watching.
