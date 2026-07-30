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

---

# AMENDMENT 3 — criterion 7 recorded **`INSTRUMENT_UNUSABLE` at stop 5** (2026-07-30)

**Recorded after stop 5's build and lean4checker gate both passed. Provenance: authorised in-session
by the project owner**, on the reasoning below. It lives here because it touches the **pass bar**, and
because a pre-registered criterion that cannot be met is amended in the open or not at all — the 4′
precedent: **VOID is the amendment path, never a silent drop.**

**Criterion 7 is not waived at stop 5. It is recorded as UNMEASURABLE, for instrument reasons proven
upstream of the subject.** The distinction is the whole content of this amendment: a waiver says *we
chose not to look*; `INSTRUMENT_UNUSABLE` says *we looked, and the instrument could not answer* — and
names the evidence that puts the void on the instrument's side of the boundary.

| | |
|---|---|
| **what was run** | the replay gate's new step **1b** (positive controls), against **every** Lean4Lean build that exists at `v4.26.0` |
| **`f37aeab`** (pinned) | `Init.Core` → `unknown constant 'String.ofList'`; `MachLib.Sign` → SIGSEGV |
| **`6bca7f6`** (last commit on the version) | `Init.Core` → `unknown constant 'Nat'`; `MachLib.Sign` → `unknown constant 'LE.le'` |
| **`56d4dc5`** (`arena-v4.26.0`, probed per the owner's bounded-probe instruction) | `Init.Core` → `unknown constant 'String.ofList'`; `MachLib.Sign` → SIGSEGV |
| **the decisive control** | **`Init.Core` is Lean's own core library.** Three independent builds cannot replay it. MachLib is not in the hypothesis space |
| **the licensing premise** | `lean4checker v4.26.0` replayed **this same olean tree** clean at 06:17 the same morning. That is what makes "the tree is fine" a premise rather than a hope |
| **verdict** | criterion 7: `INSTRUMENT_UNUSABLE` — **no verdict about MachLib, in either direction** |

**Why (b) and not (c) — hold stop 5 until v4.32.2.** Holding would couple this migration's completion
to an upstream project's release cadence, and **that coupling is already owned** by the expiry watch.
The destination asks the instrument question again regardless, so deferring buys exactly one fewer
asking, at the price of an open-ended stall against a repo we do not control.

**Why the probe was worth 30 minutes anyway.** `arena-v4.26.0` existing on origin is evidence someone
upstream hit trouble at this version and tried something. Had it passed 1b, criterion 7 would have
been *satisfied* at stop 5 with an annotation that the instrument came from a non-default branch —
recorded and defensible, and strictly better than an amendment. It failed, fast and honestly, which is
what a bounded probe is for. **Cost: one build, three gate runs, ~15 seconds each.**

**What this does NOT license.** Stop 5 is accepted on criteria 1–6 and the lean4checker replay, which
is exactly the bar stops 1–2 were accepted under. The `SECOND OPINION` grade stands unchanged; nothing
in this stop earns *"independent kernel"*, and the ⚠ finding below already established that the phrase
was not on offer at this version regardless.

---

# ⚠ FINDING THAT REFUTES THIS PLAN'S CENTRAL PREMISE (2026-07-29, before stop 3)

**The decision record above argues that v4.26.0's dual-kernel configuration is worth more than
v4.32.2's patch because "a false proof must be a defect in the type theory as understood by two
independent authors". THAT PREMISE IS FALSE, and it is refuted by primary sources, not by argument.**

**1. Lean4Lean disclaims independence, in its own README:**

> *"It is derived directly from the C++ kernel implementation, and as such **likely shares some
> implementation bugs with it (it's not really an independent implementation)**, although it also
> benefits from the same algorithmic performance improvements existing in the C++ Lean kernel."*

The plan asserted it "re-derives the typing rules from the theory rather than the implementation".
**Its author says the opposite.** The assertion was never checked against the source — this is the
`assert_normalised_cleanly` shape applied to a trust argument, which is exactly what
`TOOLCHAIN_EXPOSURE.md` warned about *for this very bug*.

**2. And for #14576 specifically the defect was SHARED — confirmed by Lean4Lean's own fix commit:**

```
0c38ab8  2026-07-29 14:36  fix: soundness bug from leanprover/lean4#14577
         Lean4Lean/Inductive/Add.lean | 19 +++++-------
```

One day after the C++ fix merged, in `ElimNestedInductive`, threading a `LocalContext` through so the
nested parametric arguments can be type-checked — **the same defect, in the same code path, fixed by
reference to the same PR.** Lean4Lean had the bug too.

> **So dual replay at v4.26.0 would NOT have covered #14576.** Its Lean4Lean commit is `6bca7f6`
> (2026-01-09), seven months before either fix. Two checkers, one ported defect, zero coverage of the
> instance the whole tradeoff was argued around. *"Independence covers the class"* was not wrong as a
> principle — it was **inapplicable, because these two implementations are not independent.**

**3. What is now true, and it changes the option set:** a **patched Lean4Lean exists** (`0c38ab8`), and
it pins **v4.29.0**. So at v4.29.0 the configuration is *unpatched C++ kernel + **patched** Lean4Lean* —
the second checker would actually **detect** a #14576-class exploit in our environment, by carrying the
check rather than by being assumed to have re-derived it.

| destination | C++ kernel | Lean4Lean | lean4checker | covers #14576 in OUR env? |
|---|---|---|---|---|
| **v4.26.0** (current plan) | unpatched | `6bca7f6`, **unpatched** | v4.26.0 ✓ | **NO — shared defect** |
| **v4.29.0** | unpatched | `0c38ab8`, **PATCHED** | rc tags only | **YES — via the second checker** |
| **v4.32.2** | **patched** | cannot read it | none | YES — via the kernel |

**4. The watch script had a matching blind spot, now fixed.** `watch_kernel_support.py` asked *"does a
checker exist at a version ≥ the fix?"* — it never asked *"does the checker itself carry the fix?"*
Those are different questions and the second one is the one the class/instance argument depends on. A
watch that tracks pins and tags would have reported STILL EMPTY on the very day the relevant thing
changed.

---

# AMENDMENT 2 — **DESTINATION CHANGED TO v4.32.2** (2026-07-29)

**Provenance: chosen by the project owner**, presented with the three-way table above, *after* the
independence premise was refuted. This reverses the destination in the decision record, and the reversal
is recorded here rather than by editing that record — **it stands as written, including its now-false
premise, because a plan that quietly rewrites its own reasoning teaches nothing.**

**Why the reversal is coherent rather than a change of mind:** the original argument rejected v4.32.2
because *"a false proof must be a defect in the type theory as understood by two independent authors."*
That barrier does not exist — the two checkers are one implementation ported into two languages, and
they shared this exact defect until 2026-07-29. **Take the patch, which is real, over independence,
which was not.**

## What this costs, stated plainly

At v4.32.2 **no external checker can read our environment at all** (lean4checker ≤ v4.28.0,
Lean4Lean ≤ v4.29.0). So we lose more than the dual-kernel grade:

* **The #14576 instance is covered** — by the kernel itself. This is the gain, and it is the one thing
  no configuration below the fix can give us today.
* **Environment-manipulation replay is LOST.** That was lean4checker's *full-strength* class — the one
  where its partial independence never mattered, and the class whose first run here found 26 orphaned
  `.olean`s. Nothing at v4.32.2 replaces it.
* **Grade at the destination: `single kernel, patched, no external replay`.** The registry must say
  exactly that. Not "verified by two kernels", not "independently checked".

## The route now ends with its own strongest verification point

The intermediates were chosen for *checker availability*, so the route extends rather than truncates —
and the last two stops are deliberately where the instruments run out, in order:

| stop | lean4checker | Lean4Lean | note |
|---|---|---|---|
| **v4.20.1** ← next | stable tag ✓ | pins it ✓ | criterion 7 live (both) |
| **v4.23.0** | stable tag ✓ | pins it ✓ | criterion 7 live (both) |
| **v4.26.0** | stable tag ✓ | pins it ✓ | **was the destination**; now a stop |
| **v4.28.0** *(recommended)* | stable tag ✓ — **the last one** | no pin | last stop with a version-matched stable lean4checker |
| **v4.29.0** | rc tags only | **`0c38ab8`, PATCHED** ✓ | **the strongest single verification point on the whole route**: replay through a checker that CARRIES the #14577 check, against a kernel that does not. If our environment contains the exploit class, this is the stop that finds it |
| **v4.32.2** | ✗ | ✗ | destination. Dark hop: footprint equality + criteria 3–6, no external replay |

**The final hop's bar** — pre-registered here, before it is walked: replay clean at the **near** end
(v4.29.0, through patched Lean4Lean), **57-footprint equality against the frozen v4.14.0 baseline**
(end-to-end, never chained), criteria 3–6 green, and **an explicit registry downgrade** recorded in the
same commit that moves the pin. No silent grade change.

## Restoring external replay is now a named deliverable, not a nice-to-have

`leg 2`'s note said contributing the lean4checker tag upstream was *"plausibly a PR, not a project"*.
With the destination at v4.32.2 that PR is **the only path back to any external replay**: bump
`lean-toolchain` + `lake-manifest.json`, confirm the five negative tests still fire, tag. Promoted from
opportunity to **follow-up deliverable**, and `watch_kernel_support.py`'s question becomes *"has any
checker reached v4.32.2 yet"* — the same watch, now watching for restoration rather than for permission.

---

# FINDING AGAINST THE SCOPE GUARD (stop 2) — the austerity asset is narrower than claimed

The scope guard above says *"MachLib's Mathlib-free discipline is the asset here … a base that
axiomatises `Real` and forbids `by_contra` exposes far less surface to elaborator drift"*, and predicts
the cost lands in the custom machinery. **Stop 1 confirmed that exactly.** **Stop 2 did not.**

At v4.19.0 the drift was **~180 call sites of Lean CORE `List`/`Nat` API churn** — explicit binders
becoming implicit (`List.mem_cons_self`, `List.not_mem_nil`, `List.length_map`, …) and `_iff` renames
(`List.length_eq_zero` → `List.length_eq_zero_iff`, `Nat.pos_pow_of_pos` → `Nat.pow_pos`). Not one of
those is a Mathlib coupling, an elaborator quirk, or a tactic.

> **Refinement, not a correction: austerity buys freedom from LIBRARY-SEMANTICS drift, not from
> CORE-API drift.** Mathlib-free means nothing chose those `List` lemmas for us — we chose them, and
> they are still someone else's API on someone else's release cadence.

**BOTH HALVES BELONG IN THE FINDING, or stop 3's expectations get calibrated to the scarier reading.**

* **The ~180 sites are SHALLOW drift.** Mechanical, bulk-attributable, fixed by regex plus a survivor
  sweep, and **no proof content moved** — a renamed lemma and an implicit binder are not mathematics.
* **The DEEP kind — what the guard was actually about — arrived exactly twice**: `dsimp only` becoming
  a no-op-and-therefore-an-error, and structure-instance notation collapsing under eta. **Both
  attributed, neither semantic.**

> **So the guard failed as stated and its INTENT held: the mathematics did not move, the surface did.**
> Three versions of drift, ~180 mechanical edits, two behaviour changes, and — per criterion 2 — zero
> changed axiom footprints.

Left as an amendment rather than an edit to the pre-registered text above, which stands. Full
attribution table in `MIGRATION_LOG.md`, stop 2.

---

# NAMED RULE — an instrument does not join a measurement midway

Promoted from a table row because it governs three separate decisions on this route and will be under
the most pressure at the end of it.

> **An instrument joins at a stop boundary, never inside a stop.** Every instrument change is completed,
> and re-verified at the *old* reference point, before the pin moves.

Three applications, one already exercised:

* **Stop 1 (done).** The per-version checker resolver was edited, then the replay gate was re-run **at
  v4.14.0** to establish verdict stability across the tooling edit, and only then did the pin move.
  Same for `lean4checker v4.16.0`: built and its five negative tests confirmed firing *before* the bump,
  so a stop-1 failure could not be confused with an unvalidated checker.
* **Stop 2.** Keeps its pre-registered bar **even if criterion 7's trigger fires while stop 2 is in
  flight.** Lean4Lean joins at stop 3.
* **The destination, where this will be hardest.** When the strong checker is finally validated here,
  there will be real temptation to let it **retroactively bless stops 1–2**. It must not.

> **Stops 1–2 were accepted under their pre-registered bars, and that is what their acceptance means.**
> Re-checking them with Lean4Lean afterwards is **new evidence about old stops** — recorded as new
> evidence, with its own date and reason code. It is *not* a retroactive amendment to what those
> acceptances meant, and it cannot be, because the bar a stop passed is a historical fact about that
> stop. (If a later Lean4Lean replay *fails* on a stop that passed, that is a finding about the stop
> and about the two checkers' disagreement — which is precisely the evidence dual replay exists to
> produce, and it is worth far more than a re-labelled checkmark.)

## And the corollary for baselines: archive before hygiene

Stop 1's `lake clean` was correct and destroyed the tree that could have answered *"did the catch-all
get slower?"*. **A measurement baseline is an artifact, so artifacts a later question will need are
snapshotted before hygiene destroys them.** The stop-acceptance procedure therefore grows a step, run
**before** each pin advance:

```
python3 tools/migration/timing_profile.py     # -> snapshots/timing/<pin>.json
```

Wall-clock elaboration of every module that raises its own heartbeat budget — the set **derived** from
`set_option maxHeartbeats`, so it maintains itself. Three `lake clean`s remain on this route; each one
would otherwise destroy another baseline. **Evidence, not a gate** — a slower module does not fail a
stop.
