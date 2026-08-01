# Toolchain migration log — the running narrative for `v4.14.0 → v4.26.0`

Plan of record: [`BUMP_PLAN.md`](BUMP_PLAN.md) — destination, decision record, route, pass bar,
failure semantics, all pre-registered **before** the first step.

**Rules of this log**, restated because a log nobody is required to write is a log that stops:

* Every **accepted stop** gets an entry: gate exit codes, every count, the frozen snapshot's digest.
* Every **halt** gets an *attribution*: which change, in which version, caused which delta. A halt
  without an attribution stays open — "it still builds" is not an attribution, and there is no
  `--accept-anyway`.
* Findings that are **not** migration drift get recorded too, marked as such, so that a later reader
  can tell "the bump broke this" from "the bump *found* this".

---

## Stop 0 — `v4.14.0`, the frozen BEFORE (2026-07-29)

```
snapshots/v4.14.0-baseline/     SHA256SUMS digest 7746aacbb5bce7b0db6dbb0c57f6e7548cdd9339275bea1868cafeab894ff05a
```

Read-only on disk; `python3 tools/migration/checkpoint.py --verify snapshots/v4.14.0-baseline`
re-checks it. **Every intermediate diffs against this directory** — including leg 2's destination, so
the invariant is end-to-end rather than chained through intermediate baselines.

| criterion | gate | v4.14.0 |
|---|---|---|
| 1 | `check_kernel_replay.py` | **exit 0** — five negative tests fire, MachLib replays clean |
| 2 | 57 headline footprints | **57 captured, 0 missing** |
| 3 | `check_ledger.py` | **exit 0** — 252 axioms pinned, 57 headline footprints ⊆ trusted |
| 4 | `check_derivable.py` | **exit 0** — 5 derivations, retained base clean |
| 5 | `sorry_audit.lean` | **exit 0** — 1 sorryAx decl, allowlist 1 entry, exact correspondence |
| 6 | `check_artifact_drift.py` | **exit 0** |
| — | `check_toolchain.py` | **exit 0** — pin = lock = `v4.14.0` @ `410fab728470` |

Instrument identity at stop 0: kernel `v4.14.0` (`410fab728470`, aarch64-linux); `lean4checker`
`v4.14.0` at `~/lean4checker`; Lean4Lean **not running** (it never pinned v4.14.0 — that is what the
bump unlocks).

**The 57 is asserted three ways and they agree:** Python bracket-parse of `AxiomLedger.headlines` = 57,
the kernel's own `collectAxioms` = 57, the Lean-side ledger gate = 57. That three-way agreement is a
precondition of the capture, not a nicety — see the house rule in `BUMP_PLAN.md`.

### FINDING 0.1 — allowlist rot in the sorry audit. **Not migration drift; found by the baseline.**

The capture reported **1** sorryAx declaration against a **2**-entry allowlist, while
`tools/AUDIT_SORRY.md` prose claimed **2 carry it**. Nobody read any Lean to notice: two
independently derived counts failed to match.

* **Attributed.** `MachLib.HighDimensional.guarded_lowering_preserves_domain_annotations` was
  allowlisted as *"NOT closable as stated"* and then **closed anyway**, by
  `GuardedLowering.guarded_lowering_preserves_domain`, footprint `[propext]` — no foothold axiom, i.e.
  the good outcome. What failed was the **pruning**: the allowlist entry and the prose outlived the
  sorry by an unknown number of commits.
* **Why it matters in the safe-feeling direction:** an allowlist entry for a clean declaration is a
  standing licence for that sorry to come back **unnoticed**. The file's own comment said exactly this
  one entry earlier, and it happened anyway — which is the argument for a mechanism over a note.
* **Remedy (mechanical, not editorial):** `sorry_audit.lean` now **fails on allowlist rot** and names
  the remedy per entry (*present & proven → prune*; *absent → deleted or renamed*). Stale entry pruned;
  prose corrected in `AUDIT_SORRY.md`.
* **Firing specimen, historical rather than synthetic:** the check went RED on contact with the real
  stale entry, then GREEN after pruning. Both directions verified 2026-07-29.

This is the reassuring-error class again, and it *upgrades* the pattern: the previous three incidents
were summaries disagreeing with their enumerations. Here a **wrong enumeration produced a correct
output** — 122 garbage names from a bracket-parse bug whose junk contributed zero footprints, so the 57
came out right for reasons that would not have survived the next edit to the file. The output was
correct and the mechanism was broken. Only cross-derivation could tell those apart.

### Instrument changes made BEFORE the first step (so no measurement straddles one)

| change | why | verified |
|---|---|---|
| `tools/migration/checkpoint.py` (new) | the six-criterion pass bar, executable; one instrument captures the before and every after | produced stop 0 |
| `tools/migration/watch_kernel_support.py` (new) | the decision record's **expiry condition**, monitored rather than remembered | run: lean4checker max stable tag **v4.28.0**, Lean4Lean pin **v4.29.0**, threshold v4.32.2 → **STILL EMPTY**, exit 0. Independently reproduces the two enumerations `BUMP_PLAN.md` asserted by hand |
| `check_kernel_replay.py`: per-version checker path | one checker per stop, so a rollback is a `git checkout` and not a checker rebuild; the version-equality rule is unchanged | re-run at v4.14.0 **after** the edit: exit 0, same verdict as the baseline's log |
| `sorry_audit.lean`: rot check + prune | FINDING 0.1 | RED on real rot, GREEN after prune |

`lean4checker` **v4.16.0** built at `~/lean4checker-v4.16.0` and its five negative tests confirmed
firing there — *the instrument for stop 1 was validated before the pin moved*, so a failure at stop 1
cannot be confused with an unvalidated checker.

---

## Stop 1 — `v4.16.0` (kernel commit `128a1e6b0a82`)

Clean build (`lake clean` first, so no v4.14.0 `.olean` could survive to be read by a v4.16.0
kernel). **682s to first full pass, 4 modules failing out of 574.**

Checker for this stop: `~/lean4checker-v4.16.0`, tag `v4.16.0`, five negative tests confirmed firing
**before** the pin moved.

### Drift attributions — 4 modules, 3 distinct causes, all inside the pre-registered expected set

**1. `NormalizedPolynomialRootCount.lean:288` — `simp` no longer unfolds a `let`-bound alias.**
The proof did `let rest := normalizeCoeff cs; by_cases hrest : rest = []`, then closed the negative
case with `simp [hrest] at h`, where `h`'s condition mentions `normalizeCoeff cs` — the alias's
*value*, not the alias. v4.14 bridged that gap; v4.16 does not, so the goal survived.
**Fix: split on the term itself and drop the alias.** Not a simp-config change — removing the
indirection makes the proof independent of how far the elaborator will zeta-reduce.

**2. `TanhTaylorRemainder.lean:323` — `mach_mpoly` crossed the default heartbeat budget.**
5 atoms, coefficients to 129024, inside 200000 heartbeats at v4.14.0 and over them at v4.16.0.
**Fix: `set_option maxHeartbeats 400000`** — deliberately *not* the 1000000 its sibling
`Rtanh6_deriv` already carries, so the number keeps reporting what the drift actually cost
(>200k, ≤400k). Proof untouched.

**3. `TwoExpPfaffianExpSum.lean:1068,1074,1081` — three `simpa` sets naming the parts but not the composite.**
The sets listed `restrict`, `dX`, `dY`; the goals contain `restrictDX`/`restrictDY`, which are plain
`noncomputable def`s over those. v4.14 unfolded them anyway while matching `denote`'s equations;
v4.16 does not, so the goal kept an unreduced `denote (restrictDX ..)` — and the type mismatch
printed it verbatim, which is what made this a five-minute diagnosis rather than an hour.
**Fix: name the composites in the simp sets.**

**4. `Ekf2GainPriorBound.lean:158` — `mach_ring`'s phase-2 catch-all hit a cost cliff.**
**Fix: `mach_mpoly [pa, pb, pd, k00, k01, h00, h01, h10, h11]` — 6.4s, faster than the failure.**

The first version of this entry said *"the `ac_rfl` closer stopped closing"*. **That was wrong**, and
it was caught by asking the right question of a green checkmark: a custom tactic falling off a cliff
across a version boundary is not a migration casualty to route around, because the next 9-atom
identity finds the same cliff. Probed with the scratch-file procedure:

| phase-2 alternative | v4.16.0 behaviour |
|---|---|
| `ac_rfl` | **fails in 0.59s** — and never was the closer: after phase 1 the two sides differ by *more* than AC (nested negations), so `ac_rfl` cannot close this goal in any version |
| catch-all `simp [add_comm, add_assoc, add_left_comm, mul_comm, mul_assoc, …]` | **exhausts 4,000,000 heartbeats in 73s** |

So the mechanism is a **cost cliff in the permutative catch-all** — combinatorial in term size, hence
a budget question rather than a soundness or fragment one.

> **And `mach_ring` swallows it.** Phase 2 is `try (first | rfl | … | simp [AC..])`, so a timeout
> *inside* the `try` re-surfaces as a bare **"unsolved goals"**. The tactic **cannot distinguish
> "outside my fragment" from "out of budget"** — which is why this first read as a fragment miss, and
> which is also the engine of the phantom errors below. Do not trust a `mach_ring` failure message to
> tell you which of the two happened.

**Demoted honestly — the remainder is UNATTRIBUTED:** whether the catch-all itself got slower across
the bump, or whether phase 1's normal form changed and handed it a harder goal. Separating those needs
a **built v4.14.0 tree**, which this migration no longer has (the `lake clean` at stop 1 was the right
call for kernel hygiene and it cost this measurement). Recorded as open rather than left implied-solved
by a green build — see *Open items*.

The reading rule this produced is written up as a standing procedure below — it is the most reusable
thing stop 1 generated, and stop 2 is the largest jump on the route.

None of the four touched a statement, an axiom, or the austerity constraints — which is what
criterion 2 is for, and it is checked below rather than asserted here.

### VERDICT: **STOP ACCEPTED** (2026-07-29)

```
snapshots/v4.16.0/     SHA256SUMS digest bad51be6f5a8a848e2033eb401e52640f9f9db6ff6234d5981f5b40a8d68585e
```

| criterion | gate | v4.14.0 → v4.16.0 |
|---|---|---|
| 1 | `check_kernel_replay.py` via `~/lean4checker-v4.16.0` | **exit 0** — five negative tests fire, MachLib replays clean |
| 2 | **57-footprint equality vs the frozen baseline** | **PASS — 0 changed, 0 lost, 0 gained** |
| 3 | `check_ledger.py` | **exit 0** — 252 axioms, unchanged |
| 4 | `check_derivable.py` | **exit 0** — 5 derivations, unchanged |
| 5 | `sorry_audit.lean` | **exit 0** — 1 sorryAx decl, exact correspondence |
| 6 | `check_artifact_drift.py` | **exit 0** |
| — | `check_toolchain.py` | **exit 0** — pin = lock = `v4.16.0` @ `128a1e6b0a82` |

Every count identical to the baseline; the 57 still agrees across all three derivations. **Two
versions of elaborator drift moved four proofs and not one dependency** — which is exactly the claim
criterion 2 exists to make checkable, and the reason a "it still builds" bar would have been worth
nothing here: all four failures were *build* failures, and the interesting question was whether the
repairs changed what anything rests on. They did not.

Total cost: 682s first pass + 40s incremental after the fixes + four repairs, one of which was the
only real one.

`git tag toolchain-stop/v4.16.0` — this stop is now a fallback position.

### Newly unblocked at this stop, and NOT taken: Lean4Lean

Lean4Lean pins `v4.16.0` — one of the six versions it has ever pinned. **As of this stop the genuinely
independent kernel can, for the first time, read our environment.** It is deliberately *not* run here:
criterion 1 is lean4checker, the route's destination (v4.26.0) is where both checkers are meant to run,
and adding an unvalidated instrument mid-route would muddy exactly the attribution this log exists to
keep clean.

**Recommendation for the next session, as a decision rather than a default:** run Lean4Lean **once at
v4.16.0 as a smoke test of the instrument** — not as a gate. Debugging a from-scratch kernel's build,
CLI and replay time is strictly cheaper here, against a green tree, than discovering its quirks at the
destination while also holding four stops of drift in your head. If it replays clean, that is the
first evidence in this project's history for the phrase *independent kernel*, three stops before the
plan expected it.

---

## Stop 2 — `v4.19.0` (kernel commit `6caaee842e94`)

Clean build. **Three versions — the largest jump on the route — and the drift is almost entirely ONE
class**, which is not the class stop 1 taught us to expect.

Checker: `~/lean4checker-v4.19.0`, five negative tests confirmed firing before the pin moved.
Timing baseline for the *departure* point captured first (`snapshots/timing/v4.16.0.json`, 940.44s
across 41 modules) — the new archive-before-hygiene step, doing its job on its first outing.

### The class: Lean **core stdlib** API churn, ~180 call sites

Not tactic behaviour, not elaboration semantics — **binder signatures and names in `List`/`Nat`**:

| change | kind | sites |
|---|---|---|
| `List.mem_cons_self a l` → `List.mem_cons_self` | explicit → implicit | **~140** |
| `List.not_mem_nil a` → `List.not_mem_nil` | explicit → implicit | ~34 |
| `List.getLast?_eq_getLast l h` → `… h` | first arg implicit | 6 |
| `List.length_map l f` → `List.length_map f` | first arg implicit | 5 |
| `List.mem_map_of_mem f h` → `… h` | first arg implicit | 2 |
| `List.length_reverse _`, `List.head?_reverse l`, `List.nodup_range n`, `List.filter_sublist l` | args implicit | 6 |
| `Nat.pos_pow_of_pos n h` → `Nat.pow_pos h` | implicit **+ deprecated rename** | 12 |
| `List.length_eq_zero` / `_eq_one` / `_pos` → `…_iff` | deprecated renames | 33 |

**This refines the plan's scope-guard claim, and the refinement is worth having.** `BUMP_PLAN.md` says
*"MachLib's Mathlib-free discipline is the asset here"* — true, and it held completely for the
*elaborator* surface at stop 1. But **austerity does not insulate a project from Lean CORE's API**, and
core is exactly where the churn was over these three versions. The asset is narrower than stated:
Mathlib-free buys freedom from *library-semantics* drift, not from *core-API* drift.

### Two behaviour changes alongside it

**`dsimp only` became a no-op in `CoreModel.lean` (11 sites) and therefore an ERROR** — *"dsimp made no
progress"*. The `Int` model instance's field proofs were `by dsimp only; omega`; at v4.19 the goals
arrive already in that form. **Fixed by dropping `dsimp only`, deliberately NOT by wrapping it in
`try`.** A `try` would make the tree insensitive to the goal shape changing again, and the whole value
of stepping is knowing what changed when. `omega` remains the closer, so the failure mode stays loud.

**Structure-instance notation now collapses under eta** (`IterExpChainStructural.lean`, 2 proofs). The
idiom was *eta-expand, rewrite the fields, collapse*:

```
calc X = { evals := X.evals, relations := X.relations } := rfl
  _    = { evals := Y.evals, relations := Y.relations } := by rw [he, hr]
```

At v4.19 `{ evals := X.evals, relations := X.relations }` **elaborates straight back to `X`**, so the
middle goal arrived as `X = Y` with no projections in it and `rw [he]` had nothing to find. Writing the
constructor explicitly (`PfaffianChain.mk X.evals X.relations`) keeps them. This one was **on the
plan's predicted list** — "structure-instance syntax" — so it cost minutes.

### THE STOP HALTED FIRST — criterion 6, and it was the INSTRUMENT, not the tree

The first capture at v4.19.0 (`snapshots/v4.19.0/`, digest `2464fe0b…`) reports **STOP HALTED**. It is
left frozen exactly as it is: **a halt is evidence, not a mistake to erase.** Criteria 1–5 and the
footprints were green; criterion 6 exited 1.

**The numbers gave it away before any name did:**

```
artifact tree : 572 .olean      ORPHANED : 572   (every single one)
source tree   : 896 .lean       unbuilt  : 896   (every single one)
```

> **When a correspondence gate reports EVERYTHING on both sides, suspect the KEY — not the trees.**
> Total failure on both sides is not drift; it is a comparison that matched nothing. A gate that had
> mismatched *half* the tree would have been far more expensive to diagnose than one that mismatched
> all of it.

**Attributed: Lake moved the olean output at v4.19.0.** `.lake/build/lib/MachLib/X.olean` became
`.lake/build/lib/lean/MachLib/X.olean`. The gate keyed on `relative_to(.lake/build/lib)`, so every key
silently gained a `lean/` component — visible in the orphan list as `lean/MachLib/AbsoluteBridge`.

**Fixed by deriving the root instead of assuming it:** locate the directory holding the top-level
`MachLib.olean`. Works under the old layout, the new one, and the next one — Lake has now changed this
once, so hardcoding it a second time would be choosing to be surprised again.

**Both directions verified, because a repaired gate that has not been seen to fire is not a gate:**
clean tree → **PASS** (0 orphans of 572); planted `MachLib/ZZZDriftSpecimen.olean` → **FAIL, naming
it**; specimen removed → **PASS**. Same discipline as the allowlist-rot check at stop 0.

**Then re-captured at `snapshots/v4.19.0-r2/`** — a second capture at the same pin, with the repaired
instrument, against a byte-identical tree (only Python gates and documentation changed between the two).
The failure semantics permitted exactly this: outcome (1), *attributed and benign — cause understood,
invariant intact → record the attribution, advance.* What it did **not** permit was editing the gate
and quietly re-reading the old verdict as a pass.

### THE LEDGER GATE'S COST IS DENOMINATED IN **CORE'S** SIZE, and core doubled

Criterion 3 went from part of a ~5-minute checkpoint to **>15 minutes on its own**. Discriminated
before the number was filed as "just the stop-2 ledger cost", because the two candidate owners have
very different consequences — and **the answer was neither of the obvious ones**:

| measurement (at v4.19.0) | result |
|---|---|
| `.olean`s vs source modules | **572 / 581** — no artifact inflation; environment growth from build drift **ruled out** |
| `import MachLib` | **1.31s** |
| + one `collectAxioms` query | **1.20s** — a single query is free |
| + all **57** footprint queries | **3.35s** — *criterion 2 is cheap*; memoising it would buy nothing |
| `env.constants.toList` (335,762 constants) | **1.84s** — materialising the whole environment is cheap. **The first attribution written here blamed this, and it was wrong** |
| **Lean CORE theorem count, v4.16.0 → v4.19.0** | **20,874 → 43,907 — 2.10×** |

The cost is **guard (6)**, `AxiomLedger.lean:566`: it calls `Lean.collectAxioms` on **every theorem in
the entire environment** — core, `Std`, everything — to catch new call sites of a discharged legacy
axiom. Its runtime is therefore **O(theorems in core + ours)**, and core's theorem count *doubled* over
these three versions.

> **Nothing in MachLib got slower. The library we sit on got twice as big.** A guard whose cost is
> denominated in someone else's release cadence will get slower at every future bump, forever, with no
> change on our side.

**The fix is obvious and DEFERRED, deliberately** (open item 4): scope guard (6) by **module**, the way
`spineTheorems` already does — which still covers `Certcom.*` declarations defined in *our* modules
while excluding core, and weakens nothing, because a core theorem cannot cite a MachLib axiom.
**Not done mid-route**: narrowing a pass-bar gate between stops would make the stops incomparable,
which is the same rule that keeps instruments out of measurements they did not start.

**And the nuisance converts into a free instrument.** `AxiomLedger.lean` is the project's *only*
whole-environment traversal, which makes it — involuntarily — the most sensitive thing on the route to
environment size and representation. Its elapsed time is now **tracked per stop** by
`timing_profile.py` (gate files added at this stop; see below), giving a canary for *"the environment
got weird"* that no per-module criterion can see.

### THE PROFILE'S FIRST DIFF FOUND TWO FINDINGS POINTING OPPOSITE WAYS

`timing_profile.py --diff snapshots/timing/v4.16.0.json snapshots/timing/v4.19.0.json`, and **neither
half of this would have been visible to any gate.**

**1. v4.19 removed a pathology in the Pfaffian modules. The library got ~4.8× faster.**

| module | v4.16.0 | v4.19.0 | |
|---|---|---|---|
| `PfaffianGeneralSingleExpDescent` | **291.70s** | **0.65s** | ~450× |
| `PfaffianGeneralSingleExpCanon` | 148.65s | 1.35s | ~110× |
| `PfaffianGeneralSingleExp` | 118.16s | 3.60s | ~33× |
| `PfaffianGeneralBase` | 70.62s | 1.65s | ~43× |
| **41-module total** | **940.44s** | **196.59s** | **4.8×** |

**A number that good is a measurement bug until proven otherwise**, so it was checked before being
believed — the same scepticism a regression gets:

* **Same work?** `git diff toolchain-stop/v4.16.0 HEAD` on all five files: **empty**. Untouched by the
  ~180-site sweeps, so both numbers measure identical source.
* **Not a cache keyed on module identity?** An identical copy under a *fresh* module name
  (`ZZZTimingProbe`) also ran in **0.65s**.
* **Independent witness?** The clean builds: v4.16.0 needed **682s** to reach its first failure wall;
  v4.19.0 reached its own in **39s**, and the whole 574-module tree finished across all six rounds in
  well under half of v4.16's single pass.

> **Mechanism UNATTRIBUTED.** Something between v4.17 and v4.19 removed a pathological cost in those
> descent modules; *which* change is not known and was not chased. Recorded as measured-and-corroborated
> with the cause open — not as a v4.19 win we can explain.

**2. Meanwhile the ledger gate went the other way, and now dominates everything.**

```
modules   940.44s -> 196.59s     (-743.85s, the library got faster)
gates          --  -> 1109.57s   (AxiomLedger.lean 1032.81s + sorry_audit 76.76s)
TOTAL     940.44s -> 1306.16s
```

**`AxiomLedger.lean` alone is now 79% of all measured elaboration cost on this project.** That reframes
open item 4 from housekeeping to the single largest cost item on the route — while the code it guards
got nearly five times cheaper to check.

**Precision about what is measured vs inferred**, because the coverage gap only just closed: the
**1032.81s is the first MEASURED ledger number** (v4.16.0's profile has no gate-file entry, which is why
`--diff` honestly reports it as *newly budget-sensitive* rather than as a regression). The claim that it
*roughly doubled* rests on the checkpoint durations (~5 min total at v4.16 vs >15 min for this gate
alone at v4.19) plus core's theorem count going 20,874 → 43,907 — **inference, corroborated, not a
before/after measurement.** From stop 3 the diff is real.

### THE GATE-FILE COVERAGE GAP — the instrument was not watching the instruments

`timing_profile.py` profiled what `lake build` builds. **`AxiomLedger.lean` and `tools/sorry_audit.lean`
are not in that set** — they are elaborated only by the gates that run them — so the ledger's runtime
could double with nothing watching. That is the coverage lesson landing on the defence layer:

> **Gates are subjects too.** Anything the pass bar depends on gets the same instrumentation as the
> code the pass bar judges.

Closed at this stop: `GATE_FILES` is profiled sequentially after the module pool (a 15-minute
single-threaded sweep run alongside a 4-worker pool would inflate its number *and* its neighbours').
The v4.16.0 profile has no gate-file entries, so the first `--diff` will honestly report them as
**newly measured** rather than as regressions — two reference points from stop 3 onward.

### VERDICT: **STOP ACCEPTED** (2026-07-29, second capture)

```
snapshots/v4.19.0/      HALTED  digest 2464fe0b025e80fdc23347dff5e56e0388d0d24baa9411151497f9d7e7390642
snapshots/v4.19.0-r2/   ACCEPTED digest 8b0e5e264a015a0f31cd04bcf8677aba71ecf0114d87fd59919e3e36fe29e871
```

**Both frozen. Both kept.** The pair *is* the record: a stop that halted on an instrument defect, and
the same stop accepted after the instrument was repaired and shown to fire in both directions.

| criterion | gate | v4.14.0 → v4.19.0 |
|---|---|---|
| 1 | `check_kernel_replay.py` via `~/lean4checker-v4.19.0` | **exit 0** |
| 2 | **57-footprint equality vs the frozen baseline** | **PASS — 0 changed, 0 lost, 0 gained** |
| 3 | `check_ledger.py` | **exit 0** — 252 axioms (in >15 min; see the cost finding) |
| 4 | `check_derivable.py` | **exit 0** — 5 derivations |
| 5 | `sorry_audit.lean` | **exit 0** — 1 sorryAx decl, exact correspondence |
| 6 | `check_artifact_drift.py` | **exit 0** — 0 orphans of 572, *after* the key repair |
| — | `check_toolchain.py` | **exit 0** — pin = lock = `v4.19.0` @ `6caaee842e94` |

**Five versions of accumulated drift from the baseline, ~180 mechanical edits, two dead idioms, one
broken gate — and still ZERO changed axiom footprints.** The 57 agrees across all three derivations at
both pins.

`git tag toolchain-stop/v4.19.0` — second fallback position. Route: **2 of 5 stops done.**

### PATTERNS THAT DIED AT v4.19 — a list the destination's documentation wants anyway

A build error is loud. **An idiom that has become a no-op by construction is silent**, and it will be
reached for again by anyone who learned it from the surrounding code. So the technique gets recorded as
dead, separately from the two proofs that happened to break:

| dead idiom | why it is dead, not merely broken |
|---|---|
| **eta-expand → rewrite the fields → collapse** (`calc X = { f := X.f, g := X.g } := rfl; _ = { f := Y.f, g := Y.g } := by rw [hf, hg]`) | structure-instance notation whose fields are all projections of one term now **elaborates straight back to that term**. The middle goal arrives with no projections in it, so there is nothing for `rw` to find. The technique cannot work at v4.19+; write the constructor explicitly (`S.mk X.f X.g`) when you need the projections to survive |
| **`dsimp only` as a load-bearing normalisation step** | when it has nothing to do it *errors*, so it is not a safe no-op to leave in a proof across versions. Where the goal already arrives normalised, delete it — and let the real closer (`omega`, here) be the thing that fails loudly if the shape changes back |

### SIX ROUNDS, and that is structural rather than sloppy

66 errors → 18 → 1 → 2 → 3 → 0. **A failing module masks its dependents**, so every error inventory
during a migration is a **lower bound**, never an estimate of remaining work.

> **RULE: never size the remaining work from the current error count.** Fix the class, rebuild, re-read.
> The count going 66 → 18 → 1 → 2 → 3 is not thrash; it is dependents becoming visible as their
> dependencies compile.

**Bulk-fix procedure, and the sweep is not optional.** The mechanical fixes were applied by regex —
correct for ~180 sites — and **every apply was followed by a grep for survivors**. The survivors were
*always* the same shape: **parenthesized arguments** the token-class regex could not see
(`List.mem_cons_self a (lower rest)`, `Nat.pos_pow_of_pos (e₁ + e₂) …`, `List.length_reverse _`
in a second file). Regex alone would have left them to surface two rounds later, attributed to nothing.

---

## Stop 5 — `v4.26.0` (kernel commit `d8204c9fd894`) — **the old destination, arriving as a waypoint**

Clean build first attempt, **zero proof edits**, 128s. Instruments prepared before the pin moved:
lean4checker `v4.26.0` (five negative tests firing) and Lean4Lean `f37aeab`.

**Eight deprecation warnings, three names, all cleared at the version that raised them:**

| deprecated | replacement | sites |
|---|---|---|
| `List.getLast?_eq_getLast` | `List.getLast?_eq_some_getLast` | 5 |
| `List.sorted_mergeSort` | `List.pairwise_mergeSort` | 2 |
| `Int.ediv_add_emod` | `Int.mul_ediv_add_emod` | 1 |

`List.getLast?_eq_getLast` is **the same lemma whose binder change cost a fix at stop 2** — now renamed
as well, two stops later. That is the core-API churn pattern the scope-guard finding named: a small set
of `List` lemmas keeps moving, first in binders, then in names.

**Why deprecations get fixed at the version that warns, not later:** at v4.19.0 the `_iff` renames
arrived as warnings; left alone they would have become hard errors somewhere further along, attributed
to whatever stop tripped over them rather than to the version that deprecated them. Clearing them where
they appear keeps attribution honest and costs one regex per name.

## DESTINATION — `v4.32.2` (kernel commit `f3b06c705e6c`) — **the bump is complete**

`v4.14.0 → v4.16.0 → v4.19.0 → v4.20.1 → v4.23.0 → v4.26.0 → v4.28.0 → v4.32.2`. The pin now carries
the **#14577 kernel fix** that this entire migration was launched to reach.

**THE NUMBER THE MIGRATION EXISTS FOR — eighteen minor versions, end-to-end, never chained:**

| | |
|---|---|
| footprints | enumerated 57, captured 57, missing 0; cross-derived **57 / 57 / 57 AGREE** |
| `v4.14.0 → v4.32.2` | **CHANGED 0 · lost 0 · gained 0** |
| verdict | **FOOTPRINT EQUALITY: PASS — same theorems, same axioms, different kernel** |
| counts vs baseline | PASS — 242 axioms pinned, 5 derivations, 1 allowlisted `sorryAx` |

**Registry downgrade, recorded in the same commit that moves the pin — no silent grade change:**

> **`v4.32.2`: PINNED, PATCHED KERNEL, INTERNALLY GREEN, EXTERNALLY UNREPLAYED — pending instrument
> availability.** Criterion 1 `CHECKER_VERSION_MISMATCH` (lean4checker's stable tags stop at v4.28.0);
> criterion 7 `INSTRUMENT_ABSENT` (no Lean4Lean runs at any version we could use). Both cited to
> Amendment 5, which pre-registered this exact grade **before** the hop was walked. Upgrade triggers
> on `digama0/lean4lean#17` closing or a lean4checker tag ≥ v4.29; owned by `watch_kernel_support.py`.

**The last externally-certified pin is `v4.28.0`**, sealed and hash-verifiable. Every
*"was this environment ever independently verified?"* question points there.

### What four dark versions actually cost

**21 errors across 11 files, five build rounds, and ZERO deprecation warnings.** The zero is the
finding. Stops 2 and 5 were warned by their own compiler before anything broke; this hop could not be,
because **every failure was a tactic-behaviour change and there is no deprecation cycle for "this
tactic stops tolerating making no progress."**

| class | sites | repair |
|---|---|---|
| `simp only []` / `dsimp only at h` now errors when it makes no progress | 12 | removed — they provably did nothing |
| `simpa [List.map_map]` leaves the composition unreduced | 5 | `Function.comp_def` added |
| `rw`'s implicit closing `rfl` stopped firing | 1 | closing step stated explicitly |
| `omega` exhausts recursion on a 1000000 literal | 1 | `Nat.add_le_add`; both summand inequalities were already in hand |
| a `simpa` standing in for a **definitional equality** | 2 | `exact sys.nonzero` |

The last one is the lesson. `TwoExpPfaffianChain2Bridge` bridged two `PfaffianFn`s differing only in
`relations`, and `.eval` **never reads `relations`** — the file's own docstring said so. The `simpa`
was doing unfolding, not reasoning. **The first instinct — feed it a bigger simp set — was wrong and
failed;** the fix was to read the definitions and state the fact.

### Two instruments broke at the destination, and one of them stopped itself

**`tools/sorry_audit.lean`** used `CollectAxioms.collect`, which v4.32.2 made **private**. The public
`Lean.collectAxioms` existed all along — the gate was reaching into an implementation detail, and the
repair also removes the reason it can break again. Instrument breakage, not a subject regression: the
library built clean with its one allowlisted `sorry` while the gate could not compile.

**`checkpoint.py` refused to compare**, and this is the behaviour to keep: it reported
*"count 'allowlisted sorryAx decls' NOT EXTRACTED from sorry_audit — a count that cannot be derived is
an instrument failure, not a zero"* and **did not attempt the footprint comparison**. A gate that
declines to render a verdict it cannot support is the whole thesis of this repo, arriving unprompted.

### `AxiomLedger` guard (6): 874.77s → 4.17s, and why that needed proving

Open item 4 recorded guard (6)'s cost as denominated in **core's** theorem count, past 15 minutes and
worsening, with module-scoping deferred as the fix. At v4.32.2 it elaborates in seconds.

**Identical gate output was NOT accepted as evidence of identical coverage.** `"0 new legacy call
sites"` reads the same whether the sweep visited 43,907 theorems or 500, and v4.32 ships Lean's new
module system — a silently narrowed `env.constants` was a live hypothesis. So it was measured:

    env.constants total = 220108;  thmInfo = 98560;  MachLib-prefixed = 13253

Core had 43,907 theorems at v4.19. The sweep now sees **98,560** — coverage did not shrink, it more
than doubled, over a 210× speedup. **Open item 4's cost problem is retired by upstream, not by us**,
and the deferred module-scoping work is no longer needed for that reason.

*(Probe deleted in the same breath it was run — it was an instrument, not an artifact.)*

**One measurement caveat, filed against the profiler:** the first destination timing run recorded
`tools/sorry_audit.lean` at `1.31s, exit 1` — time-to-error, not time-to-elaborate. The JSON stores
the exit code honestly, but `total_seconds` sums failed runs alongside clean ones, so a reader
comparing totals compares a broken run against working ones. The re-capture is clean (43 modules, no
non-zero exits); `timing_profile.py` should exclude non-zero-exit modules from its total.

---

### What step 1b actually bought, counted as a schedule fact

Positive controls were added at 09:00 on 2026-07-30. At 12:28 the same day they answered the route's
largest open question in **five seconds**: Lean4Lean at v4.29.0 — `0c38ab8`, the commit carrying the
#14577 fix — SIGSEGVs on `Init.Prelude`. That killed *"the strongest single verification point on the
whole route"* before the pin ever moved toward it (see `BUMP_PLAN.md` Amendment 5).

**Count the counterfactual precisely, because it is the argument for can-acquit specimens generally.**
Without 1b the sequence was: advance the pin to v4.29.0 → run stop 7 → silent SIGSEGV, no output →
and the ambiguity *arrives with the pin already moved*, on an uncertified position, with the previous
morning's four-OOM-kill diagnostic cycle as the price of unwinding **which** of the two candidate
causes it was.

So the five-second control did not merely save time. **It moved the discovery to the cheap side of the
pin advance** — which is the entire design intent of a positive control, stated as a schedule fact
rather than as a principle. That is the line to give anyone who asks why a gate needs a can-acquit
specimen and not just a can-convict one:

> **It converted a stranded migration into an amendment.**

### CORRECTION — stop 5 was committed as "accepted" before it had been measured

Commit `cc54930f` is titled *"stop 5 accepted"*. **At the time it was written, criterion 2 — the
57-footprint equality, the strong one — had never been run at v4.26.0.** Every prior stop carries
`footprints.json`, `verdict.json` and `SHA256SUMS`; `snapshots/v4.26.0/` carried only `logs/`. The
prior session reached the build and the replay gates, hit the four OOM kills, and stopped before
`checkpoint.py`. The next session read a set of green replay gates and inferred a verdict from them.

**The instrument that renders acceptance is `checkpoint.py`, and it had not run.** Inferring the
verdict from whichever gates happened to be lying around is the same error as reading a checker's exit
code without asking whether the checker could testify — the failure this very stop is famous for,
committed in the commit that documents it.

**Measured afterwards, on a rebuilt v4.26.0 tree** (`checkpoint.py --label v4.26.0 --compare-to
snapshots/v4.14.0-baseline`):

| criterion | result |
|---|---|
| 2 — footprints | enumerated 57, captured 57, missing 0; count cross-derived **57 / 57 / 57 AGREE** |
| 2 — equality vs **frozen v4.14.0** | **CHANGED 0, lost 0, gained 0 — PASS** |
| 0, 1, 3, 4, 5, 6 | all exit 0; counts 242 axioms / 5 derivations / 1 allowlisted `sorryAx` |
| 7 | `INSTRUMENT_UNUSABLE` — Amendment 3 |

So the substance held and the process did not. Twelve versions of kernel drift moved **no** headline
footprint. The stop is sound; the word "accepted" preceded the evidence for it by one commit, and this
correction is what that costs. **A green gate you did not run is not a green gate.**

### Criterion 7 — `INSTRUMENT_UNUSABLE`, and the four crashes that were never about us

**The gates:** lean4checker `v4.26.0` **PASS** (five negative tests firing, `MachLib` re-checks clean,
06:17). Lean4Lean: **no verdict, in either direction.**

Lean4Lean v4.26.0 cannot replay **`Init.Core`** — Lean's own core library — on any of the three builds
that exist at this version (`f37aeab`, `6bca7f6`, `arena-v4.26.0`/`56d4dc5`). See `BUMP_PLAN.md`
Amendment 3 for the evidence table and the reasoning that chose recording over deferral.

**The failing names locate the bug:** `String.ofList` and `Char.ofNat` are exactly the pair
`Main.lean`'s string-literal special case inserts when a declaration contains a string literal. That
code path is broken at this version, which is also **why breakage is feature-conditional** and why 1b
now carries two specimens rather than one: an instrument that replays core fine could still choke on
whichever literal forms a given library happens to exercise. Ours exercises them; `FloatRealBridge`
failed on `Char.ofNat` specifically.

**Four OOM kills on 2026-07-30 (06:32, 06:44, 06:55, 07:09 — 59.0 to 90.4 GiB anon-rss) were a
symptom, not the fault.** `6bca7f6` does not crash; it fails to build its environment and then churns
through 572 modules emitting a phantom "problem" for each, at 61 GiB within 50 seconds. The memory was
the garbage, not the work. Two hypotheses were entertained and both were wrong: that the cause was
lean4lean's unbounded `IO.asTask` fan-out (refuted — `LEAN_NUM_THREADS` ∈ {1,2,4,8,16,unset} all fail
in 2–6s), and that the checkout was not the variable (refuted — it selects *which* failure mode).

**The near-miss is recorded in full under SCOPE POISONING**, as the newest substrate and its worked
example. Short form: an orderly non-zero exit carrying `unknown constant 'Nat'` is precisely what the
classifier read as `REPLAY_FAIL`, and only the OOM kill stopped this gate from convicting a tree
lean4checker had passed forty minutes earlier. **A crash prevented a lie.**

**Gate changes earned here**, both live before stop 5 was recorded:
* **step 1b, positive controls** — `Init.Core` + `MachLib.Sign` must PASS, or the gate halts at
  `INSTRUMENT_UNUSABLE` and step 2 never runs. ~15s, and it would have replaced all four OOM kills.
* **the foreign-constant backstop** — any `unknown constant` naming a non-`MachLib` constant is an
  `INSTRUMENT_ERROR`, never a `REPLAY_FAIL`. Verified not to mask a genuine finding: an unknown
  constant under `MachLib.` still reaches `REPLAY_FAIL` untouched.
* **`INSTRUMENT_OOM` / `INSTRUMENT_KILLED`** — a resource kill is not a fault. SIGKILL is uncatchable,
  so an OOM'd checker prints *nothing*; the empty output tail in `lean4lean_replay.f37aeab-CRASH.log`
  was the unread tell. OOM is now confirmed against the **kernel's** log by pid, never inferred from
  the signal, and it carries the `anon-rss` figure.

### The destination reversal cost nothing already spent

v4.26.0 was chosen as the destination because it is the newest version where **both** checkers exist,
on the argument that dual replay would force a false proof to be *"a defect in the type theory as
understood by two independent authors"*. That premise was refuted at stop 3, so v4.26.0 lost its reason
to be an endpoint and became a step toward the patch.

**Every stop up to here is identical work under either plan.** That is not luck: the intermediates were
picked for *checker availability*, which is a property of the versions themselves rather than of the
endpoint. A route planned by proximity to v4.26.0 would have had to be re-planned; a route planned by
where the instruments exist did not.

## Stop 4 — `v4.23.0` (kernel commit `50aaf682e9b7`)

**Clean build, first attempt, ZERO MachLib edits** — 121s, 0 errors, 0 deprecation warnings. Three
versions of drift (v4.20.1 → v4.23.0) and not one proof needed touching. The first stop where the
migration cost nothing but compute.

Instruments prepared before the pin moved, per the boundary rule: lean4checker `v4.23.0` (five negative
tests confirmed firing) and Lean4Lean `4faf514`.

### IT HALTED ON TWO GATES — one spurious, one a real finding about our own trust number

**Criterion 7 — SPURIOUS, attributed to the instrument.** Lean4Lean `4faf514` rejected three modules
with *"universe level of type_of(arg #2) of 'InnerKhovanskii.mk' is too big for the corresponding
inductive datatype"*. **Three witnesses say our declaration is fine:** the C++ kernel accepted it
(criterion 1 passed), Lean4Lean **`93abda0`** — the *first* commit in the same v4.23.0 window — accepts
the **same environment** exit 0, and the arithmetic agrees (`MachLib.Real : Type`, the structure at
`Type 1`, and arg #2's type `T → Real → Real` in `Type 0`). `4faf514` is
`chore: initial refactoring for typed defeq`; the regression is in the refactor. **This is the
walk-back fallback firing exactly as the rule prescribes** — and note the environment was held fixed
while the checker varied, which is what made it a controlled experiment rather than a guess.

**Criterion 3 — REAL, and it is about the project's headline trust number.** *"10 ledger entries name a
vanished axiom (rot)"*, all `_elambda_N`:

| what | evidence |
|---|---|
| all 10 were genuinely **`.axiomInfo`** at v4.20.1 | observed directly in a `git worktree` rebuild of `toolchain-stop/v4.20.1` — **not** inferred from `emit_ledger.py`'s filter |
| they are **lambda-lifted fields of structure-instance `def`s** | `intModel._elambda_1 : Int → Int`, `emlEmptyChain._elambda_2 : Fin 0 → Real → Real`, two SDR-solver lifts, one lower-solver lift |
| **no headline ever cited one** | 0 citations across **all six** frozen snapshots' `footprints.json` |
| **no real declaration cites one** | all **17** transitive citers under `MachLib` are `_cstage1`/`_cstage2`/`_closed_N._cstage2` compiler IR |
| why they vanished | v4.23.0's compiler stopped emitting them |

> **So "252 axioms pinned" counted 10 compiler artifacts as trust assumptions. The honest number is
> 242, and it always was.** `.axiomInfo` does not distinguish a human's assumption from the code
> generator's closure, and a name-prefix filter cannot either.

**Fixed three ways, because fixing only the list would have left the producer producing:**

1. **The list**: 10 entries removed, `knownAxioms` = **242**.
2. **The structure**: `liveAxioms` *and* `emit_ledger.py` now both exclude compiler artifacts by name
   predicate — the miscount is **unrepresentable**, not merely corrected. `emit_ledger.py` is where the
   10 entered, so patching only the checker would have left the generator free to re-add them.
3. **The audit trail**: `snapshots/count_amendments.json` records `252 → 242` with date, stop, reason,
   all five evidence lines, and an explicit `not_a_drift` note. `checkpoint.py` treats a **matching**
   amendment as expected and **still halts on any unlisted count change** — deliberately an audit
   trail, not the `--accept-anyway` this tool still refuses to have. The frozen baseline keeps saying
   252; the amendment explains why 242 is right. **Neither number is erased.**

**And this is the same coverage shape as stop 2's gate-file gap.** No gate asks *"does any non-headline
declaration depend on an axiom nobody pinned?"* — the leak check covers the 57 headlines, `spineTheorems`
covers the Option-D modules, guard (6) covers two specific discharged axioms. The 10 sat outside every
frame for as long as they existed. Recorded as open item 5.

**The last-commit rule needed its empirical form on first reuse.** At v4.20.1 the twelve commits after
the first were fixes, so *last* was right. At v4.23.0 the last commit pinning the version is
`chore: initial refactoring for typed defeq` — a mid-refactor state, not a stabilised one. So the rule
is not "read the commit messages and judge":

> **Default to the LAST commit pinning the version; walk backwards if the instrument fails to build or
> crashes.** The gate's `INSTRUMENT_ABSENT` / `INSTRUMENT_CRASH` codes drive the fallback, which keeps
> the choice mechanical instead of interpretive. (Here `4faf514` built and ran, so no walk-back was
> needed — but the rule now says what to do when it isn't.)

## Stop 3 — `v4.20.1` (kernel commit `b02228b03f65`)

**One version, one drift site in MachLib — and five defects in the instruments.** That ratio is the
finding, so the two are listed separately and by owner.

### MachLib drift: exactly one site

`TwoExpNonlinearCurveInstance.lean:188` — **`decide` now refuses a goal whose expected type contains
free variables** (*"expected type must not contain free variables … Use the '+revert' option"*). The
type was `¬⟨2, hv⟩ = ⟨1, _⟩`; the `by omega` proof terms inside the `Fin` literals drag the local
context in.

**The compiler's suggestion was declined**: `decide +revert` would make the proof depend on exactly the
behaviour that just changed. Routed through the file's own `fin3_ne_of_val_ne` instead — **and that
first attempt failed identically**, because the helper wants `p.val ≠ q.val`, so the goal became
`↑⟨2, hv⟩ ≠ ↑⟨1, _⟩`, still carrying the proof term. *The helper moves where the free variables appear;
it does not remove them.* `by simp` closes it by reducing the coercions away. Both the fix and the
failed reasoning are recorded at the site.

### Five instrument defects, four of them mine

| # | defect | failed in the… |
|---|---|---|
| 1 | error-count regex assumed **relative** paths; v4.20.1's Lake prints absolute ones | **reassuring** direction — reported `errors: 0` on a **failing** build |
| 2 | criterion-7 specimen `.olean` written to the olean root, not the module path | loud (checker could not find it) |
| 3 | criterion-7 step 1 classifier called an **instrument error** an **acceptance of `False`** | **alarming** direction — a false accusation |
| 4 | `cleanup()` deleted from the *old* buggy olean path, so the specimen **survived** | **contaminating** — see below |
| 5 | picked the **FIRST** commit pinning a version instead of the **LAST** | loud, eventually — a deterministic `double free` in the checker |

**Defect 4 is the instructive one: a gate that fails to clean up contaminates its own next check.**
The leftover `MachLib/ZZZSpecimenAddFalse.olean` — *a compiled proof of `False`* — was still on the
search path when step 2 replayed `MachLib`, so step 2 dutifully reported a smuggled `False`. And then
defect 3's classifier mislabelled *that* as a crash, because `uncaught exception:` is how lean4lean
reports ordinary rejections.

> **RULE, learned three times in one gate: classify by MECHANISM, not by message text.** A memory fault
> aborts the process (`SIGABRT`/`SIGSEGV` → negative returncode, or 134/139); a rejection is an orderly
> non-zero exit. Substring matching on error text got the verdict wrong in three different directions
> before the returncode test got it right.

**Defect 5 gives a rule for every remaining stop:** Lean4Lean's `7cc5a77` is the *first* commit pinning
v4.20.1 — a bare `chore: update lean` — and **twelve later commits still pin v4.20.1**, including
`fix: panic in error reporting`, `fix: duplicate declaration errors`, and `fix: more panics in error
reporting`. At `7cc5a77` the replay died with a deterministic `free(): double free detected in tcache 2`
on an environment that had replayed **clean** at v4.19.0. At `143d58a` — the last v4.20.1 commit — it
passes.

> **RULE: take the LAST commit that pins a version, not the first.** The first is the start of the
> support window, before that window's own fixes. This applies to Lean4Lean at every remaining stop.

### VERDICT: **STOP ACCEPTED** (2026-07-29) — first stop with a second kernel

```
snapshots/v4.20.1/   digest 5025a9ade66a727a134ed2271b13783f0a08a43ee4e566fb91a86a99967b6393
```

| criterion | gate | v4.14.0 → v4.20.1 |
|---|---|---|
| 1 | `check_kernel_replay.py` (lean4checker v4.20.1) | **exit 0** |
| **7** | **`check_lean4lean_replay.py`** (Lean4Lean `143d58a`) | **exit 0** — specimen rejected, MachLib replays clean. **First dual-kernel stop on this route** |
| 2 | 57-footprint equality vs baseline | **PASS — 0 changed, 0 lost, 0 gained** |
| 3 | ledger | **exit 0** — 252 axioms |
| 4 | derivable | **exit 0** — 5 derivations |
| 5 | sorry audit | **exit 0** — 1 decl, exact |
| 6 | artifact drift | **exit 0** — after cleaning up criterion 7's own litter |
| — | toolchain | **exit 0** — pin = lock = `v4.20.1` @ `b02228b03f65` |

**Six versions from the baseline. Zero changed axiom footprints, still.** Grade for this stop:
**two implementations, shared lineage** — the strongest phrase the evidence supports, and deliberately
not "independent kernel".

`git tag toolchain-stop/v4.20.1` — third fallback position. Route: **3 of 6 stops** on the amended
(v4.32.2) plan.

### And criterion 6 is the only gate that can catch criterion 7's litter

The smuggled declaration sits at the **root** namespace, so the ledger's prefix-filtered axiom
enumeration misses it; **nothing depends on it**, so no footprint moves; and it is **not a `sorry`**.
Only the source↔artifact tripwire sees it. **`artifact_drift` must therefore run AFTER
`lean4lean_replay`** — now recorded as load-bearing in `checkpoint.py`'s gate order rather than left as
an accident of how the list was typed.

---

## Lean4Lean maiden run (2026-07-29, on the green v4.19.0 tree) — **VALIDATED, and it refuted the plan**

Run before the pin advanced, per *an instrument does not join a measurement midway*. Commit `f8cd3d3`
(the one pinning v4.19.0), `lake build lean4lean`, dependency `batteries` — no Mathlib.

**Protocol result, with reason codes:**

| step | outcome |
|---|---|
| its own negative tests | **none shipped** — protocol anticipated this: use lean4checker's specimens |
| **negative specimen** — lean4checker's `AddFalse` smuggling test, ported into a MachLib module | **REJECTED, exit 1**, naming it: *"(kernel) declaration type mismatch, 'false' has type Prop but is expected to have type False"*. lean4checker rejects it identically |
| orphan check on its own build tree | clean (fresh clone, single build) |
| **replay `MachLib`** | **exit 0 — clean** |
| **verdict** | **`REPLAY_PASS`, instrument VALIDATED in both directions** |

Specimen removed afterwards and criterion 6 re-run: 0 orphans. The tree that produced this is the same
tree stop 2 was accepted on.

### But the maiden run's real finding is documentary, not experimental

**Lean4Lean's README disclaims independence** — *"derived directly from the C++ kernel implementation…
likely shares some implementation bugs with it (it's not really an independent implementation)"* — and
**its commit `0c38ab8` (2026-07-29 14:36) is `fix: soundness bug from leanprover/lean4#14577`**, one day
after the C++ fix, in `ElimNestedInductive`, threading a `LocalContext` through so nested parametric
arguments get type-checked. **The same defect, the same code path, fixed by reference to the same PR.**

> **The plan's central claim is refuted.** Dual replay at v4.26.0 (Lean4Lean `6bca7f6`, 2026-01-09)
> would have been **two checkers sharing one ported defect** — not "a defect in the type theory as
> understood by two independent authors". See the ⚠ finding at the top of `BUMP_PLAN.md` for the
> three-way destination table this opens, including **v4.29.0**, where the C++ kernel is unpatched but
> Lean4Lean **carries the check**.

**And the watch had the matching blind spot**, now closed: it asked *"does a checker exist at a kernel ≥
the fix?"* and never *"does the checker carry the fix?"*. It now greps both checkers' commit histories,
and today reports **`FIX PORTED INTO A CHECKER` (exit 2)** where yesterday's logic said `STILL EMPTY`.
A watch that tracks pins and tags would have missed the day the answer changed.

---

# Standing procedures earned at stop 1

## SCOPE POISONING — attribute the first failure in a shared-resource scope

**One failure produced three errors.** `maxHeartbeats` is per-**declaration**, so `hidp` exhausting the
4M budget made `hidr` (line 159) and the theorem's own `whnf` (line 144) time out as collateral. Both
pass untouched; `hidr` in **0.5s on the DEFAULT budget**. Two of three reported failures were phantoms.

> **RULE: a failure that exhausts a shared resource invalidates every report downstream of it in the
> same scope.** Attribute the *first* failure in a scope before believing anything reported after it,
> where **scope = whatever unit shares the exhausted resource** — a Lean declaration for heartbeats, a
> process for file descriptors, a shell for `$?` (the pipe-exit-code trap: an observer reading a
> register the failure already clobbered), a build for a lock, a test run for a poisoned fixture.

The generalisation is what makes it worth a rule rather than a note: this is not a Lean fact. It is the
observer reading state that the first failure already destroyed, which this project has now hit in at
least three unrelated substrates.

### Newest substrate: **an instrument, scoped to its own environment** (2026-07-30)

The shared resource is the checker's *constructed environment*, and the observer is the gate reading a
verdict out of it. Lean4Lean v4.26.0 fails to build its own environment — `unknown constant 'Nat'`,
`'Eq'`, `'String.ofList'` — and then dutifully reports a "problem" in every module it visits. Each
report is downstream of one failure, so all of them are phantoms, and the exit code carrying them is
an orderly non-zero: **the exact signature the gate read as `REPLAY_FAIL`**.

**The worked example, because the isolation procedure is what unwound it** — each step removing one
term from the hypothesis space rather than accumulating guesses:

| step | question | result |
|---|---|---|
| 1. config sweep | is the assumed lever real? | `LEAN_NUM_THREADS` ∈ {1,2,4,8,16,unset} → SIGSEGV in 2–6s, every one. **The lever was imaginary** |
| 2. differential | is the checkout the variable? | `f37aeab` SIGSEGV / `6bca7f6` runs and emits garbage. **Yes — it selects the failure mode** |
| 3. minimisation | is it scale or fan-out? | one small module, `MachLib.Sign`, reproduces both. **Neither** |
| 4. decisive control | is MachLib in it at all? | `Init.Core` — **Lean's own core** — fails identically. **MachLib removed from the hypothesis space entirely** |

Step 4 is the one that ends the argument, and it is only licensed because **lean4checker had passed
this same olean tree at 06:17 that morning**. That is what made "the tree is fine" a premise rather
than a hope; without it, step 4 shows only that two things are broken together.

**What the near-miss actually was.** Only the OOM kill stood between this gate and
`REPLAY_FAIL — the checker rejected our environment. This IS a finding.` A false accusation against a
clean tree, sourced from an instrument that cannot read `Nat`, and it would have been *believed* —
halting the stop and opening a MachLib soundness audit against a phantom. **A crash prevented a lie.**

This is the reassuring error's dangerous sibling: the **alarming** error, which is worse precisely
because it is not reassuring. A reassuring error buys false comfort and is caught the next time
someone looks hard. An alarming error *triggers real work* — it recruits the team's diligence against
a ghost, and the harder they look the more the phantom's authority is confirmed by the effort spent
on it. Nobody audits an alarm for being wrong; they audit the subject it names.

**Why it matters more at stop 2 than it did here:** three versions of drift, the largest jump on the
route, so multi-error modules are the expected case. Unattributed, each is a three-fix afternoon.
Attributed, each is one fix and two dismissals.

## The two-minute isolation procedure (named, so that it gets used)

1. Copy the **failing `have`/goal alone** into `foundations/scratch_<topic>.lean`, importing only what
   it needs (`MachLib.Ring`, `MachLib.MPolyRing`, … — not `MachLib`), inside the right `namespace`.
2. Give it the **default** budget first. A goal that passes at default proves it was collateral.
3. Vary **one** thing per run — the tactic, or the budget, never both — and `time` each run.
4. To attribute a composite tactic, **run its alternatives individually** (this is how `ac_rfl` was
   cleared and the catch-all convicted at stop 1); a `try`-wrapped alternative hides its own reason.
5. Delete the scratch file in the same commit as the fix. It is a probe, not an artifact.

Cost at stop 1: **~2 minutes per finding**, against a 40s incremental rebuild per blind attempt and a
three-error module that looked like three problems.

## ARCHIVE BEFORE HYGIENE — a measurement baseline is an artifact

Stop 1's `lake clean` was **correct** (no v4.14.0 `.olean` may survive to be read by a v4.16.0 kernel)
and it **destroyed the only tree that could answer** *"did the catch-all get slower?"*. That is this
project's own build-artifact-drift lesson **running in reverse**: there, artifacts outlived the source
that justified them; here, an artifact a gate would need was deleted by justified hygiene.

> **RULE: artifacts that a later question will need are snapshotted BEFORE hygiene destroys them.**
> The route has three `lake clean`s left, and each one destroys another potential baseline.

**So the stop-acceptance procedure grows a step, and it runs *before* the pin advances:**

```
python3 tools/migration/timing_profile.py          # -> snapshots/timing/<pin>.json
```

Wall-clock elaboration of every module that raises its own heartbeat budget — **41 at v4.16.0**, and the
set is **derived** from `set_option maxHeartbeats`, never listed, so it maintains itself. Then
*"did X get slower across stop N"* is `--diff` of two files:

```
python3 tools/migration/timing_profile.py --diff snapshots/timing/v4.16.0.json snapshots/timing/v4.19.0.json
```

**This is evidence, not a gate.** A slower module does not fail a stop; it answers a question that
otherwise costs a rebuilt tree. Comparability protocol: same machine, same `--workers` (recorded in the
file; a different count is a different instrument and `--diff` refuses).

**What it partly recovers:** the v4.16.0 profile is captured *now*, on the green tree, so when the
9-atom cliff surfaces again anywhere on the route the "slower or harder?" question costs minutes at
every boundary from here on. It cannot recover the v4.14.0 → v4.16.0 answer — that one still needs the
worktree in *Open items*.

---

# Lean4Lean maiden run — protocol pre-registered BEFORE the instrument is trusted

A fresh instrument's first failure is **ambiguous between "found a defect" and "I built it wrong"**, and
that ambiguity is worth exactly nothing at a trust boundary. So the maiden run is gated the same way
every other instrument here was:

1. **Its own negative tests first.** If Lean4Lean ships them, run them; if it does not, feed it
   lean4checker's five specimens (`AddFalse`, `AddFalseConstructor`, `ReplaceAxiom`,
   `UseFalseConstructor --fresh`, `ReduceBool`) — historical witnesses beat synthetic ones, and they
   are already built here.
2. **Then the orphan check on Lean4Lean's OWN build tree**, before trusting anything it says about
   ours. It is a Lake project like any other and accumulates `.olean`s like any other, and *the
   instrument that caught our build-artifact drift is not immune to the class it detects*. The 26
   orphaned modules found here on 2026-07-29 were found in a tree nobody suspected either.
   **Instruments get the same hygiene as subjects** — that is part of what upgrading *second opinion*
   to *independent kernel* costs.
3. **Then the environment.** `MachLib` at v4.16.0, on the green tree.
4. **Reason codes on the verdict**, so the row cannot be read as more than it is: `INSTRUMENT_ABSENT`
   / `INSTRUMENT_UNVALIDATED` (negative tests did not fire) / `INSTRUMENT_UNUSABLE` (positive controls
   did not pass) / `INSTRUMENT_TREE_DIRTY` (its own build tree has orphans) / `VERSION_MISMATCH` /
   `REPLAY_FAIL` (defect in our environment) / `REPLAY_PASS`.
   **`INSTRUMENT_UNVALIDATED` outranks any replay result** — an unfired checker's PASS and its FAIL are
   equally uninformative, and a PASS from an unvalidated instrument is the reassuring-error class
   wearing a kernel's authority. **`INSTRUMENT_UNUSABLE` likewise outranks `REPLAY_FAIL`.**

   > **THE ASYMMETRY THIS REGISTRY WAS BUILT WITH, AND THE HALF IT WAS MISSING.** Every code above
   > guarded against an **unearned acquittal** — `INSTRUMENT_UNVALIDATED` exists precisely so an
   > unfired checker cannot hand us a `REPLAY_PASS` we did not earn. *Nothing outranked
   > `REPLAY_FAIL`.* The registry was built by people worried about being reassured, and an
   > instrument that convicts does not feel reassuring, so the symmetric hole went unnoticed until an
   > instrument that could not resolve `Nat` came within one OOM kill of convicting a clean tree.
   >
   > **RULE: every verdict-rendering gate needs both a can-convict specimen and a can-acquit
   > specimen.** Negative controls prove the instrument can fire; positive controls prove it can hold
   > fire. A gate with only the first can distinguish "guilty" from "broken" in exactly one
   > direction, and it is the *cheap* direction. This is general — it is not a fact about kernel
   > replay — and **the gate census has only ever demanded the first**, so every gate in this repo is
   > presumed half-validated until its positive control is named.
5. **Both directions before it counts**, per the standing gate rule: seen to reject something, and
   seen to accept our environment. Until then the registry says *second opinion*, unchanged.

   > This clause was **stated correctly and enforced by nothing** from 2026-07-29 to 2026-07-30. The
   > gate read "seen to accept our environment" as *step 2 exits 0* — but step 2 is the measurement,
   > and a measurement cannot also be its own validation. The acceptance half needs a specimen whose
   > answer is known in advance, exactly as the rejection half always had. Written rules are not
   > controls; only firing specimens are.

**Then, and only then, criterion 7 activates for stops 3–5** — dual replay through both kernels, one
extra command per stop, front-loading the destination configuration's debugging by three stops. See
`BUMP_PLAN.md`; it is pre-registered there as conditional, not adopted here by momentum.

---

# Open items

| # | item | status | why deferred, and what settles it |
|---|---|---|---|
| 1 | Does `mach_ring`'s permutative catch-all carry a **latent cost cliff** independent of the bump — did it get slower, or did phase 1 hand it a harder goal? | **worked around, mechanism partly unattributed** | Needs a **built v4.14.0 tree** to compare; `lake clean` at stop 1 removed it (correct for kernel hygiene, and it cost this measurement). Cheapest settlement: a `git worktree` at `dec74242` with its own toolchain, built once, and the two probes replayed there. Do it **before stop 4**, not after — a second 9-atom identity anywhere on the route will hit the same cliff, and it will present as "unsolved goals" |
| 2 | `mach_ring` **cannot distinguish "outside my fragment" from "out of budget"** — `try (first | … )` swallows the timeout | **designed, not implemented** — design note below | Implementing it touches the tactic used by hundreds of proofs, mid-migration, which the scope guard forbids. Deferred to after the destination *with the design fixed now*, so it is a coding task and not a rediscovery |
| 3 | Lean4Lean maiden run | **DONE at stop 1, validated both directions; criterion 7 live from stop 3** | — |
| 5 | **No gate asks "does any NON-headline declaration depend on an axiom nobody pinned?"** The leak check covers the 57 headlines, `spineTheorems` covers the Option-D modules, guard (6) covers two specific discharged axioms. The 10 `_elambda` non-axioms sat outside every frame for as long as they existed | **open** | A whole-namespace sweep would catch it, but that is guard (6)'s cost profile (~11 min) again — so it belongs with open item 4's module-scoping work, where the sweep gets cheap enough to widen. Same coverage shape as stop 2's gate-file gap: the instrument watched what it was pointed at |
| 4 | `AxiomLedger.lean` guard (6) sweeps `collectAxioms` over **every theorem in the environment**, so criterion 3's cost is denominated in **core's** theorem count — which doubled (20,874 → 43,907) across v4.16 → v4.19, taking the gate past 15 minutes | **attributed, fix deferred** | Fix: scope by module like `spineTheorems` does (covers `Certcom.*` decls in our modules, excludes core, weakens nothing — a core theorem cannot cite a MachLib axiom). **Deferred to after the destination**: narrowing a pass-bar gate between stops makes the stops incomparable. Gets more valuable every stop, since core keeps growing |

## DESIGN NOTE (open item 2) — make the swallowed timeout speak

**Three incidents, one root**, which by this project's arithmetic makes it structural rather than
unlucky: a `sorry` swallowed by `mach_ring`'s `try`, the phantom errors at stop 1, and the
misattribution in this very log. **`try (first | A | … | Z)` collapses "outside my fragment" and "out of
budget" into the same silence**, and every one of those three incidents is that single lie propagating.

The isolation procedure finds the truth in two minutes. **An instrument would have prevented the false
filing in zero** — so the scope-poisoning table should end up with an instrument, not only a procedure.

**Mechanism, fixed now so implementing it later is typing rather than thinking.** The heartbeat timeout
arrives as an ordinary `Exception.error` whose message contains *"deterministic timeout"*, which is why
`first`/`try` catch it like any failure. Two viable repairs, in preference order:

1. **Catch, inspect, re-throw.** Wrap phase 2 in an elab-level combinator that `tryCatch`es, tests the
   message for the timeout signature, and **re-throws on timeout while swallowing genuine failure**.
   Then "out of budget" surfaces as itself and "outside my fragment" still degrades gracefully. Costs
   ~20 lines of `Lean.Elab.Tactic` and turns `mach_ring`'s failure message into evidence.
2. **Bound the catch-all separately.** Give the permutative alternative its own small budget
   (`set_option maxHeartbeats <n> in`), so exhausting it fails *that alternative* rather than the
   declaration, and the declaration's remaining budget survives to elaborate the rest. This kills the
   **scope poisoning** as a side effect — the phantom errors were the declaration's budget being spent
   by one alternative — but it does not by itself distinguish the two failure modes, so it is the
   cheaper half-measure. Doing both is right.

**Crude interim, available at zero risk to the library:** the alternatives can be run individually in a
scratch file (step 4 of the isolation procedure). That is exactly how `ac_rfl` was cleared and the
catch-all convicted, and it needs no change to any tactic.
