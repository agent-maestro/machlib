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

---

# Lean4Lean maiden run — protocol pre-registered BEFORE the instrument is trusted

A fresh instrument's first failure is **ambiguous between "found a defect" and "I built it wrong"**, and
that ambiguity is worth exactly nothing at a trust boundary. So the maiden run is gated the same way
every other instrument here was:

1. **Its own negative tests first.** If Lean4Lean ships them, run them; if it does not, feed it
   lean4checker's five specimens (`AddFalse`, `AddFalseConstructor`, `ReplaceAxiom`,
   `UseFalseConstructor --fresh`, `ReduceBool`) — historical witnesses beat synthetic ones, and they
   are already built here.
2. **Then the environment.** `MachLib` at v4.16.0, on the green tree.
3. **Reason codes on the verdict**, so the row cannot be read as more than it is: `INSTRUMENT_ABSENT`
   / `INSTRUMENT_UNVALIDATED` (negative tests did not fire) / `VERSION_MISMATCH` / `REPLAY_FAIL`
   (defect in our environment) / `REPLAY_PASS`. **`INSTRUMENT_UNVALIDATED` outranks any replay result**
   — an unfired checker's PASS and FAIL are equally uninformative.
4. **Both directions before it counts**, per the standing gate rule: seen to reject something, and
   seen to accept our environment. Until then the registry says *second opinion*, unchanged.

**Then, and only then, criterion 7 activates for stops 3–5** — dual replay through both kernels, one
extra command per stop, front-loading the destination configuration's debugging by three stops. See
`BUMP_PLAN.md`; it is pre-registered there as conditional, not adopted here by momentum.

---

# Open items

| # | item | status | why deferred, and what settles it |
|---|---|---|---|
| 1 | Does `mach_ring`'s permutative catch-all carry a **latent cost cliff** independent of the bump — did it get slower, or did phase 1 hand it a harder goal? | **worked around, mechanism partly unattributed** | Needs a **built v4.14.0 tree** to compare; `lake clean` at stop 1 removed it (correct for kernel hygiene, and it cost this measurement). Cheapest settlement: a `git worktree` at `dec74242` with its own toolchain, built once, and the two probes replayed there. Do it **before stop 4**, not after — a second 9-atom identity anywhere on the route will hit the same cliff, and it will present as "unsolved goals" |
| 2 | `mach_ring` **cannot distinguish "outside my fragment" from "out of budget"** — `try (first | … )` swallows the timeout | **recorded, not fixed** | A real repair means restructuring the tactic (e.g. run the catch-all outside `try`, or bound it with its own `maxHeartbeats` and report the distinction). That is a tactic change, and the scope guard says the migration does not modernise tactics. File it for after the destination |
| 3 | Lean4Lean maiden run | **unblocked at stop 1, not attempted** | Protocol above. Do it against the green v4.16.0 tree |
