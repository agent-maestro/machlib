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

**4. `Ekf2GainPriorBound.lean:158` — `mach_ring`'s `ac_rfl` closer stopped closing.**
The Joseph-form congruence identity (9 atoms, degree 4) normalises to a large AC residue that
`mach_ring`'s final `ac_rfl` used to close. At v4.16 it spends 21s and leaves the goal.
**Fix: `mach_mpoly [pa, pb, pd, k00, k01, h00, h01, h10, h11]` — 6.4s, faster than the failure.**
This is the standing house rule anyway: `mach_ring` is the weak all-`try` normaliser, `mach_mpoly`
the complete one for identities needing cancellation.

> **The transferable finding, and it is a reading rule for the remaining four stops:
> ONE failure produced THREE errors.** `maxHeartbeats` is per-*declaration*, so `hidp` exhausting the
> 4M budget made `hidr` (line 159) and the theorem's own `whnf` (line 144) time out as collateral.
> Both pass untouched — `hidr` in **0.5s on the DEFAULT budget**. Isolating each into a scratch file
> took two minutes and turned a three-error module into a one-line fix. **Attribute the first failure
> in a declaration before believing anything reported after it**, or the eighteen-version haystack
> gets padded with phantoms.

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
