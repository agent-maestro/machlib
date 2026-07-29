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

## Stop 1 — `v4.16.0`

*(in progress — entry completed when the stop is accepted or halted)*
