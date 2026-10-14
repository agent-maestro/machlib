# Gate 14 (machsig-trust) — repair status and the steps that remain

The owner's ruling of 2026-10-13: *repair the gate before STOP 2; do not automatically accept the new
baseline.* Seven steps. This file says which are done on branch `machsig-gate`, where the evidence
is, and exactly what the remaining steps are. It is hand-written; every number in it is quoted from
a generated file named next to it.

| step | what | state |
|---|---|---|
| 1 | gate refuses missing, stale, untracked baselines/signatures | **done**, then hardened after the independent review (below) |
| 2 | regenerate signatures from an identified revision | **done** — `regen.py`, MachSig v0.4, Lean sources = c3046961 |
| 3 | deterministic old-vs-new transition report | **done** — `TRANSITION_2026-10-13.md` + `.json` (version 2), byte-identical on rerun |
| 4 | classify by type and trust implication | **done** — same report |
| 5 | independent review of removals, restatements, assumption changes | **done for the narrow candidate**: ACCEPT EXCEPT E1/E2/E3, which go to the owner (`scratchpad/MACHSIG_INDEPENDENT_REVIEW_2026-10-13.md`) |
| 6 | reproducible classification + targeted checks of the large groups | **done**: 200/200 sampled (seed 20261013), full `#print axioms` sweep; the reviewer's own seed-777 sample 98/98 |
| 7 | commit the reviewed baseline, enable the gate in CI | **open** — waits for the owner's rulings on E1-E3 |

## The candidate

`trust_baseline.candidate-narrow-2026-10-13.json`: the population the gate watched until v0.4
(`MachLib.*` theorems passing the old name filter, 7,948), transition `TRANSITION_2026-10-13.md`,
packet `REVIEW_PACKET_2026-10-13.md` (reviewed). A widened candidate, watching every theorem MachLib
declares, follows in SEPARATE commits on this branch so the owner can land the hardening without it.

The narrow candidate's axiom sets are byte-identical to the candidate the independent review accepted
(the `axiom_sets` table and every theorem's `ax`/`d`/`set` are equal); v0.4 only adds per-theorem
definition-closure digests, axiom statement pins, the declared policy, and the binding fields.

## What the gate does now (MachSig v0.4)

**Refuses (exit 3), one tagged line per reason, before comparing anything:** a signature set with no
provenance, a truncated/edited/duplicated one, one extracted from other Lean sources, another
extractor or another declared policy, one from another run when `MACHSIG_RUN_ID` is set; a baseline
that is untracked, modified, without provenance, naming a commit the repository lacks,
self-contradicting, from another extractor, or not REVIEWED; a REVIEWED stamp not bound to this
baseline's content [review-unbound]; a stamp whose report is not a committed machsig-transition JSON
[review-report-invalid]; a report whose binding is not (previous committed baseline → this one)
[review-report-mismatch]; a clone too shallow to read the previous baseline. Missing inputs: exit 2.

**FAILS (exit 1):** an axiom enters an unchanged statement's footprint (sets, so swaps too); a
statement changes; a definition under an unchanged statement changes (`redefined`); a watched theorem
leaves the set; sorryAx outside the allowlist, a compiler-trust axiom or an undeclared axiom in ANY
watched theorem, however old (`policy-violation`); an axiom restated under its name; trustedFootprint
or the sorry allowlist grows (`policy-widened`).

**On this branch the gate refuses `[baseline-provenance-absent]`**: the committed baseline is still
the pre-repair counts-only file. That is the true state until step 7, and check_all.sh says so.

**Friction, by design (the owner can relax it):** deleting, renaming, restating or redefining a
watched theorem, or promoting an axiom, now needs a reviewed rebaseline. The default is closed.

**What the stamp is and is not.** The gate binds CONTENT: the stamp names the baseline's own digest,
and the report it cites must describe exactly the transition from the previous committed baseline
(read from git) to this one. That stops reusing, borrowing or forgetting a stamp. It cannot
authenticate a person: anyone with commit access can write a stamp and generate a matching report.
That a review happened remains a process recorded in git — who committed the stamp, and the packet's
sign-off table.

**Standalone runs are advisory.** A signature set's identity is self-declared, so a stale set given
a fresh header passes (the review's attack 2). `tools/check_all.sh` and the proposed CI job therefore
regenerate the set in the same run and export `MACHSIG_RUN_ID`; `regen.py` records it and the gate
refuses a set with another run's id. Run by hand without it, the gate prints
`MACHSIG-TRUST ADVISORY` under its verdict.

**Proof of the red paths:** `--selftest` (Part A: 8 injections + 4 controls on the real set; Part B:
41 faults + 1 control end to end in throwaway git repositories, including every attack of the
review that passed) and `--mutate` (28 mutant gates, each must be killed). Both run in check_all.sh.

## Hardening after the independent review (2026-10-13)

| review item | fix | regression test |
|---|---|---|
| attack 3: `--update`, paste the old stamp | stamp carries `baseline_sha256`; gate recomputes | B23 |
| attack 4: reviewer "x", lakefile.lean as report | report must be a committed machsig-transition JSON bound to (previous → this) | B24-B27 |
| attack 5: restatement launders sorryAx | restatement FAILS whatever its axioms | B28, B29, Part A |
| attack 6: theorem leaves the watched set | removal FAILS | B30, Part A |
| axiom statements not pinned (16 restated) | `AxiomStatementDigest` per axiom; `axiom-restated` | B36, Part A |
| E3: definition changes invisible | `DefClosureDigest`; `redefined` | B37, Part A |
| sorryAx / outside the policy in any theorem | `policy-violation`, judged against the declared policy | B33-B35, Part A |
| E1/E2: promotions invisible (not a listed item) | policy pinned; `policy-widened` | B38, B39, Part A |
| attack 2: relabelled stale set | `MACHSIG_RUN_ID` binding in check_all/CI; ADVISORY standalone | B40, B41, B0 |
| doc error (below) | corrected | — |

**Correction.** Version 1 of this file said all ten growths of 203cc854 sit in
`OperatorBasisGeneral.lean`. Six do (`aerr_exp`, `aerr_exp_upper`, `aexpr_fwd_error`, `aexpr_sound`,
`cos_sq_mixed_via_meta`, `exp_sq_via_meta`); four (`aerr_ln`, `aerr_pow`, `ln_step`,
`ln_lipschitz_bound`) are in `OperatorBasisComplete.lean`. All ten
come from 203cc854, as the review verified. The data in the packet was right; the prose was not.

## For the owner (from the review)

* **E1** `MachLib.Real.pi_lower_bound` joined trustedFootprint in 5841ea60, the commit that started
  using it; it entered 181 existing footprints. The report now classes these `assumption-promoted`.
* **E2** `realPow`, `realPow_nonneg` joined trustedFootprint in e25e0cd1.
* **E3** `clamp`'s definition changed in 9802f19e. The report's packet section G lists every theorem
  whose statement reaches it (33 by the gate's edge rule; the review counted 32 with its own walk),
  and every other definition that changed under unchanged statements (natCast becoming a definition
  reaches 845 watched theorems).

## Step 7 — after the owner rules and picks a candidate

1. On a tree whose Lean sources and policy still equal the candidate's (`content_digest` in its
   provenance), copy the chosen candidate to `tools/machsig/trust_baseline.json`. If anything moved,
   do not reuse it: `regen.py`, `trust_gate.py --update`, and a new transition report.
2. Fill its `review` block: `status` REVIEWED, `reviewer`, `transition_report` = the committed
   transition JSON (`docs/machsig/transition_2026-10-13.json`),
   and `baseline_sha256` = `python3 tools/machsig/trust_gate.py --content-digest`. The report's
   `binding.old_baseline_sha256` is c3046961's committed baseline, which is what the file replaces.
3. `MACHSIG_RUN_ID=x python3 tools/machsig/regen.py && MACHSIG_RUN_ID=x python3 tools/machsig/trust_gate.py`
   must print `MACHSIG-TRUST OK`. Commit.
4. Move `docs/machsig/PROPOSED_CI_machsig-trust.yml` to `.github/workflows/machsig-trust.yml` in the
   same commit (~30-40 min per run; extract.lean dominates).
5. Do not squash-merge `machsig-gate`: the candidate's provenance commit must stay reachable.

## Reproduce

See section 9 of each transition report. In short: cold-build 23e0d047 in its own worktree, copy this
branch's extractor files into it, run `regen.py` in both trees, then `collect_evidence.py`,
`targeted_check.py --full` and `transition.py`. The small evidence files are in
`evidence-2026-10-13/`; the signature sets (~11 MB each) are regenerated, and their `records_sha256`
is the cross-machine comparator.
