# Gate 14 (machsig-trust) — repair status and the steps that remain

The owner's ruling of 2026-10-13: *repair the gate before STOP 2; do not automatically accept the new
baseline.* Seven steps. This file says which are done on branch `machsig-gate`, where the evidence
is, and exactly what the remaining steps are. It is hand-written; every number in it is quoted from
a generated file named next to it.

| step | what | state |
|---|---|---|
| 1 | gate refuses missing, stale, untracked baselines/signatures | **done** — `trust_gate.py`, 18 end-to-end faults + 11 mutants |
| 2 | regenerate signatures from an identified revision | **done** — `regen.py` at 066bb75f (Lean sources = c3046961) |
| 3 | deterministic old-vs-new transition report | **done** — `TRANSITION_2026-10-13.md` + `.json`, byte-identical on rerun |
| 4 | classify by type and trust implication | **done** — same report, sections 2-6 |
| 5 | independent review of removals, restatements, assumption changes | **open** — `REVIEW_PACKET_2026-10-13.md` |
| 6 | reproducible classification + targeted checks of the large groups | machinery **done** (mechanism, `targeted_check.py`); sign-off **open** |
| 7 | commit the reviewed baseline, enable the gate in CI | **open** — candidate + proposed workflow below |

## What the gate does now

`tools/machsig/trust_gate.py` refuses (exit 3, one tagged line per reason) before it compares
anything: a signature set with no provenance record, one whose recorded source bytes or extractor
differ from the live tree, a truncated or edited set, a baseline that is untracked, locally modified,
without provenance, naming a commit the repository lacks, self-contradicting, derived with another
extractor, or never reviewed. Missing inputs are UNAVAILABLE (exit 2). An axiom entering an unchanged
statement's footprint is FAIL (exit 1) — compared as SETS, so a swap (one out, one in) is caught,
which the count rule could not do. Proof of each red path: `--selftest` (Part A on the real set,
Part B in a throwaway git repository); proof that the selftest notices a broken gate: `--mutate`.

`tools/check_all.sh` now runs `machsig-extract` (regen.py), `machsig-trust-selftest`,
`machsig-trust-mutate` and `machsig-trust` on separate lines.

**On this branch the gate refuses `[baseline-provenance-absent]`.** The committed baseline is still
the pre-repair counts-only file, which records no provenance. That is the true state and stays so
until step 7.

## Findings (from `TRANSITION_2026-10-13.md`)

* The 2026-09-03 baseline is **reconstructed byte-identically** (cold build of 23e0d047 + its own
  extractor). The stale local set the gate read for forty days equals a fresh 23e0d047 extraction.
* **0 extractor-caused changes** at either revision; all 4,317 are source changes.
* grew 1,816 / shrank 1,642 / **swap 375** (invisible to the old gate) / restated 2 / new 480 / removed 2.
* No sorryAx, compiler-trust or undeclared axiom moved; no conditional axiom entered any footprint; no
  axiom created since 2026-09-03 entered an existing theorem; 119 theorems went conditional→approved,
  none the other way.
* 39 axioms were discharged on 2026-10-04 (5841ea60, 2d2f59c0, e25e0cd1). That explains 3,761 of the
  3,835 grew/shrank/swap/restated changes mechanically. The other 74 are listed in full in the packet
  (C1, plus one restatement in B). The 10 growths among them all sit in `OperatorBasisGeneral.lean`,
  whose only commits in the window are 203cc854 (derived tangent line) and 9802f19e (clamp): the axiom
  `one_add_le_exp` left and `HasDerivAt_*` / `rolle_ct` entered, as that file's own comment at line 119
  says it should. Six of the ten are the entries c3046961 accepted by hand against the stale set.
* Targeted checks: 168/168 sampled theorems (seed 20261013, 10 per class, every class, all 74
  unexplained) reproduce through `#print axioms`; full sweep 7,470/7,470 and 7,948/7,948.

## Step 5 — the review (not done by the agent that built this)

Read `REVIEW_PACKET_2026-10-13.md` (sections A-F) and fill in its sign-off table. The packet's
primer is written for someone who has never seen MachLib. Things that deserve a person's eyes first:

* **B. Restatements.** `clamp_le_hi` GAINED the hypothesis `lo ≤ hi` (a weaker statement) and
  `lo_le_clamp` LOST it (stronger); both from 9802f19e "clamp is max lo (min x hi)". Intended?
* **A. Removals.** `MachLib.div_one_eq` moved to `MachLib.Real.div_one_eq` (same statement digest,
  e7b91de7); `MachLib.Real.mul_succ_eq` was deleted in 5841ea60 with no successor.
* **C1.** The 10 growths and 64 other unexplained changes.

## Step 6 — reproduce the classification

```
python3 tools/machsig/collect_evidence.py --evidence EV --old-root OLD/foundations \
    --new-root NEW/foundations --old-rev 23e0d047 --new-rev c3046961
python3 tools/machsig/targeted_check.py --evidence EV --old-root OLD/foundations \
    --new-root NEW/foundations --seed 20261013 --per-class 10 --full
python3 tools/machsig/transition.py --evidence EV --out-md T.md --out-json T.json --packet P.md
```

`TRANSITION_2026-10-13.md` section 9 lists how each evidence file is produced, and the sha256 of each.
The small ones are in `evidence-2026-10-13/`; the signature sets (~11 MB each) are regenerated with
`regen.py` (their record digest, `records_sha256`, is the cross-platform comparator: the header's
`lean_version` names the machine).

## Step 7 — commit the reviewed baseline and enable CI (after step 5 signs off)

1. On a tree whose Lean sources still equal the candidate's (`content_digest` in its provenance),
   copy `docs/machsig/trust_baseline.candidate-2026-10-13.json` to `tools/machsig/trust_baseline.json`.
   If the sources moved, do not reuse the candidate: run `regen.py`, `trust_gate.py --update`, and a
   new transition report against this one.
2. Set its `review` record by hand: `{"status": "REVIEWED", "reviewer": "<name>",
   "transition_report": "docs/machsig/TRANSITION_2026-10-13.md"}` (plus a date if wanted).
3. `python3 tools/machsig/trust_gate.py` must print `MACHSIG-TRUST OK`. Commit.
4. Move `docs/machsig/PROPOSED_CI_machsig-trust.yml` to `.github/workflows/machsig-trust.yml` in the
   same commit. Estimated 30-40 min per run (12.6 min cold build + extract.lean, which dominates).
5. Do not squash-merge `machsig-gate`: the candidate's provenance names 066bb75f, and the gate refuses
   a baseline whose provenance commit the repository does not contain.

## Not done here, for the owner to decide

* **Population.** The gate does not watch the 301 `Certcom.*` theorems (no axiom extraction in
  `extract.lean`'s scope) nor ~70 hand-written `MachLib.*` theorems that `extract_statement.lean`'s
  substring filter mistakes for generated ones (`.rec`→`recip_*`, `.inj`→`injective_*`, `.below`,
  `.eq_`, `proof_`). Fixing it is an extractor change and so its own reviewed transition.
* **Cost.** `extract.lean` takes 8.5-10.7 min locally; `#print axioms` over every watched theorem takes
  seconds. Making it cheap is another extractor change.
