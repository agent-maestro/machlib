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
| 7 | commit the reviewed baseline, enable the gate in CI | **open** — waits for the owner's rulings on E1-E3, the choice of candidate, and (widened only) a review of the second packet |

## Two candidates — the owner picks

| | narrow | widened |
|---|---|---|
| file | `trust_baseline.candidate-narrow-2026-10-13.json` | `trust_baseline.candidate-widened-2026-10-13.json` |
| population | `MachLib.*` theorems passing the old name filter: 7,948 | every theorem MachLib declares, the theorem ledger's rule: 9,431 (adds 1,497, drops 14 generated `congr_simp`) |
| derived from | 8e836a56 (hardening) | 30fcd3aa (widening) |
| transition | `TRANSITION_2026-10-13.md` | `TRANSITION_WIDENED_2026-10-13.md` |
| review packet | `REVIEW_PACKET_2026-10-13.md` (reviewed: ACCEPT EXCEPT E1-E3) | that one, plus `REVIEW_PACKET_WIDENING_2026-10-13.md` (only what the widening adds; NOT yet reviewed) |
| lands with | the hardening commits (through cab7a801; f5b45a37 is a cosmetic report fix that cherry-picks alone) | the hardening AND the widening commits (30fcd3aa onward) |

The widened candidate holds the narrow one's 7,934 shared theorems byte-identically (`ax`, `d`, `c`,
`set`), the same 232 axiom pins and the same policy. What it adds: 301 `Certcom.*`, 1,092 private, 65
filter-dropped and 39 root-namespace theorems; 18 of the 1,497 are conditional, none unchecked; 35
axioms are used ONLY by them (all 16 restated in the window and all 13 added since 2026-09-03).

The narrow candidate's axiom sets are byte-identical to the candidate the independent review accepted
(the `axiom_sets` table and every theorem's `ax`/`d`/`set` are equal); v0.4 only adds per-theorem
definition-closure digests, axiom statement pins, the declared policy, and the binding fields.

## Trust model — what this gate is and is not

**It catches** honest mistakes and unreviewed drift: a footprint that grows past the committed
baseline, a statement or a definition that changes, a theorem that disappears, an axiom restated or
promoted, sorry or an undeclared axiom anywhere, a stale or foreign signature set, a toolchain or
runner change, a review chain broken by a revert or a merge, and a stamp whose report's machine rows
are not the NET transition from the last COUNTED reviewed baseline at the anchor (CI: the change's
base commit; locally: the merge-base with the main line). A footprint that grows inside one change
therefore shows as `grew` in the report its stamp cites, however many stamped commits the change is
split into, and however it reaches master -- pull request, merge, fast-forward or direct push -- on
every run, not only the first (B62-B66, B71-B72, B74, B79, B81, B86-B87).

**What counts as a reviewed baseline (review 5).** On the anchor's first-parent line, a stamp makes a
reviewed baseline only when it arrives in a MERGE commit (the merge's own tree brings the file: it
differs from the first parent's), or is the step-7 landing (the only reviewed baseline before it is
the pre-review origin). A stamp on a plain commit never does. A single-stamp fast-forward still
passes, on its push run and on every later run, because HEAD's stamp is judged NET from the last
counted baseline (B76-B77); a multi-stamp one stays refused until it is re-stamped net (B72, B74,
B75). Why plain stamps cannot count, even one at a time: two stamped commits pushed together and the
same two commits pushed one after the other are the same objects in git, so no later run can tell a
reviewed sequence from the two-hop (B79).

**What that costs.** Between merge commits, reports accumulate: every baseline change after a
fast-forward reports net from the last counted baseline, not from the previous fast-forward (B78).
For the same reason a plain stamp is never locked in: a later change may return the baseline to the
last counted one as a net-zero step (B82). A merge commit locks a reviewed baseline in (B80); merge
pull requests with merge commits.

**What it does not catch.** It judges each change, not the history of a theorem. (a) A theorem
removed in one reviewed change and re-added grown in a LATER one shows as `removed`, then as `new`
with its whole footprint (B69). The gate now prints `MACHSIG-TRUST NOTE [readded]` with the
footprint the last reviewed baseline holding that name gave it (B85). Since the boundary between
changes is a merge commit, and anyone can make one, "a later change" includes a merge followed by one
fast-forwarded stamp, pushed together. (b) The gate binds content, not people: see the stamp below.

**A weak anchor is ADVISORY (review 5).** A local run with no main-line ref (`origin/master`,
`master`, `origin/main`, `main`) falls back to HEAD; a main ref still before the first reviewed
baseline judges against the origin. Either way the gate prints `MACHSIG-TRUST ADVISORY
[anchor-none]` or `[anchor-before-landing]` under its verdict (B83, B84), and `check_all.sh` lists a
run that prints any ADVISORY as UNAVAILABLE, never green.

**It stops a change from judging itself with an edited gate**: in CI the base commit's gate judges,
run as `python3 -I -S` from a checkout outside the tree under test, importing nothing from it, on a
fresh runner that never builds or executes the tree (the proposed two-job workflow).

**It is NOT a boundary against a hostile committer.** The signature set is produced by building the
change, and building MachLib runs the change's own code — `lakefile.lean`, every module (Lean
elaboration performs arbitrary IO), the extractor, the toolchain `lean-toolchain` names. A change
can therefore forge its own signature set, and no gate that consumes that set can tell. The boundary
against deliberate tampering is **required human review** of every change to the paths in
`.github/CODEOWNERS` (the gate, its extractor, the policy files, the toolchain pin, the build
configuration, the runner, the workflow), made required by branch protection. That is a repository
setting and the owner's decision; nothing on this branch changes it.

A stamp is likewise content-bound, not authenticated: anyone with commit access can write one and
generate a matching report. What the gate guarantees is that a stamp cannot be reused or borrowed
(it names this baseline's own digest), cannot be forgotten (a later commit that changes the baseline
loses it), and that the report it cites has machine rows equal to the net transition from the last
counted reviewed baseline at the anchor: everything since the last merge commit (or the landing) that
brought a reviewed baseline onto the main line. And by design it checks only the machine block (`gate_transition`) of a report: the human-readable rows
and prose of a report could disagree with it, so a reviewer must read what the gate binds (the third
review's row 4).

**Decision (reviews 4 and 5): stamps inside a change do not count.** Only a merge commit on the
anchor's first-parent line (or the landing) whose stamp starts at the last counted baseline makes a
reviewed baseline. A branch's commits are never judged as steps, nor are plain commits on the main
line; the merge commit that brings the file onto the line is, and the stamp it carries must start
at the main line's last counted baseline. So stamps cannot chain, inside a branch or on master, and
a change is one reviewed step whose report describes everything since its base. Stamping
intermediate commits is harmless but useless: only the stamp the change ends with is judged.

## What the gate does now (MachSig v0.4)

**Refuses (exit 3), one tagged line per reason, before comparing anything:** a signature set with no
provenance, a truncated/edited/duplicated one, one extracted from other Lean sources, another
extractor or another declared policy, one from another run when `MACHSIG_RUN_ID` is set; a baseline
that is untracked, modified, without provenance, naming a commit the repository lacks,
self-contradicting, from another extractor, or not REVIEWED; a REVIEWED stamp not bound to this
baseline's content [review-unbound]; a stamp whose report is not a committed machsig-transition JSON
with `binding` and `gate_transition` [review-report-invalid]; a report that does not start at the
reviewed baseline as of the anchor, or binds a baseline to itself [review-report-mismatch]; a report
whose `gate_transition` differs from the transition the gate recomputes between the two baselines
[review-report-rows]; an `--anchor` that is not an ancestor of HEAD [anchor-unreachable]; a clone too
shallow to reach the pre-review origin. Missing inputs: exit 2.

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
and the report it cites must describe exactly the transition from the reviewed baseline as of the
anchor to this one. The gate finds that baseline by walking the file's git history forward from the
pre-review origin (c3046961's counts-only baseline, `ORIGIN_CONTENT`) to the anchor, advancing only
past versions that a merge commit on the anchor's first-parent line (or the landing) brings and
whose own stamp passes every check; it recomputes
the transition from the two baselines' content and requires the report's `gate_transition` to equal
it row for row. That stops reusing, borrowing or forgetting a stamp, and splitting a change into
stamped hops. It cannot
authenticate a person: anyone with commit access can write a stamp and generate a matching report.
That a review happened remains a process recorded in git — who committed the stamp, and the packet's
sign-off table.

**Standalone runs are advisory.** A signature set's identity is self-declared, so a stale set given
a fresh header passes (the review's attack 2). `tools/check_all.sh` and the proposed CI job therefore
regenerate the set in the same run and export `MACHSIG_RUN_ID`; `regen.py` records it and the gate
refuses a set with another run's id. Run by hand without it, the gate prints
`MACHSIG-TRUST ADVISORY` under its verdict.

**Proof of the red paths:** `--selftest` (Part A: 8 injections + 4 controls on the real set; Part B:
70 faults + 19 controls end to end in throwaway git repositories, including every attack of the five
reviews that passed) and `--mutate` (49 mutant gates, each must be killed). Both run in check_all.sh.

**The gate's own code is pinned in CI (H2, reviews 2 and 3).** The proposed workflow has an
untrusted `extract` job (build + regen.py, uploads only the signature set) and a `judge` job on a
fresh runner that runs the BASE commit's gate isolated against the tree (data only), with
`--anchor <base>`; when the change touches the gate's files, its own versions must also pass their
own tests in the extract job. `.github/CODEOWNERS` requests the owner's review for `foundations/tools/machsig/**`,
AxiomLedger.lean, sorry_audit.lean and the workflow; making that review REQUIRED is a repository
setting, left to the owner.

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
| H1 (review 2): `--update`, then a stamp with a 4-line "this → itself" report | reference = last REVIEWED baseline (history walk from the origin); report rows recomputed and compared | B42-B47, controls B48-B49 |
| H2 (review 2): the gate's own code is not pinned | CI runs the base commit's gate against the tree; CODEOWNERS | simulated: a PR weakening `trust_gate.py` passes its own gate and FAILS under the pinned one |
| review 3, RESTART: revert to the counts-only origin, rebaseline from it | the chain starts at ONE commit (c3046961); a reappearance of the origin or of an older reviewed baseline is an unreviewed version | B50, B51; real data: refused |
| review 3, MERGE: a pre-review branch merged, its file kept | the chain is computed over the whole commit graph; a version must be valid against every reviewed line it joins; CI also anchors on the base commit | B52, B53, B55, control B54, B56; real data: refused |
| review 3, json.py takes over the pinned judge | judge job on a fresh runner, `python3 -I -S` outside the tree, base code only; the selftest no longer imports the tree's sig.py | B60 (isolated judge FAILS), B61 (in-tree: the attack is real); CI simulation with the workflow's judge steps verbatim: FAIL |
| review 3, toolchain and runner not checked | `[toolchain-mismatch]` (version and commit, not platform), `[runner-changed]` (capped_lean.sh vs the baseline's provenance commit) | B57, B58, B59 |
| review 5, limit (b): a two-hop fast-forwarded onto master is red on its push run only; every later run is OK | on the main line only a merge commit that brings a new version, or the step-7 landing, makes a reviewed baseline; a plain commit's stamp never does | B72, B74 (later local run, later push: refused), B79, B81, B86, B87, B88 (H1 through merge commits); controls B75-B78, B80; cost pinned: B82 |
| review 5, weak local anchor prints a clean OK | `MACHSIG-TRUST ADVISORY [anchor-none]` / `[anchor-before-landing]`; check_all.sh counts any ADVISORY as UNAVAILABLE | B83, B84; check_all `--selftest` canary |
| review 5, limit (a) (optional) | `MACHSIG-TRUST NOTE [readded]`: the re-added name's last reviewed footprint | B85 |
| review 4, QUIET TWO-HOP: drop a theorem in one stamped commit, re-add it grown in the next, each report exact for its own hop | the stamp must cite a report from the reviewed baseline AT THE ANCHOR with the NET rows; locally the anchor defaults to the merge-base with the main line; stamps off the anchor's first-parent line never count; superseded references pruned | B62-B66 (removal, empty baseline, three hops, `--anchor`, merged without CI), B71 (fast-forward, CI push run); controls B67-B70, B73 (origin reached through a merge's second parent); B72 pinned the fast-forward limit, closed in review 5 |

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
2. Fill its `review` block (the cited report's `binding.old` is the last reviewed baseline -- for the
   first review, the pre-review origin -- and its `gate_transition` must match the gate's recompute;
   transition.py writes both): `status` REVIEWED, `reviewer`, `transition_report` = the committed
   transition JSON (`docs/machsig/transition_2026-10-13.json` for the narrow candidate,
   `docs/machsig/transition_widened_2026-10-13.json` for the widened one),
   and `baseline_sha256` = `python3 tools/machsig/trust_gate.py --content-digest`. The report's
   `binding.old_baseline_sha256` is c3046961's committed baseline, which is what the file replaces.
3. `MACHSIG_RUN_ID=x python3 tools/machsig/regen.py && MACHSIG_RUN_ID=x python3 tools/machsig/trust_gate.py`
   must print `MACHSIG-TRUST OK`. Commit. Until the landing is on master, a local run also prints
   `ADVISORY [anchor-before-landing]` (check_all.sh: UNAVAILABLE): expected for this one change, the
   only one judged against the pre-review origin.
4. Move `docs/machsig/PROPOSED_CI_machsig-trust.yml` to `.github/workflows/machsig-trust.yml` in the
   same commit (~30-40 min per run; extract.lean dominates).
5. Do not squash-merge `machsig-gate`: the candidate's provenance commit must stay reachable. The
   landing counts as a reviewed baseline whether it arrives as a plain commit or in a merge commit;
   every later change locks a reviewed baseline in only through a merge commit (review 5).

## Not done here

* `extract.lean` still takes 8.5-10.7 min; `#print axioms` over every watched theorem takes ~10 s.
  Making it cheap changes the extractor and so needs its own reviewed transition.
* The REVIEWED stamp binds content; it cannot authenticate a reviewer (see above).

## Reproduce

See section 9 of each transition report. In short: cold-build 23e0d047 in its own worktree, copy this
branch's extractor files into it, run `regen.py` in both trees, then `collect_evidence.py`,
`targeted_check.py --full` and `transition.py`. The small evidence files are in
`evidence-2026-10-13/`; the signature sets (~11 MB each) are regenerated, and their `records_sha256`
is the cross-machine comparator.
