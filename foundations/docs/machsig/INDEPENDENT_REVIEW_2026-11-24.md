# Independent review: branch `derive-sqrt-exp-u` (gate-14 rebaseline), 2026-11-24

Scope: `97d4c6d8` (six axioms become theorems), `92351128` (54 claims and 38 figures re-pinned), `e8e26ae4`
(UNREVIEWED baseline, transition script/report, statement probe), on top of master `fcc4ae1b`. The branch is not
pushed (`git ls-remote origin refs/heads/derive-sqrt-exp-u` is empty), so CI has never run on it. **GitHub master
moved during this review**: PR #15 merged at 23:57Z, and `origin/master` is now `ea94aab8`. The local clone's
`origin/master` still says `fcc4ae1b`, and local `master` is `f5f86076`, which is older still. See Q7.

I took no commit message at its word. Each claim below is labelled **[checked]** (I produced the evidence) or
**[read-only]** (I read it and did not reproduce it). Every Lean run went through
`systemd-run --user --scope -p MemoryMax=16G -p MemorySwapMax=0 lake env lean`, from `foundations/`, against the
branch's existing `.olean`s (sources older than oleans for the four changed modules; `git status` clean). Peak RSS
was 1.6 GB. I ran no `lake build` and no `check_all.sh`. Nothing in the branch worktree, forge or monogate-lean was
modified: `git status` is clean in all three afterwards, and the main repo's refs are unchanged. All gate
simulations ran in a `--shared` scratch clone, which I deleted afterwards because it held a simulated REVIEWED
stamp. Each "pass" below sits beside a negative control that shows the instrument can fail.

| Q | verdict |
|---|---|
| 1 Statements identical | **HOLDS**, binders included [checked] |
| 2 Proofs genuine, trusted-only | **HOLDS** [checked] |
| 3 AxiomLedger | **HOLDS** [checked] |
| 4 Transition report | **HOLDS**; **F3** (C6 weakened more than this data needed) [checked] |
| 5 The 54 re-pinned claims | **HOLDS** for the 54; **F2** (five OTHER claims' sqrt firewall went vacuous) [checked] |
| 6 Downstream | **F1** (Forge CI breaks), **F6** (the full after-merge list) [checked] |
| 7 Merge mechanics | **HOLDS** against the new master `ea94aab8` [checked]; **F7** |

Recommendation: **accept with changes.** The MachLib change and its rebaseline are correct. F1 is a release
blocker for Forge, not a defect in MachLib, and it is not in any of the branch's after-merge notes. F2 should be
fixed on the branch before the stamp; it touches only `claims.json`, so it does not invalidate the stamp.

---

## 1. Statements — HOLDS [checked]

**Method.** `probe_branch.lean` is my own probe. Its `serExpr`/`serLevel` are copied by line range (68-95) straight
from `tools/machsig/extract_trust.lean`, not from the branch's probe. It prints kind, module, level params, `SER`
(the gate's serialization), `FULL` and the `collectAxioms` footprint. My `FULL` keeps binder names and binder info at
every binder, plus mdata size.

| name | branch kind / module | sha256(SER) = master's axiom pin |
|---|---|---|
| `sqrt_zero` | theorem / `MachLib.Trig` | `7a9f7d16…` yes |
| `sqrt_neg_zero` | theorem / `MachLib.Trig` | `9568af33…` yes |
| `u_lt_one` | theorem / `MachLib.FPModel` | `a1958c2b…` yes |
| `u_le_half` | theorem / `MachLib.FPModel` | `7ff9c983…` yes |
| `exp_exp_minus_exp_strictly_increasing` | theorem / `MachLib.ExpExpNotInEML1` | `28881806…` yes |
| `exp_one_lt_three` | theorem / `MachLib.IteratedExpBounds` | `527614d4…` yes |

Full 64-hex digests compared (`q1_compare.txt`); level params `[]` on both sides; same defining modules as on master.

**Binders, against master's actual axioms.** The baseline pins drop binder names, so I rebuilt master's axiom
types. For each of the four modules I elaborated master's own source text (`git show fcc4ae1b:…`), truncated after
the axiom, against the branch's oleans for its imports. Those imports are byte-identical between master and the
branch: the only `.lean` files the branch changes are the reviewed set.
- Fidelity control: each reconstruction's `SER` reproduces master's pin. That holds for all six, plus `sqrt_nonneg`,
  `u_nonneg` and `u_le_inv_two_pow_52`.
- Result: the branch's `FULL` equals master's `FULL` for all six, byte for byte (`q1_full_compare.txt`). That
  includes `sqrt_neg_zero`'s `x:d` and the anonymous arrow binder `a._@._internal._hyg.0:d`, and
  `exp_exp_minus_exp…`'s `x:d`, `y:d` and arrow binder. **No binder changed, so named-argument call sites are
  unaffected.**
- `ExpExpNotInEML1` now imports `MachLib.Ring`. The reconstruction ran WITHOUT that import, and the hashes still
  agree, so the import changed no elaboration of the statement.

**Controls.**
- My serializer reproduces the NEW baseline's pins for nine unchanged axioms: `sqrt_nonneg`,
  `u_le_inv_two_pow_52`, `exp_gt_one_plus_self`, `tanh_neg`, `u_nonneg`, `sqrt_le_of_le_sq`, `one_add_le_exp`, `u`,
  `sqrt_sq_nonneg`.
- Crossed pins give `False`: `sqrt_zero` against `sqrt_neg_zero`'s pin, and `u_lt_one` against `u_le_half`'s.
- Seven near-miss names are ABSENT, e.g. `MachLib.Real.Real.u_lt_one`, `MachLib.u_le_half`,
  `MachLib.Real.FPModel.u_lt_one`.
- No `attribute [...]`/`@[...]` names any of the six, on master or on the branch (`git grep`).

**The author's probe is reproducible.** I re-ran `statement_probe.lean` as committed, redirecting only its output
file. The TSV is byte-identical to the committed one, and its sha256 equals the report's `statement_probe_sha256`.

## 2. Proofs — HOLDS [checked]

**Footprints.** `collectAxioms` on the branch (`probe_branch.tsv`, `probe_branch_helpers.tsv`):

| theorem | axioms | outside the 154 trusted |
|---|---|---|
| `sqrt_zero`, `sqrt_neg_zero` | 17 each | none |
| `u_lt_one`, `u_le_half` | 28 each | none |
| `exp_exp_minus_exp_strictly_increasing` | 35 | none |
| `exp_one_lt_three` | 34 | none |

- The five private helpers are trusted-only too.
- None of the footprints contains `sorryAx`, a `_native` axiom, `ofReduceBool` or `trustCompiler`.
- The proofs are not circular: every dependency the probe reports is `axiom`-kind, including `u_le_inv_two_pow_52`,
  `sqrt_le_of_le_sq`, `sqrt_nonneg`, `one_add_le_exp` and `exp_gt_one_plus_self`.
- No axiom set in the new baseline names any of the six (0 of 2 003).

**Negative control** (`control_sorry.lean`). A planted `:= sorry` prints `sorryAx`, and a planted `native_decide`
prints `…_native.native_decide.ax_1_1`. `#print axioms u_lt_one` shows `u_le_inv_two_pow_52` and not itself.

**Diff scan** [checked]. Across all added `.lean` lines I found no `sorry`, `admit`, `native_decide`,
`implemented_by`, `extern`, `set_option`, `unsafe` or new `axiom`. The `partial def`s are in the evidence probe
under `docs/`, which is not built. Six `by decide` calls on small `Nat` facts (`0 < 2^52`, `1 < 2^52`,
`46656 < 46875`, …) leave no axiom, as the footprints show.

**Mathematics** [checked by reading; arithmetic recomputed].
- `sqrt_le_of_le_sq` at `z = 0` with `sqrt_nonneg`.
- `u ≤ 2⁻⁵² < 1`, and `u + u ≤ 2⁻⁵²·2 ≤ 2⁻⁵²·2⁵² = 1`.
- `exp(-1/6) ≥ 5/6`, so `15625·e ≤ 46656 < 46875 = 3·5⁶`.
- `exp(exp y) = exp(exp x)·exp d ≥ exp(exp x)(1+d) > exp(exp x)+d`.

## 3. AxiomLedger — HOLDS [checked]

`lake env lean AxiomLedger.lean` on the branch (`axiomledger_branch.out`, 5.8 s): `AxiomLedger OK: 202 axioms pinned;
112 headline footprints ⊆ trusted (154); 5 disclosed inert; 34 disclosed-trusted …; 162 Option D spine theorems …
(0 leaking); … 326 algebra-spine theorems … (0 leaking); 260 trust-list entries resolved …; 1 sub-theory
primitive(s) checked.`

**Lists, master's source against the branch's.** I parsed both with a string-aware parser; my first parser cut
lines at `--` inside string literals and missed `disclosedTrusted`, so I fixed it (`ledger_lists.py`,
`q3_ledger_lists.txt`).

| list | change | removed |
|---|---|---|
| `knownAxioms` | 208 -> 202 | exactly the six |
| `trustedFootprint` | 156 -> 154 | exactly `u_lt_one`, `u_le_half` |
| `disclosedTrusted` | 36 -> 34 | exactly `u_lt_one`, `u_le_half` |

Nothing entered any list. Every other list is identical, `headlines` (112), both spine module lists,
`subTheoryPrimitives` and `algebraFootprint` among them. The baselines agree:
- `policy.known` 208 -> 202 and `policy.trusted` 156 -> 154, same names, `allowed_sorry` unchanged;
- `axiom_statements` 223 -> 217: the six gone, none new, none restated.

**Headlines and spines.** 54 of the 112 headlines changed footprint, all through the `u` pair (`q3_headlines.txt`),
and every one stays inside trusted. The spine counts (162, 326) match the 2026-10-26 review's; no spine module is
among the touched files.

**Classification**, recomputed from the new baseline as an independent instrument: 9 534 theorems = 9 426 approved
+ 107 conditional + 1 unchecked. That matches README/CLAUDE.md. The 19 theorems that left "conditional" were blocked
only by the four untrusted converted axioms (`q3_classification.txt`).

**Mutation controls** (scratch copies of the ledger):

| mutant | result |
|---|---|
| `u_lt_one` back in `trustedFootprint` | FAIL, "names no live axiom … [u_lt_one]" |
| `sqrt_zero` back in `knownAxioms` | FAIL, "vanished axiom (rot)" |
| `Certcom.realToR` dropped from `knownAxioms` | FAIL, "UNKNOWN axiom … undisclosed" |

**Gate 13** (`soundness_witness_audit.analyze`). Fed the branch ledger and the live monogate-lean bridge, it gives
`fails=[]`. `u_lt_one` and `u_le_half` become `extra_witnesses`, which the audit treats as harmless, as it did
`tanh_neg`. Its own selftest gives `SELFTEST PASS`.

**AXIOM_MANIFEST.md.** I regenerated it in the scratch clone at `e8e26ae4`, with monogate-lean symlinked: it is
byte-identical to the committed file (154; float-bridge 32, mapped 14, standard 3, witnessed 105).

**Not run [read-only]:** `prose_counts_check.py` (it runs the theorem ledger, which runs `lake build`) and
`lake build` itself. The figures it guards were checked above by other instruments.

## 4. The transition report — HOLDS; FINDING F3 [checked]

**Reproduction.** I ran a scratch copy of the script that changes only the output paths and allows mutant inputs
(`transition_runner.py`). It printed `rows 184 {'grew': 92, 'shrank': 13, 'swap': 3, 'new': 76}; checks C1=ok …
C7=ok`. Both JSON and MD are **byte-identical** to the committed files (sha256 `db1ecb99…`, `dd64e652…`).

**Binding, computed with the gate's own functions.**
- `trust_gate.reviewed_chain` returns exactly one reference, `sha256:5b26c935…` ("the baseline reviewed at
  cc90d9b4"), at `fcc4ae1b`, at `f5f86076`, at `HEAD`, and at the new master `ea94aab8`. That is
  `binding.old_baseline_sha256`.
- `binding.new_baseline_sha256` = `--content-digest` of the committed baseline = `sha256:b0820dda…e06e1`.
- The baseline blob is `c4755920` at `a356363b`, `cc90d9b4`, `f5f86076`, `fcc4ae1b` and `ea94aab8`.

**OLD_REV.** `fcc4ae1b` was the right revision when the report was written: correct content, and every
master-added theorem exists there. It is now one commit behind GitHub master, but #15 touched no Lean and not the
baseline, so nothing it feeds changes. The gate does not read `OLD_REV`.

**End-to-end gate**, in the scratch clone with the check_all signature set (its sources digest matches):

| case | result |
|---|---|
| unstamped tip | `REFUSED [baseline-unreviewed]` (rc 3) |
| stamped (review block only; digest unchanged by stamping), default anchor and `--anchor fcc4ae1b` | `MACHSIG-TRUST OK` (9 534 compared; only the standalone `MACHSIG_RUN_ID` advisory) |
| `--no-ff` merge onto `fcc4ae1b` | OK; `reviewed_chain` at the merge = `b0820dda…` |
| unstamped `--no-ff` merge | REFUSED |
| stale-anchor variant (no `origin/master`, `master` = `f5f86076`) | OK, same reviewed baseline |

Negative controls, each committed on a throwaway commit:
- a dropped report row gives `[review-report-rows]`;
- an edited `entered` list gives `[review-report-rows]`;
- a wrong `baseline_sha256` gives `[review-unbound]`;
- an edited `binding.old` gives `[review-report-mismatch]`;
- editing only `checks` still passes. That is by design: C1-C7 are reviewer evidence, not gate input.

**C1-C7 can each fail** (`c_mutation_harness_v2.py`, `c_mutation_results_v2.txt`). Each mutant turns its own check
red, and the unmutated control passes:

| check | mutants that turn it red |
|---|---|
| C1 | a theorem restated; a theorem removed |
| C2 | an axiom pin restated; a new pin; `sqrt_zero` still an axiom |
| C3 | WAS_TRUSTED missing `u_lt_one`; untrusted `arcsin_zero` added to trusted; an extra trusted name removed; `u_lt_one` kept in trusted; `known` grows; `allowed_sorry` grows |
| C4 | a changed row also loses `exp_add`; an unrelated row loses `exp_add` |
| C5 | trusted-but-unbrought `Certcom.floatOfR` enters; untrusted `arcsin_zero` enters; an exp-proof axiom enters a `u_lt_one`-only row |
| C6 | a novel-name theorem; a helper dropped from HELPERS; a helper on `arcsin_zero`; one of the six on `arcsin_zero`; a colliding name on an UNDECLARED axiom; the template's trusted-only rule (fails on `oneQueryLevelSet_of_residue'`) |
| C7 | `sqrt_zero` SER altered; `u_lt_one` reported as an axiom; a control's SER altered; a near-miss name present; one of the six missing |

My first harness used `floor` as the "untrusted" axiom. That was a no-op: `floor` has been trusted since
2026-10-27, the same trap the 10-26 review recorded for C5. I replaced it with `arcsin_zero`. Do not reuse
`floor`.

**C3's change is sound.** `gate_transition` emits only `added`/`removed` per policy list
(`trust_gate.py:540-542`), so `trusted.added == [] and set(trusted.removed) == WAS_TRUSTED` is exactly as tight as
the template's `trusted == {added: [], removed: []}`. It pins `removed` to the two names instead of to empty.
Hard-coding WAS_TRUSTED is fine; computing it as `six ∩ old.policy.trusted` would be more robust.

### FINDING F3 (LOW-MEDIUM) — C6 was weakened more than this data needed, and a planted case slips through

The name-syntax fix is right. With `\b`, the template misses `theorem FxBox.has_intro` and
`oneQueryLevelSet_of_residue'`, as the commit says. Two other changes go further:
1. **`len(v) == 1` became `>= 1`.** With the new regex every one of the 65 master-added rows has exactly one hit, so
   `== 1` would still pass (`q4_c6_independent.txt`).
2. **Master-added rows may now rest on any DECLARED axiom**, needed for #13's `oneQueryLevelSet_of_residue'`.

Classification is still by SHORT name, with no namespace check. My adversarial mutant adds
`MachLib.ReviewEvil.sqrt_one` (a theorem THIS change could add) resting on untrusted `arcsin_zero`. It is classed as
"added on master", because `theorem sqrt_one` exists at `OLD_REV`, and **C6 holds**. The template's rule would have
failed it.

**Not exploited here** [checked independently]:
- The diff `fcc4ae1b..HEAD` adds exactly 11 theorem declarations: the six and the five helpers (`u_le_one` only
  moved).
- The 65 other new rows are exactly the 65 theorem declarations master added since the old baseline's source commit
  `7eb1b859`: FixedPointNet 30, FixedPointNetInterval 28, EMLOneQueryResidueRepair 7.

**For the next template:**
- classify master-added rows from `git diff <old provenance commit>..OLD_REV`;
- require the change's own added declarations (`git diff OLD_REV..new_sources_commit`) to be exactly the converted
  names plus HELPERS;
- restore `== 1`.

Also: the generated MD says the master-added rows each "rest on trusted axioms only", then lists
`oneQueryLevelSet_of_residue'` resting on `eml_tree_analytic_on_interval` 30 lines later (a stale template
sentence; see F4).

## 5. The 54 re-pinned claims — HOLDS; FINDING F2 [checked]

`claims.json`, master against the branch (`q5_claims.txt`):
- 579 claims each side, same ids, same order, `_comment` header unchanged.
- Exactly 54 claims differ, all in `foundations/docs/what_is_proven.md`, and in each one only `axioms_exact` changed.
- For every one: removed ⊆ {`u_lt_one`, `u_le_half`} and non-empty; added ⊆ the union of the two proofs'
  footprints; no `sorryAx`; the relative order of kept axioms unchanged.
- **Independent instrument:** each new list equals the theorem's footprint in the new baseline, and each old list
  equaled master's baseline footprint.
- No unchanged `axioms_exact` claim disagrees with the new baseline.

**Is re-pinning honest?** Yes. The 54 claims anchor on specimen and instantiation prose ("has a specimen at
`pidSpecimenEnv` …", "`pid_grounded_instantiated`"), and none of that depends on the two being axioms.
`what_is_proven.md:941-955` is dated history and gained a correct update sentence. The registry's own `_comment`s
are stale: 23 still call the two axioms, and `grounded-det-instantiated` ("Rests on real_fpfinite and u_lt_one") and
the PID ones ("on the literal, libm-finiteness and u_le_half axioms") now describe footprints that no longer exist
(F4).

### FINDING F2 (MEDIUM) — the sqrt-totalisation firewall is now vacuous, and no gate noticed

Five unchanged claims guard the Apollonius/Circle design with `forbid_axioms_exact: ["MachLib.Real.sqrt_neg_zero"]`:
`tangency-sqrt-free-changelog`, `apollonius-elimination-changelog`, `apollonius-root-identity-changelog`,
`apollonius-attainment-all-classes-changelog` and `apollonius-exactly-two-per-mode-changelog`. Their own
`_comment`s say this IS the content: "The sqrt-totalisation firewall. forbid_axioms_exact on sqrt_neg_zero is the
actual content". CHANGELOG.md:12879-12883, 13202 and 13267-13272, Circle.lean:5-15 and two Apollonius docstrings
make the same point.

**What changed.** `sqrt_neg_zero` is a theorem now, so it can never appear in a footprint, and the five guards can
never fire. A future proof that reaches the totalisation branch now shows `sqrt_le_of_le_sq` instead.
`claim_audit.py:632-635` tests `ax in names` and never checks that a forbidden name is still an axiom, so the audit
stays green. The commit message's "The sqrt and exp conversions touched no claim" is true of `axioms_exact` only.

**Fix, before the stamp** (claims.json only; it does not touch the baseline or the stamp digest):
- Add `MachLib.Real.sqrt_le_of_le_sq` to those five claims' `forbid_axioms_exact`. It is the only sqrt axiom that
  bounds `sqrt` from above (the sqrt axioms are `sqrt`, `sqrt_nonneg`, `sqrt_sq_nonneg`, `le_sqrt_of_sq_le`,
  `sqrt_le_of_le_sq`, `HasDerivAt_sqrt`, `Certcom.real_sqrt_rounds`).
- It is in the footprint of both derived theorems, and absent from all five guarded footprints today: those hold
  only `sqrt`, `sqrt_nonneg` and `sqrt_sq_nonneg`, or none.
- Update the five `_comment`s.
- Follow-up: a rot rule in the claim audit — a `forbid_axioms*` entry must name a live axiom — like AxiomLedger's
  "vanished axiom (rot)".

## 6. Downstream — FINDINGS F1, F6 [checked unless marked]

### FINDING F1 (HIGH) — Forge's blocking CI step fails 54/73 once the linked MachLib moves

**The mechanism.**
- `forge/reproduce/verify_grounding.py` requires `MachLib.Real.u_lt_one` and/or `u_le_half` to be PRESENT in the
  `#print axioms` of 54 of its 73 grounded certificates (`_RANGE`, `_EML`, three `pipeline_*` entries). Otherwise:
  "NOT grounded on the disclosed floor".
- Theorems never appear there.
- It runs as a **BLOCKING** step in `forge/.github/workflows/ci.yml:116-125`, "through the linked ../machlib".
- The Forge runner's `_work/forge/machlib` is a symlink to `/home/monogate/monogate/machlib`, the main checkout.

**Measured.** I computed the 73 footprints with my own probe; the script itself would write a temp file into the
MachLib tree. Then I applied Forge's own `check()` (`q6_forge_verify_grounding.txt`). The canary is rejected in both
runs.

| footprints from | certificates passing |
|---|---|
| main checkout (`f5f86076`) | 73/73 |
| branch | **19/73**: 51 missing both names, 3 missing `u_lt_one` |

**Not mentioned anywhere.** Neither commit message nor CLAUDE.md's "After merge" names Forge.

**The fix, tested.** Replacing `u_lt_one`/`u_le_half` with `MachLib.Real.u_le_inv_two_pow_52` in those need-sets:

| version | branch | current main checkout |
|---|---|---|
| plain replacement | 73/73 | 21/73 |
| transition-tolerant ("old pair OR `u_le_inv_two_pow_52`") | 73/73 | 73/73 |

So land the tolerant form first, tighten it after the main checkout moves, and update the CI step's comment.

**No other Forge effect.**
- `gen_lean_visible_names.py --check` against the branch: `up to date: 2738 names`.
- Admission (`axiom_policy.py`, 58 names) registers none of the six and not `u_le_inv_two_pow_52`. Every one of the
  six proofs rests on at least one unregistered axiom (`one_add_le_exp`, `sqrt_le_of_le_sq`,
  `u_le_inv_two_pow_52`, `u`), so no artifact newly passes or newly fails admission.
- No other Forge file names the six. `forge-mcp-pin` has its own copy of `verify_grounding.py` [read-only; not CI].

### F6 (INFO) — everything else after the merge, and the order

- **The main checkout is stale.** `/home/monogate/monogate/machlib` is at `f5f86076`, four merges behind GitHub (#8,
  #13, #14, #15). Both the Forge runner and monogate-lean (`require MachLib from "../machlib/foundations"`) build
  against it, so the downstream effects land when it is pulled and rebuilt, not at the merge.
- **monogate-lean.** `checkWitnessed` uses `env.find?`/`ci.type` and never asks for `axiomInfo`, so the witnesses
  for `u_lt_one`/`u_le_half` keep typechecking (same types, Q1). The bridge's log line will count them as
  "registered axioms verbatim-witnessed", which goes stale. Retire them (as 76835b9 did for `tanh_zero`). Gate 13
  passes either way.
- **monogate.org** (`monogate/blog/scripts/lean_claims.json`, machlib sources pinned at `89e6855b`). It registers no
  changed theorem and allows none of the six. But all eight `.lean` files this branch touches are byte-identical
  between `89e6855b` and master, so once the main checkout moves, `check_claims.py` will report IMPORT for every
  claim reaching them, until the pin moves to the merge commit.
- **monogate.dev** (`monogate-dev/scripts/lean_claims.json`, pinned at `9802f19e`). Already differs from master in
  Trig, FPModel, IteratedExpBounds and GroundedInstanceArith; pre-existing, not this change's. Its `site_figures.json`
  quotes no trust figures.
- **machlib.org.** `site/components/{Numbers,TrustBase,CheckIt}.tsx` changed and the deploy is manual (said in
  92351128's message only, not in CLAUDE.md).
- **Order:**
  1. Fix F2 on the branch; land the transition-tolerant Forge change (F1).
  2. Stamp, push, PR; CI `machsig-trust-extract` + `-judge` green; `--no-ff` merge.
  3. Pull and `lake build` the main checkout; re-run Forge CI.
  4. Retire the two monogate-lean witnesses and rebuild.
  5. Re-pin monogate.org's lean_claims to the merge commit.
  6. Redeploy machlib.org.
  7. Tighten the Forge need-sets to `u_le_inv_two_pow_52`.

## 7. Merge mechanics — HOLDS [checked]; F7

**The stamp.** Edit only the `review` block:

| field | value |
|---|---|
| `status` | `REVIEWED` |
| `reviewer` | the owner |
| `transition_report` | `docs/machsig/transition_2026-11-24.json` |
| `baseline_sha256` | `sha256:b0820dda28f999e7f3928c498ae86bcbf14797351a4c950b8db6313cb86e06e1` (= `--content-digest`) |

Also replace the `--update` boilerplate `note`; the gate does not read it. The digest covers everything EXCEPT
`review`, provenance included (`trust_gate.py:299-304`). So:
- editing `claims.json`, prose, or the report's MD does not invalidate the stamp;
- re-running `--update` for any reason means a new report and a re-check of the delta.

Merge with a merge commit (`git merge --no-ff`, or GitHub "Create a merge commit"), never squash or rebase. The
baseline's `provenance.machlib_commit` `92351128` must stay reachable, and only a merge commit makes a reviewed
reference.

**Master moved first (#15, `ea94aab8`). Simulated:**
- the stamped branch with `origin/master = ea94aab8` gives OK;
- a `--no-ff` merge onto `ea94aab8` gives OK, locally and with `--anchor ea94aab8`, and the reference becomes
  `b0820dda…`;
- the CI judge's form gives OK: `python3 -I -S <ea94aab8>/…/trust_gate.py --tree <merge> --anchor ea94aab8`.

No re-stamp is needed.

### F7 (INFO) — if `bounded-germ-transcendence` merges first

`bounded-germ-transcendence` (`4bfa3cc7`, base `fcc4ae1b`) touches neither `trust_baseline.json` nor any existing
statement. Its edits to existing modules are docstrings and doc tables, plus one import in `MachLib.lean` and a new
module.
- In either order, the reviewed reference is unchanged, this report stays exact, and its theorems are gate-INFO
  `new` rows. No re-stamp, unless someone re-runs `--update`.
- It overlaps this branch textually in CLAUDE.md, README.md, `what_is_proven.md`, `SELF_ASSESSMENT_…md` and
  `site/components/Numbers.tsx`, all figure edits. Expect conflicts there.
- Re-measure the figures (`prose_counts`) on the merged tree. Its new theorems' approved/conditional class may
  depend on this branch.

## Other findings

### F4 (LOW) — stale or wrong prose (fix with the merge; none is gate-held)

- **`IteratedExpBounds.lean:57`.** "no smaller step than `1/6` works (`(5/4)⁵ ≈ 3.05`)" has the direction backwards.
  Smaller steps work, e.g. `(7/6)⁷ ≈ 2.94`; it is the LARGER step `1/5` that fails. Say "no larger step".
- **"The tangent line at −1/6".** CLAUDE.md and 97d4c6d8's message say this; it is the tangent line at 0, read at
  −1/6, as the Lean comment says.
- **`TRANSITION_2026-11-24.md`.** "Each is found at `fcc4ae1b` and rests on trusted axioms only" is contradicted by
  its own list below (F3). Fix the script text and regenerate the MD; the JSON is unchanged, so the stamp is
  unaffected.
- **`claims.json` `_comment`s.** 23 still call `u_lt_one`/`u_le_half` axioms, and two state footprints that no
  longer exist (Q5).
- **`FPModel.lean`, `u`'s docstring.** "Kept abstract: the bounds below rest on `0 ≤ u < 1`" is now true of what the
  proofs use, but not of their kernel footprints, which show `u ≤ 2⁻⁵²` (F5).
- **CLAUDE.md "After merge".** It omits Forge (F1), the machlib.org redeploy and the main-checkout pull (F6).

### F5 (INFO, owner-ruled) — 87 theorems now formally rest on `u ≤ 2⁻⁵²` instead of `u < 1`

89 rows lost `u_lt_one` or `u_le_half`. 87 of them did not already rest on `u_le_inv_two_pow_52`, and now do: a
binary64-specific bound where they used only `u < 1` / `u + u ≤ 1` (`q_u_narrowing.txt`; `Certcom.bridge_add`,
`bridge_mul`, the grounded EML and PID certificates, …). This is the 2026-10-26 F1 pattern, and ruling U1
(OWNER_RULINGS_2026-10-14) ordered exactly this direction. No f32 claim is lost: the f32 path is parameterized over
`w` (`RoundsW`, `dot2_fwd_error`, `f32_u`) and never touches the axiomatic `u`. Recorded so nobody later reads these
footprints as format-generic.

## Recommendation

**Accept with changes.**
- Statements are identical, binders included.
- The six proofs are genuine and trusted-only.
- The ledger moved exactly the right names, with no headline, spine or disclosed-trusted invariant disturbed.
- The report reproduces byte for byte and binds the gate's own recompute from the correct reviewed baseline. C1-C7
  each fail under mutation.
- A stamped copy passes the full gate, including the isolated CI-judge form, before and after a `--no-ff` merge onto
  both `fcc4ae1b` and the new master `ea94aab8`. Every negative control is refused.

Before the stamp:
- **F2**: re-arm the five sqrt-firewall claims with `sqrt_le_of_le_sq` (claims.json only).

Before pulling the merge into `/home/monogate/monogate/machlib`:
- **F1**: land the transition-tolerant Forge `verify_grounding.py` change.

With the merge:
- **F4** prose;
- CLAUDE.md's after-merge list completed (**F6**).

Follow-ups:
- **F3**: harden C6 in the next template;
- the claim-audit rot rule (F2).

Owner's note:
- **F5**, already covered by U1.

## Scratch evidence (all under `/tmp/claude-1000/-home-monogate/c1816acb-9d2c-4072-803c-b04b5afab46f/scratchpad/review-2026-11-24/`)

- **Q1–Q2:** `probe_branch.lean`/`.tsv`/`_helpers.tsv`/`.out`, `serexpr_from_extractor.lean.part`, `ReviewSer.lean.inc`,
  `master_{Trig,FPModel,ExpExp,IterExp}.lean`/`.tsv` (+ `master_src/`), `q1_compare.txt`, `q1_full_compare.txt`,
  `control_sorry.lean`/`.out`, `author_probe_rerun.lean`/`.tsv`.
- **Q3:** `axiomledger_branch.out`, `AxiomLedger_mut{A,B,C}_*.lean`/`.out`, `AxiomLedger_master.lean`,
  `ledger_lists.py`, `q3_ledger_lists.txt`, `q3_headlines.txt`, `q3_classification.txt`, `baseline_*.json`,
  `baseline_axiom_diff.txt`, `gate13_branch.txt`, `gen_manifest.out`.
- **Q4:** `transition_runner.py`, `transition_runner_oldrule.py`, `repro_transition.json`/`.md`,
  `c_mutation_harness.py` (first run, with the `floor` no-op), `c_mutation_harness_v2.py`,
  `c_mutation_results_v2.txt`, `mutants/`, `q4_chain.txt`, `q4_c6_independent.txt`,
  `master_since_oldbaseline.diff`, `gate_sim_*.out`, `gate_neg_*.out` (the scratch clone itself was deleted).
- **Q5:** `claims_master.json`, `claims_branch.json`, `q5_claims.txt`.
- **Q6:** `forge_grounding_probe.lean`, `forge_grounding_{branch,mainckout}.out`, `q6_forge_verify_grounding.txt`,
  `forge_visible_names_check.out`, `q6_lean_claims.txt`, `q_u_narrowing.txt`.
