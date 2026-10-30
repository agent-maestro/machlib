# Independent review: branch `remove-false-forge-bridge-axioms` (gate-14 rebaseline), 2026-10-27 (b)

Scope: machlib `37ff5477`, `e1eacf33` and `3aa71728` on top of master `89e6855b` (the PR #10 merge). `git ls-remote
origin` shows GitHub master at `89e6855b`; the branch is not pushed, so no CI has run on it. Origin of the change:
finding F2 of `INDEPENDENT_REVIEW_2026-10-27.md` and the owner's ruling F2 in `OWNER_RULINGS_2026-10-27_implicit.md`
("a separate change right after this one").

I took no commit message, docstring or report at its word, and read `git log -p 89e6855b..HEAD` in full. Every Lean run
went through `tools/capped_lean.sh` (16G; 24G for AxiomLedger), one at a time, against `.olean`s that
`lake build --no-build MachLib` reported current (`All targets up-to-date (830 jobs)`). I modified no tracked file in
machlib, forge, monogate or monogate-lean; the only file this review adds is this one. Scratch evidence is under
`/tmp/claude-1000/-home-monogate/1e310cfa-129e-41fe-bf8e-88a49f35db3d/scratchpad/review3/`; the scratch worktree and
clone were removed afterwards. Each pass below sits next to a negative control that shows the instrument can fail.

| Q | verdict |
|---|---|
| 1 Were the two axioms (and the old `interval_add_scale`) false, and are EXACTLY those statements refuted? | **HOLDS** |
| 2 The new `interval_add_scale`; Forge uses; the two `ForgeTest` proofs | **HOLDS** |
| 3 Transition report, checks C1-C7, gate mechanics | **HOLDS**; **FINDING F4** (C6 is described more strongly than it checks; minor) |
| 4 Side effects (forge visible names, monogate.org, gate 13, other gates) | **HOLDS**; **FINDINGS F1** (forge's generated name list and its test go stale), **F5** (machlib.org redeploy) |
| 5 Other: prose, and the same flaw elsewhere | **FINDINGS F2, F3** (prose); no other axiom found with the flaw |

Recommendation: **accept with changes** (details at the end). Nothing found is a defect of the change's soundness.

---

## 1. The removed axioms and the old `interval_add_scale` were false, and exactly they are refuted — HOLDS

**False as stated.** Master's text (`git show 89e6855b:foundations/MachLib/Forge.lean`, lines 550-551, 579-580, 587-593):
- `interval_scale_unit_lit_le {k} (hk_pos : 0 < k) (hk_lit_le_one : 0 < k) : k ≤ 1` — the hypothesis named `..._le_one`
  has type `0 < k`, so the axiom is `0 < k → k ≤ 1`; false at `k = 1 + 1`;
- `interval_weight_sum_le {j k} : 0 < j → 0 < k → j ≤ 1 → k ≤ 1 → j + k ≤ 1` — false at `j = k = 1`;
- the old theorem `interval_add_scale` (`j ≤ 1`, `k ≤ 1`, no sum bound) — false at `x = y = j = k = 1`
  (`1·1 + 1·1 ≤ 1`). It was a theorem only because it was proved through the false `interval_weight_sum_le`.

`ForgeBridgeControls`' three refutations compile, and `#print axioms` gives 12, 12 and 14 axioms, all field and order
axioms in `trustedFootprint` (`addR`, `add_lt_add_left`, `add_zero`, `leR`, `le_iff_lt_or_eq`, `ltR`, `lt_irrefl_ax`,
`lt_trans_ax`, `oneR`, `zeroR`, `zero_lt_one_ax`, plus `mulR`, `mul_one_ax` for the third). None cites a removed axiom.

**C5 re-derived independently.** In scratch (`q_main.lean`) I typed master's three statements verbatim as scratch axioms
under fresh names and compared them with the control Props:

| comparison | `Expr ==` | `isDefEq` |
|---|---|---|
| master's `interval_scale_unit_lit_le` vs `OldUnitLitLeStatement` | true | true |
| master's `interval_weight_sum_le` vs `OldWeightSumLeStatement` | true | true |
| master's `interval_add_scale` vs `OldIntervalAddScaleStatement` | true | true |
| control: the intended `0 < k → k ≤ 1 → k ≤ 1` vs `OldUnitLitLeStatement` | false | false |
| control: `… → j + k ≤ 1 + 1` vs `OldWeightSumLeStatement` | false | false |
| control: the NEW `interval_add_scale` vs `OldIntervalAddScaleStatement` | false | false |
| each refutation's type vs `Old…Statement → False` | true (3/3) | true |

(`Expr ==` ignores binder names and binder info; `Expr.equal`, which does not, is false for the first three only because
the defs have anonymous binders.) Applied to master's text directly, all three refutations typecheck (`r1`-`r3`: `False`;
`r1`'s footprint then names the scratch axiom, as it must). As a second instrument, the gate's serializer copies applied
to the hand-typed master text reproduce master's baseline exactly: `sha256(serA)` equals master's pins of both axioms, and
`serT`'s digest equals master's `d` of the old `interval_add_scale`; the two "intended" controls do not match.

Negative controls (`q_neg.lean`, every declaration must be rejected, and is): the first refutation applied to the intended
statement, and the third applied to the new `interval_add_scale`, are type mismatches.

## 2. The new statement, Forge uses, and the `ForgeTest` proofs — HOLDS

**The new `interval_add_scale`** is `0 < j → 0 < k → j + k ≤ 1 → 0 ≤ x → x ≤ 1 → 0 ≤ y → y ≤ 1 → 0 ≤ x·j + y·k ∧
x·j + y·k ≤ 1`. It is true (proved; 19 axioms, all trusted; the bound is `x·j + y·k ≤ j + k ≤ 1`), and the old `j ≤ 1`,
`k ≤ 1` follow from positivity and the sum, so nothing a caller could supply before is lost except in the case where the
sum exceeds 1, which was the false case. Its type is `Expr ==` (and `Expr.equal`) to the statement I typed from the
commit's description; controls with `0 ≤ j`, with `j + k < 1`, and with all three bounds kept are all unequal. It is the
only restated theorem: the gate's transition has one `restated` row, no `removed`/`redefined` rows, and a C1 mutant that
restates a second theorem fails (Q3).

**Nothing a real Forge use needs became unprovable.**
- forge `origin/master` (`d30f7d5c`; the local `master` is 5 commits behind, and the files below are identical in both):
  `git grep` finds the three names only in the generated `lean_visible_names.py`. The emitter never cites any `interval_*`
  lemma. Its convex-combination path (`_render_convex_interval_verify`, `LeanBackend.py:1005`) emits `convexN_le/ge` with
  the weight sum as a hypothesis taken from the kernel's `requires`. Nothing in forge's axiom-policy registry names them.
- machlib: no file under `MachLib/` outside `Forge.lean`, `ForgeTest.lean` and `ForgeBridgeControls.lean` mentions them,
  tracked or untracked, `Discovered/` and the 12 unreachable modules included. Elsewhere only prose cites
  `interval_add_scale` (`SignTactic.lean:220`, a docstring the restatement does not affect; `Linarith.lean`, see F2).
- forge-examples, eml-stdlib, monogate, monogate-lean, monogate-research, monogate-dev, monogate-net,
  monogateforge-site, 1op: no hits.
- The literal facts the old bridges stood in for are provable on trusted axioms. Scratch, each with a footprint inside
  `trustedFootprint`: `0.5 ≤ 1`, `0.75 ≤ 1`, `0.5 + 0.5 = 1`, `0.3 + 0.6 ≤ 1`, and a use of the new
  `interval_add_scale` at the weights 0.3, 0.6.

**The two `ForgeTest` proofs rest only on trusted axioms.** By `#print axioms`, `halve_in_unit` and `add_halves_in_unit`
have 29 axioms each, and every one is in the new baseline's `policy.trusted` (156). So do `realOfScientific_le_of_nat` (29)
and `realOfScientific_one_dot_zero` (17), which the first proof uses, and `mach_decimal_ofnat`'s proof of
`0.5 + 0.5 = 1` (23). The `grew` rows' entering axioms (`mul_assoc`, `propext`, `Quot.sound`) are exactly what these
lemmas add. The same script flags `r1` (the scratch axiom) and `halve_in_unit_sorry` (`sorryAx`), so it can fail.
The commit's control holds: `realOfScientific_le_of_nat (by decide)` at `1.5 ≤ 1.0` is refused (`decide` proved
`15 * 10 ^ 1 ≤ 10 * 10 ^ 1` false). `mach_decimal_ofnat` refuses the false `0.5 + 0.6 = 1`, the old call shape of
`interval_add_scale` (two unit bounds) no longer typechecks, and both removed names are unknown identifiers.

## 3. Transition report and gate mechanics — HOLDS; FINDING F4

**Reproduction.** `python3 docs/machsig/transition_2026-10-27b.py` in a detached worktree at `3aa71728` printed
`rows 9 {'new': 6, 'grew': 2, 'restated': 1}; checks C1=ok … C7=ok`. The regenerated JSON's sha256 is `b1513bba…6755`,
equal to the committed one, and `git status` was clean afterwards, so the `.md` is byte-identical too. Rerunning the
committed statement probe into scratch (output path changed, nothing else) gives a TSV byte-identical to the committed
one (14 rows, sha256 `49b3ed94…`, the report's `statement_probe_sha256`). The probe's `serA`, `serT` and `serLevel` are
textually identical to `extract_trust.lean`'s `serExpr`/`serLevel` and `extract_statement.lean`'s `ser`, apart from
their names, and `tools/machsig/` is unchanged from master apart from the baseline.

**Each check tests what it says, and each can fail.** I ran the script's own source with only its input and output
paths substituted (`c_mutation_harness.py`). The unmutated control passes all seven checks and reproduces the committed
`gate_transition`. Every one of 18 mutants fails its own check and no other. Where possible the mutants are SEMANTIC:
serializations of real Lean statements from the scratch file, not edited strings.

| check | mutants (each fails its check) |
|---|---|
| C1 | restated to `0 ≤ j, 0 ≤ k` (probe and baseline agreeing); restated keeping `j ≤ 1, k ≤ 1` and adding the sum; the expected statement is `j + k < 1`; a second theorem (`interval_one_minus`) restated |
| C2 | the probe finds `interval_weight_sum_le` still in the environment; a third axiom (`floor_zero`) gone; `interval_weight_sum_le` re-pinned |
| C3 | `known` still lists `interval_weight_sum_le`; `HasDerivAt_sqrt` trusted on the way |
| C4 | `halve_in_unit` gains untrusted `HasDerivAt_sqrt`; `add_halves_in_unit` loses the trusted `mul_comm` |
| C5 | `OldUnitLitLeStatement` is the intended true statement; `OldWeightSumLeStatement` concludes `j + k ≤ 1 + 1`; `OldIntervalAddScaleStatement` is the new statement |
| C6 | a new theorem outside the module; a refutation resting on untrusted `HasDerivAt_sqrt` |
| C7 | a `CTRL_AX` and a `CTRL_THM` row serialized differently |

**Nothing in the transition is unexplained.**
- 1 restated row (`interval_add_scale`, 20 → 19): `interval_weight_sum_le` left, nothing entered.
- 2 grew rows (`halve_in_unit` 27 → 29, `add_halves_in_unit` 28 → 29): the removed axioms left, and `mul_assoc`,
  `propext` and `Quot.sound` entered through the literal proofs (Q2). Both statements and definition-closure digests
  (`d`, `c`) are unchanged.
- 6 new rows: the module's six theorems, three refutations and three private helpers. The module declares exactly
  these six theorems; the three `Old…Statement` are defs, so they are not rows.
- Axioms: exactly the two gone, none new or restated. Policy: `known` −2; `trusted` and `allowed_sorry` unchanged.
- The rest of the baseline diff is two new axiom sets, three no longer used, the provenance (sources bound to
  `e1eacf33`, `content_digest` `b0a0b85a…`, equal to `artifacts/machsig_extraction.json`'s) and the unreviewed `review`
  block.

**The full gate on a stamped copy** (a scratch clone with `origin/master` = `89e6855b`, the branch at `3aa71728`, and the
main checkout's signature set, bound to `e1eacf33`, whose sources "match this tree"):

| run | result |
|---|---|
| the branch as committed (main checkout and clone) | `REFUSED [baseline-unreviewed]`, rc 3 |
| stamped (`REVIEWED`, `baseline_sha256` = `--content-digest` = `sha256:3c8563b2…648d` = the report's `binding.new_baseline_sha256`), committed | `MACHSIG-TRUST OK`, 9 458 compared, 0 acquired, restated, redefined, removed, violations, axiom-restated, policy-widened; only the standalone `MACHSIG_RUN_ID` advisory |
| the same with `--anchor 89e6855b…` (what CI's judge passes) | OK |
| after `git merge --no-ff` onto master at `89e6855b`, plain and with `--anchor` at the merge | OK |
| control: the report with one row (`halve_in_unit`) dropped | `REFUSED [review-report-rows] … 8 theorem row(s) reported, 9 recomputed` |
| control: a stamp naming master's digest | `REFUSED [review-unbound]` |
| control: a stamp citing PR #10's report | `REFUSED [review-report-mismatch]` |

The report's `binding.old_baseline_sha256` (`sha256:0c23b9e5…`) is the digest master's stamp names.

**FINDING F4 (gate, minor).** C6 is described as "new rows = `ForgeBridgeControls`'s declarations". It checks that each new
row is inside the module's namespace or private prefix and that the three refutations are among them, so a missing helper
would pass. Here the six rows are all of the module's theorems (read above), so the report is right. Two things in the
template rest on the reader: this, and C1's target `ExpectedNewIntervalAddScale`, which is the author's own text in the
probe (I confirmed it independently, Q2). For the next use, have the probe list the module's theorems and compare C6 with
that list.

## 4. Side effects — HOLDS; FINDINGS F1, F5

| place | check | result | control |
|---|---|---|---|
| machlib | `lake env lean AxiomLedger.lean` | `AxiomLedger OK: 208 axioms pinned; 112 headline footprints ⊆ trusted (156); … 264 trust-list entries resolved to live axioms` | a copy with `interval_weight_sum_le` re-listed in `knownAxioms` FAILS (rc 1): `1 ledger entr(y/ies) name a vanished axiom (rot)` |
| machlib | theorem ledger | `THEOREM-LEDGER OK`: 12 413 declarations, 9 458 theorems, 9 332 approved, 125 conditional, 1 unchecked, as CLAUDE.md, README and `Numbers.tsx` now say. The env holds 176 `MachLib.*` + 32 `Certcom.*` axioms (dump), as claimed | — |
| machlib | gate 13, `soundness_witness_audit.py` | `SOUNDNESS-WITNESS OK — 156 trusted axioms, all accounted, toolchains agree` (the trusted set did not move) | `--selftest`: `SELFTEST PASS (7 specimens, 4 perturbations)` |
| machlib | `hypothesis_audit.py` | `OK — 39 … exactly the pinned set` | a baseline without `OldWeightSumLeStatement`: `NEW … consumed by weight_sum_le_false`, DRIFT, rc 1 |
| machlib | `prose_counts_check.py` | `95 tracked figures match` | — |
| machlib | `check_aggregator.sh` | `824 of 1089 modules reachable` (`ForgeBridgeControls` is imported by `MachLib.lean`) | — |
| machlib | `witness_audit.py` | `OK — 65 … exactly the pinned set` | — |
| machlib | `claim_audit.py` | `CLAIM-AUDIT PASS — all 579 claims resolve against #print axioms`, rc 0; none of the 579 claims names a changed row | — |
| machlib | `AXIOM_MANIFEST.md` | lists the trusted axioms only; neither removed axiom was trusted, so it does not change | — |
| forge | `gen_lean_visible_names.py --check` (read-only, run from forge against this build) | `DRIFT: 0 names added, 2 removed (… -['interval_scale_unit_lit_le', 'interval_weight_sum_le'])`, rc 1 | the generator's own code, `OUTPUT` pointed at scratch, regenerates 2 738 names, exactly the committed 2 740 minus those two, tokens unchanged, and `--check` against that copy prints `up to date: 2738 names` |
| monogate.org | `lean_claims.json` (pins machlib `89e6855b`) | no claim, environment or exemption names any of the nine rows or the two axioms; nothing changes until a re-pin, and a re-pin to the merge is a no-op for every claim | — |
| monogate-lean | `git grep` of the names | no hits; no witness or classification names them, so no monogate-lean change and no push-order coupling (unlike PR #10) | — |

**FINDING F1 (follow-up, forge).** Forge's generated `software/verification/lean/lean_visible_names.py` goes stale with
this merge: exactly the two removed names (measured above). That is harmless for emission (a superset only renames a
kernel function that would not have collided), but `test_the_committed_list_matches_the_environment`
(`software/verification/lean/tests/test_lean_visible_name_collisions.py`) runs the same `--check` and fails. It runs
whenever `lake` and a built `../machlib` exist. Forge's CI runner symlinks `../machlib` to this box's working checkout
(`.github/workflows/ci.yml`: `ln -sfn /home/monogate/monogate/machlib …`), so the test reads whatever branch that checkout
is on and has built. The checkout is on this branch now, built at its tip, so a forge CI run today would already fail it.
(Forge master's last CI run, 2026-10-27 01:35Z, was red before this branch existed, for a reason I could not read.)
What must follow the merge: regenerate the list in forge (`python3 tools/scripts/gen_lean_visible_names.py --machlib-root
../machlib/foundations`; −2 names) with the box's checkout on the merged master, and commit it in forge. Do not land it
before the merge: against master's environment it would fail the same test the other way.

**FINDING F5 (follow-up).** `site/components/Numbers.tsx` and `CheckIt.tsx` now say 208 / 9 458 / 9 332 / 125.
machlib.org deploys by hand, so the live site keeps master's figures (true until the merge) until someone redeploys it.
Redeploy after the merge. monogate.org's registry needs no change; re-pinning it to the merge commit is optional.

## 5. Other — FINDINGS F2, F3; the same flaw elsewhere: none found

**The same flaw elsewhere.** `Forge.lean` has no axioms left except `floor`, `floor_le`, `lt_floor_add_one` and
`floor_zero`, trusted and witnessed by `Int.floor` (previous review, Q2). Among the 208 axioms in the environment, 55 are
untrusted (dump `axioms.tsv`, `untrusted.tsv`, with types and docstrings). I read every one against its docstring:
- no docstring promises a condition the type lacks: `HasDerivAt_sqrt` "valid for x > 0" has `0 < x`; both
  `eml_tree_analytic_*` axioms carry their log-argument positivity; `cos_arccos`/`sin_arcsin` carry `[-1, 1]`;
- each holds at the standard reading:
  - the numeric ones checked numerically: `exp 1.35 = 3.85743 > 3.8570`; `exp 1.7 = 5.47395 < 5.4740`; `log 1.5`,
    `log 2.0`, `log 2.2` and `log 2.7` inside their intervals; `π < 3.141593`; `e < 3`;
  - `realPow_*` at `Real.rpow`, the `arccos`/`atan2`/`arctan`/`erf`/`lambertW` bounds and values at Mathlib's functions,
    and `tan_half_pos`, `tanh_neg`, `analytic_sin`;
  - `chain_algebraic_dependence` by the transcendence-degree bound its docstring gives;
- the four `HighDimensional` predicates are opaque, with axioms only of the form `… → Obligation p`, so the
  predicates can be read as `True`: consistent, and contentless by their own "UNGROUNDED" docstrings;
- `eml_pfaffian_validon_from_{sin,cos}_equality` have no docstring. Each is true because its premise is never met: a
  totalised-log EML function is definable in `ℝ_exp`, which is o-minimal, so it cannot equal `sin` or `cos`, which have
  infinitely many zeros. That is the content of the theorems they serve, and it is not this flaw.
- The 233 `axiom` lines in tracked `Discovered/` files are all one-line opaque `… : Real` symbols (233 of 233 end in `: Real`); none is a proposition.

A mechanical scan for the removed axiom's exact defect (two hypotheses of the same type, or a hypothesis equal to the
conclusion) over all 208 axioms: nothing among the 208. Both planted controls are flagged: master's `interval_scale_unit_lit_le`, re-declared, and an axiom whose hypothesis is its conclusion (`scanned 210 axioms; flagged 2`).

**FINDING F2 (prose, flagged by the author and still open).** `mach_linarith`'s docstring (`Linarith.lean:925-936`) says
it "Wraps the Forge interval-arithmetic `interval_add_scale` lemma", and that the linear cases "reduce to
`interval_add_scale` once `1/2` literal arithmetic is in scope". The macro has never cited it, and the literal
arithmetic is in scope (`mach_decimal`, `realOfScientific_le_of_nat`, as this change's `ForgeTest` shows). The commit
says so ("Not done here, noted"); the docstring still reads as a claim about the lemma this change restates.

**FINDING F3 (prose, pre-existing; one item contradicts this change).** Statements that `realOfScientific` facts are
axioms, or untrusted, stale since 2026-10-04:
- **a. `CLAUDE.md:179`**: "`mach_decimal`'s order arms rest on `realOfScientific_le_of_nat`/`_lt_of_nat`, which are not
  trusted". The new bullet at `CLAUDE.md:399` proves `0.5 ≤ 1` by `realOfScientific_le_of_nat` and counts
  `halve_in_unit` approved-policy, which is right: its footprint is 29 trusted axioms. The two now contradict each other.
- **b.** `CLAUDE.md:774` and `mach_decimal_ofnat`'s docstring (`Decimal.lean`): "`Basic.lean` bridges them **by axiom**
  (`realOfScientific_one_dot_zero`)". It is a theorem (17 trusted axioms).
- **c.** `Forge.lean:478`: "`realOfScientific_pos` is the underlying axiom in `MachLib.Basic`" (a theorem).
- **d.** `Forge.lean:650-658`: `floor` has "no defining properties"; three laws exist and are trusted.
- **e.** `ForgeTest.lean`'s header cites a "`MachLib.Forge.Interval` lemma library", a module that does not exist.

Checked and correct: the new prose in `Forge.lean` (the Class D note and the `interval_add_scale` docstring),
`ForgeTest`'s comments (`5·10 ≤ 10·10` is the `Nat` side condition), the `ForgeBridgeControls` docstring, the
CLAUDE.md bullet and counts, README, `what_is_proven.md`, the SELF_ASSESSMENT figures and `Numbers.tsx`/`CheckIt.tsx`.
Every figure in them was re-measured above.

## Recommendation

**Accept with changes.**
- Both axioms were false, and the controls refute exactly master's statements, shown by two independent instruments. The
  restated `interval_add_scale` is true and the only restatement, and nothing Forge emits used any of the three.
- The two `ForgeTest` proofs rest on trusted axioms only.
- The report reproduces byte for byte, and each of its checks is killed by its mutants. A stamped copy passes the full
  gate before and after a `--no-ff` merge, and three negative controls are refused.

Before the stamp, the owner's rulings:
- **S:** accept this rebaseline. Record it the way the last two were recorded (a rulings file cited by the stamp's
  `review.rulings`; ruling F2 of `OWNER_RULINGS_2026-10-27_implicit.md` is the authority for the change itself);
- **F2/F3b-e:** fix the Lean docstrings in this change, or later. Any `.lean` edit after this review changes the sources'
  content digest, so it needs `regen.py`, `--update` and the report rerun; the nine rows must come out identical.

With the merge: **F3a** (`CLAUDE.md` is not a gate-14 source, so it needs no regen). Then:
- stamp only the `review` block (`status: REVIEWED`, `reviewer`, `transition_report:
  docs/machsig/transition_2026-10-27b.json`, `baseline_sha256:
  sha256:3c8563b29747b983384f6ec4b123538977259ded6ca92a19960175a784b0648d`; the digest excludes the block, simulated
  above);
- run one `check_all.sh` on the stamped tip;
- merge with `git merge --no-ff`, since `e1eacf33` is the baseline's `provenance.machlib_commit`;
- if master moves first, rerun `regen.py`, `--update` and the script (update `OLD_REV`) and re-review the delta.

Right after the merge: **F1** (regenerate forge's visible-names list, with the box's machlib checkout on the merged
master) and **F5** (redeploy machlib.org). Follow-up: **F4** (the template's C6).

## Scratch evidence

All under `/tmp/claude-1000/-home-monogate/1e310cfa-129e-41fe-bf8e-88a49f35db3d/scratchpad/review3/`:

| file | for |
|---|---|
| `q_main.lean`, `q_main.out`, `q_main_ser.tsv` | Q1 (master text vs controls, refutations on master's text), Q2 (new statement, literal facts, footprints) |
| `q_neg.lean`, `q_neg.out` | Q1/Q2 negative controls |
| `statement_probe_rerun.lean`, `statement_probe_rerun.tsv` | Q3 probe reproduction |
| `c_mutation_harness.py`, `c_mutation.out` | Q3 mutants |
| `gate_*.out` | Q3 gate runs |
| `lvn/lvn_control.py`, `lvn/lean_visible_names_regen.py` | Q4 forge visible names |
| `axiomledger*.out`, `AxiomLedger_mut.lean`, `ledger.out`, `theorem_ledger_branch.json`, `gate13*.out`, `hyp*.out`, `prose.out`, `aggr.out`, `witness.out`, `claim_audit.out` | Q4 |
| `axiom_dump.lean`, `axioms.tsv`, `untrusted.tsv`, `dup_binders.lean`, `dup_binders.out` | Q5 |
