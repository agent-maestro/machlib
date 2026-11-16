# Independent review: branch `prove-derivable-axioms` (gate-14 rebaseline), 2026-10-27

Scope: `61f7ac5e` (five axioms become theorems) and `59f991bb` (UNREVIEWED gate-14 baseline, transition report,
generator script), on top of master `f572de8a`. `git ls-remote origin` shows GitHub master is still at `f572de8a`.
The branch is not pushed, so CI has never run on it.

I took no commit message at its word. Every Lean run went through `tools/capped_lean.sh` (16G, or 24G for
AxiomLedger and the ledger), one job at a time. Peak RSS was 1.8 GB. Nothing in machlib, forge or monogate-lean was
modified. The scratch worktree and the scratch clone were removed afterwards, and `git status` is clean in all three
repos. Each "pass" below sits next to a negative control that shows the instrument can fail.

The main checkout's `.olean`s are current for the branch tip. `lake build --no-build MachLib` printed
`All targets up-to-date (828 jobs)`. Every Lean probe below ran against them.

| Q | verdict |
|---|---|
| 1 Statements identical | **HOLDS** |
| 2 Proofs genuine, footprints trusted | **HOLDS** |
| 3 Sub-theory / claims policy | **HOLDS** for everything a gate holds; **FINDING F1** (u_le_one, policy judgment) |
| 4 Transition report | **HOLDS**; **FINDING F2** (a process gap: statement identity is checked by nothing the gate binds) |
| 5 Side effects in forge / monogate-lean / siblings | **HOLDS**; **FINDING F3** (minor: stale witness in monogate-lean) |
| 6 Other | **FINDING F4** (stale prose), **F5** (another derivable sole blocker, proved in scratch), **F6** (merge mechanics) |

Recommendation: **accept with changes.** No finding is a soundness or gate defect. F1 needs the owner's explicit
ruling. F4 should be fixed before or with the merge. F2 and F5 are follow-ups.

---

## 1. Statements — HOLDS

Method: `probe_branch.lean` (scratch) imports the five defining modules on the branch. For each name it prints the
kind, the defining module, the level params, and two serializations of the stored type:
- `SER` is a byte-for-byte copy of `tools/machsig/extract_trust.lean`'s `serExpr`. So `sha256(SER)` can be compared
  with master's baseline pins (`git show f572de8a:foundations/tools/machsig/trust_baseline.json`, `axiom_statements`).
  Those pins were computed in MASTER's environment, where the five were axioms.
- `FULL` is the same plus binder names and binder info (implicit/explicit), which `serExpr` drops.

| name | kind (branch) | module | sha256(SER) | master axiom pin | equal |
|---|---|---|---|---|---|
| `MachLib.exp_tangent_line_strict` | theorem | EMLAsymptoticClass | b99864189c13f743… | b99864189c13f743… | yes |
| `MachLib.Real.exp_gt_two_x` | theorem | SinNotInEMLDepth2Sweep | cbd0e6c79b57fd20… | cbd0e6c79b57fd20… | yes |
| `MachLib.Real.tanh_zero` | theorem | **Hyperbolic** (was Trig) | 42bfdcc8830ff405… | 42bfdcc8830ff405… | yes |
| `MachLib.Real.sqrt_one` | theorem | Trig | fc88431df02691da… | fc88431df02691da… | yes |
| `MachLib.Real.u_le_one` | theorem | FPModel | 0a5d8d1186ff22ea… | 0a5d8d1186ff22ea… | yes |

The full 64-hex digests are equal; the table shows prefixes. The level params are `[]` on both sides.

Controls:
- My `serExpr` copy reproduces the NEW baseline's pins for four unchanged axioms (`tanh_neg`, `u_lt_one`,
  `sqrt_zero`, `exp_gt_one_plus_self`), so it is the gate's own serializer.
- A mismatched pin (tanh_zero's SER against tanh_neg's pin) gives `False`.
- The probe reports `MachLib.Real.Real.tanh_zero` and `MachLib.Real.exp_tangent_line_strict` as `ABSENT`. No
  doubled-namespace or stray alias was created.

Binders: `FULL` for `exp_tangent_line_strict` is `(P x:d … (P hx:d …))` and for `exp_gt_two_x` it is `(P x:d …)`.
These are explicit binders named `x`/`hx`, the same as master's source text
(`axiom exp_tangent_line_strict (x : Real) (hx : 0 < x) :` and `axiom exp_gt_two_x : ∀ x : Real, …`). The other
three have no binders. Neither Trig.lean nor Hyperbolic.lean has an `open`, `variable`, local notation or instance
that could re-elaborate `0`/`1`/`tanh` differently. The digests confirm it at the Expr level: both use
`MachLib.Real.instOfNatZero`/`instOfNatOne`. Neither master nor the branch has any `attribute [...]` or `@[...]` on
the five names (`git grep` over `*.lean`, empty on both revisions), so no simp set or attribute was lost.

## 2. Proofs — HOLDS

`#print axioms` on the branch (`probe_branch.out`):
- `exp_tangent_line_strict`: 8 axioms, `exp_gt_one_plus_self` plus the carrier and `add_comm`.
- `exp_gt_two_x`: 34 axioms. Elementary exp only: `exp_add`, `exp_surj`, `exp_gt_one_plus_self`, `one_add_le_exp`,
  plus field and order axioms, `propext` and `Quot.sound`. No calculus.
- `tanh_zero`: 35 axioms: `sinh_eq`, `cosh_eq`, `tanh_eq_sinh_div_cosh`, `exp_add`, `exp_surj`, field, order.
- `sqrt_one`: 14 axioms: `le_sqrt_of_sq_le`, `sqrt_le_of_le_sq`, and order.
- `u_le_one`: 7 axioms: `u`, `u_lt_one`, and order.

There is no `sorryAx`, `ofReduceBool` or `trustCompiler` in any of them. Negative control: a planted
`theorem … := sorry` in the same file prints `sorryAx`.

The probe also shows that the proofs are not circular. `exp_gt_one_plus_self`, `u_lt_one`, `sqrt_le_of_le_sq` and
the other dependencies are `axiomInfo` in the branch environment, not theorems proved from the converted names. The
mathematics checks out: tangent line at 0 for x<1 and at 1 for x>0; sinh 0 = 0; antisymmetry from the two order
characterisations; `le_of_lt`.

Theorem ledger, run into scratch (`ledger.py --out …/theorem_ledger_branch.json`):
`THEOREM-LEDGER OK`, 9 440 theorems, 9 112 approved, 327 conditional, 1 unchecked, all invariants hold. These match
CLAUDE.md and the README. The five theorems and both private helpers are `approved_policy`. Of the 149 changed old
rows, **134 are now approved_policy and 15 stay conditional**. The 15 are held back by `HasDerivAt_sqrt` (11),
`arcsin_zero` (4), `floor*`, `exp_one_lt_three`, `arccos_zero` and `pi_upper_bound`, never by one of the five. All 9
new rows are approved. No axiom set in the environment contains any of the five (control: 45 sets contain
`u_lt_one`). Random sample of 10 changed rows (seed 20261027): 8 approved, 2 conditional (`Rasin0_bound`,
`Rasin7_bound`, on `arcsin_zero`/`HasDerivAt_sqrt`).

Second, independent instrument: the ledger's footprints equal the new machsig baseline's for **all 9 440 theorems**
(0 mismatches, 0 missing on either side).

## 3. Policy — HOLDS for every gate-held check; FINDING F1

**AxiomLedger.lean** on the branch printed `AxiomLedger OK: 212 axioms pinned; 112 headline footprints ⊆ trusted
(143); … 162 Option D spine theorems … (0 leaking); … 326 algebra-spine theorems field-axiom-checked (0 leaking);
251 trust-list entries resolved to live axioms; 1 sub-theory primitive(s) checked.`

Negative control: a scratch copy with `MachLib.Real.tanh_zero` put back into `trustedFootprint` FAILS, `rc=1`:
`1 trustedFootprint entr(y/ies) name no live axiom … [MachLib.Real.tanh_zero]`.

The 158 changed rows lie in 31 modules. None is an `algebraSpineModules` or `optionDSpineModules` module. No headline
can be among them, because every headline was approved before the change and the five were never trusted. No trust
list in AxiomLedger names any of the five. `known` is 180 `MachLib.*` + 32 `Certcom.*` = 212, read from the baseline
policy.

**Claims** (`tools/claim_audit/claims.json`): the file is identical to master's (579 claims), and no claim's
`forbid_axioms`, `forbid_axioms_exact` or `axioms_exact` names any of the five. I simulated the audit's own matching
rules: substring for `forbid_axioms`, whole token for `_exact`, set equality for `axioms_exact`. I ran them over old
and new baseline footprints for the **22 claims whose theorem is a changed row**. There are 0 problems on master and
0 on the branch. Negative control: a planted `forbid_axioms: ["one_add_le_exp"]` on `MachLib.compLt_deepDecay` is
clean on master and fires on the branch. I did not run `claim_audit.py` itself, as the brief allowed.

**Gate 13**: `tools/soundness_witness_audit.py` gives `SOUNDNESS-WITNESS OK — 143 trusted axioms, all accounted`.
Its `--selftest` gives `SELFTEST PASS`.

### FINDING F1 — `u_le_one` was primitive in the documented abstract FP model; 14 theorems now formally rest on `u < 1`

The muses' rule says "an axiom belongs to the smallest theory in which it is primitive", with `zero_ne_one_ax` as
the precedent. `FPModel.lean` still says of `u`: *"Kept abstract; every bound below holds for any `0 ≤ u ≤ 1`"*
(line 43). That model, `{u, u_nonneg, u_le_one}`, was the FP model before `u_lt_one` was added for binary64 on
2026-09-14. In it, `u_le_one` is primitive. Proving it from `u_lt_one` puts `u_lt_one` (false at `u = 1`) into these
14 footprints:

- `Certcom.bridge_add`, `bridge_mul`, `evalEML_forward_error`, `evalEML_prod3_fwd`, `length_sq2_bridge`,
  `pipeline_prod3`, `pipeline_sqSum`, `prod3_bridge`
- `MachLib.Real.Rounds.nonneg`, `cosh_fwd_bound`, `cosh_fwd_reduces_to_exp`, `length_sq2_fwd_error`,
  `length_sq3_fwd_error`, `one_sub_u_nonneg`

Each is a swap: it lost `u_le_one` and gained `u_lt_one`. The bounds are still true for `u ≤ 1`, but their kernel
footprints no longer show it. No gate holds a "u ≤ 1 model" footprint, which is why AxiomLedger stays OK.

Mitigation: the owner's ruling U1 already calls `u_le_one` derivable and the tiering "incoherent", so this may be
exactly what was meant.

The alternative is to keep `u_le_one` primitive and trust it, with an easy witness at 2⁻⁵³, plus a
`subTheoryPrimitives`-style record. That would widen the policy (`policy-widened`), so it would need its own
approval. **Owner's call.** Either way, FPModel line 43's sentence should be changed or qualified.

## 4. The transition report — HOLDS; FINDING F2

**Reproduction.** I ran `python3 docs/machsig/transition_2026-10-26.py` in a detached worktree at `59f991bb`. It
printed `rows 158 {'swap': 54, 'grew': 29, 'shrank': 66, 'new': 9}; checks C1=ok … C6=ok`, exit 0. The
regenerated JSON's sha256 `9c916d64…46351` equals the committed one. `git status` was clean afterwards, so the
`.md` is byte-identical too.

**What the gate binds is computed only by the gate's functions.** I read `review_problems`. From a report, the gate
reads only `binding.new_baseline_sha256`, `binding.old_baseline_sha256` and `gate_transition`:
- the two digests come from `trust_gate.baseline_content_digest`;
- `gate_transition` comes from `trust_gate.gate_transition(old, new)`.

The script imports both, and `tools/machsig/trust_gate.py` is unchanged between master and the branch. The other
binding fields (`old_baseline_file`, `old_baseline_role`, `new_sources_commit`) are labels the gate does not read.
Control: editing only `checks` in a report still passes `review_problems`. That is by design (GATE14_REPAIR: only
the machine block is bound), so C1–C6 are evidence for the reviewer, not for the gate.

**The old side is the right one.** The baseline blob is `c2cef531` at `37edde55`, `4a4ac875` and `f572de8a`. It
changed only in `94c543ff`, which landed through the merge `37edde55`, and `37edde55` is on master's first-parent
line. `trust_gate.reviewed_chain(root, f572de8a)` returns exactly one reference, `sha256:c0e60b09…` labelled
"the baseline reviewed at 37edde55da19". That equals `binding.old_baseline_sha256`. `default_anchor` = `f572de8a`.
The committed new baseline's content digest `sha256:aab76eb9…` equals `binding.new_baseline_sha256`. The `review`
block is excluded from the digest, so stamping does not invalidate the report.

**C1–C6 are real.** I ran the script's own source with mutants of the new baseline, swapping the input path and the
output path only. Each mutant fails its own check; the unmutated control passes all six.

| mutant | result |
|---|---|
| C1: an unrelated theorem's statement digest changed | C1 fails (and C4) |
| C2: an axiom pin restated | C2 fails |
| C3: `floor` added to `trusted` | C3 fails |
| C4: a theorem loses `exp_add` | C4 fails |
| C5: a trusted axiom no proof uses (`Certcom.floatOfR`) enters a footprint | C5 fails |
| C5b: an untrusted one (`floor`) enters | C5 fails |
| C6: a fake new theorem not present at `f572de8a` | C6 fails |

My first C5 mutant was a no-op: it added an axiom the footprint already held, so C5 still passed. I replaced it. I
record this so nobody re-uses that mutant.

Weaknesses, none of which affects this data:
- C6's `git grep` matches the short name, not the namespace. I checked by hand that `affine_remap_nonneg_right` and
  `step_nonneg` are in `namespace MachLib.Real` in `Linarith.lean` at `f572de8a`, came in with `d67304fa`
  (PR #6), and are absent at `37edde55`.
- The `.md` renders `Quot.sound` as `` `sound` `` (cosmetic).
- `OLD_REV` is hard-coded; if master moves, see F6.

**The full gate on a stamped copy.** I made a scratch clone with `origin/master` = `f572de8a` and the check_all
signature set copied in. That set is bound to `61f7ac5e`, its sources digest `792374…` matches, and it is clean.
- Unstamped branch tip: `REFUSED [baseline-unreviewed]`, rc 3.
- Stamped (status REVIEWED, digest from `--content-digest`, report = the committed JSON) and committed:
  `MACHSIG-TRUST OK`, 9 440 theorems compared, 0 acquired/restated/redefined/removed/violations. The only advisory
  was the standalone `MACHSIG_RUN_ID` one.
- The same with `--anchor f572de8a` (the CI PR judge): OK.
- After `git merge --no-ff` onto a master at `f572de8a`, local run and `--anchor f572de8a`: OK. `reviewed_chain`
  at the merge now returns the new baseline as the reference.
- Negative control: the same stamped commit with one row dropped from the report:
  `REFUSED [review-report-rows] … 157 theorem row(s) reported, 158 recomputed`.
- In-process controls: wrong `baseline_sha256` gives `[review-unbound]`; judged against the origin gives
  `[review-report-mismatch]`; an edited `entered` list gives `[review-report-rows]`.

### FINDING F2 — nothing the gate binds checks that a converted axiom's statement is kept

In `gate_transition`, each converted name appears only as an axiom `gone` plus a theorem `new`. The axiom pin
(`serExpr` digest) and the theorem's `d` (`extract_statement`'s `ser`, truncated) are different serializations, so
the gate cannot compare them. C1–C6 do not compare them either. The report's sentence "each is now a theorem of the
same name and statement" is prose.

A conversion that restated an axiom under its own name would therefore pass the gate and C1–C6 alike, as long as the
dependents still compiled. For this change I verified the statements independently (Q1), so this is not a defect
here.

Recommendation for the next such change: add a C7 that recomputes `extract_trust`'s `serExpr` for each converted
theorem and compares it with the old axiom pin. Q1's probe is a ready template; it is 1 s and 1.5 GB.

## 5. Side effects — HOLDS; FINDING F3 (minor)

**Forge** (local master is 5 commits behind origin, but neither the generator nor `software/verification/lean/`
differs between them):
- `gen_lean_visible_names.py --machlib-root <branch> --check` gives `up to date: 2740 names`. `tanh_zero` is still
  visible: Forge's header imports `MachLib.Forge`, which imports Hyperbolic. The private helpers are not visible.
  Negative control: a copy of `lean_visible_names.py` with `tanh_zero` deleted gives
  `DRIFT: 1 names added … +['tanh_zero']`, rc 1.
- Forge's admission registry (`axiom_policy.py`, 58 names, policy `2026-10-04.2`) registers none of the five, so no
  Forge artifact could have passed by citing them. A future artifact citing `tanh_zero` now rests only on
  registered axioms. One citing the others now rests on `exp_gt_one_plus_self`, `one_add_le_exp`,
  `le_sqrt_of_sq_le`, `sqrt_le_of_le_sq` or `u_lt_one`, none registered, so it still fails closed.
- No Forge proof trail (25 files), evidence JSON or `proof_discharge_baseline.json` mentions the five. No trail
  theorem is a changed row.

**monogate-lean**: only `AxiomWitnessBridge.lean` imports MachLib, and it imports all of it, so the move of
`tanh_zero` cannot break an import. `checkWitnessed` uses `env.find?` and `ci.type` without asking for `axiomInfo`,
so the `tanh_zero` witness still typechecks: same type, by Q1. The other hits (`HyperbolicPreservation`,
`UpperBounds`, `MachLibRealModelHyperbolic`) are Mathlib-only files using Mathlib's `Real.tanh_zero`/`Real.sqrt_one`.

**Other repos.** I ran `git grep` over every sibling repo under `/home/monogate/monogate/`. The hits are:
- historical docs and research notes in monogate-research, monogate-engine and monogate;
- an LLM prompt in monogate-engine that lists names an agent may use;
- graph/data snapshots.

None depends on the five being axioms. MachLib's own `Discovered/`, `ForgeCheck/` and `legacy_eml/` (not built by
`lake build`) do not mention them.

**F3 (minor).** By the corpus's own precedent ("a theorem needs no witness": 18 retired on 2026-10-04, 6 on
2026-10-05), the `tanh_zero` witness in monogate-lean should be retired. Until then the bridge's log line counts it
among "registered axioms verbatim-witnessed". It is outside the trusted footprint, so gate 13's sums are unaffected,
and the commit message discloses it. Follow-up in monogate-lean, not a blocker.

## 6. Other — FINDINGS F4, F5, F6

### F4 — stale or contradictory prose (fix before or with the merge)

- `foundations/docs/what_is_proven.md:487-488`: "As of **2026-10-05** the ledger pins **212 axioms** (… **185**
  `MachLib.*` plus 32 `Certcom.*`)". The total was updated and the split was not: 185 + 32 = 217. It should read
  180 + 32, dated 2026-10-26. `prose_counts_check` tracks only the total, so it passes (`91 tracked figures match`).
- `MachLib/EMLReciprocalDepth2.lean:544`: "`exp_tangent_line_strict` … is a classical-citation axiom, not a theorem.
  It is used here and nowhere else in this file, so `#print axioms` separates the theorems that depend on it." This
  is false now: no footprint shows it any more, so the "Cost 1" bookkeeping the docstring promises is gone.
- `MachLib/EMLDepth2Case9RowU2.lean:116`: "the `exp_tangent_line_strict` axiom that `var_var_not_mx` had to pay
  for".
- `MachLib/GroundedInstanceArith.lean:19`: "`u_le_one` is an axiom that is neither witnessed nor in the trusted
  footprint". It is a theorem now, on a trusted footprint. The same paragraph's `realOfScientific_*_of_nat` remark
  has been stale since 2026-10-04.
- `MachLib/FPModel.lean:78`: "`u_le_half`, `u_lt_one` and `u_le_one` follow from it and are left as they were".
  `u_le_one` was not left as it was. Line 43 is covered under F1.
- `README.md:208` "Measured 2026-10-10:" and `site/components/Numbers.tsx` `MEASURED_ON = "2026-10-10"` now sit
  over 2026-10-26 numbers.
- The `CLAUDE.md` section added in `61f7ac5e` ends "Do not `--update` and commit". The very next commit does exactly
  that, correctly, as an UNREVIEWED baseline for review. After the merge the sentence will mislead the next agent.
  Suggested wording: a rebaseline is `--update` + transition report + a reviewed stamp, merged with `--no-ff`.

### F5 — "provable means proved" is not at zero; one more derivable sole blocker, kernel-checked in scratch

CLAUDE.md's new section lists what is "still conditional, and NOT derivable here". The live sole-blocker ranking on
the branch also has `exp_exp_minus_exp_strictly_increasing`
(`∀ x y, x < y → exp (exp x) - exp x < exp (exp y) - exp y`, `ExpExpNotInEML1.lean:53`). It is the sole blocker of
4 conditional theorems: `exp_exp_not_in_eml_1`, `exp_exp_ne_eml_var_const`, `strict_eml_one_subset_eml_two` and
`strict_eml_one_two_via_iter_exp`.

It is derivable from trusted axioms. `eemes_derivable.lean` (scratch, about 35 lines) proves a theorem whose type is
`Expr`-equal to the axiom's (`same type (Expr ==): true`). Its footprint is 35 axioms, all in `trustedFootprint`
(computed: `untrusted: []`), elementary exp only: `exp_add`, `exp_lt`, `exp_surj`, `exp_gt_one_plus_self`,
`one_add_le_exp`, field, order.

`exp_one_lt_three` (sole blocker of 5) also looks derivable from the tangent line (e ≤ (6/5)⁶ < 3). I did not check
that one. Out of scope for this change, but the owner's policy says the count "goes to zero and stays there", and
this round's own method surfaced these.

### F6 — merge mechanics the owner should follow

1. The branch is red until stamped. Merging it unstamped would make master's gate refuse (`[baseline-unreviewed]`).
2. Stamp = `status: REVIEWED`, `reviewer`, `transition_report: docs/machsig/transition_2026-10-26.json`,
   `baseline_sha256: sha256:aab76eb91d3bbb60103bd3e74a05b756d7a7b35ae6abbd0dd04ee69d46298c67` (=
   `--content-digest`). Edit only the `review` block; the digest excludes it, so the report stays valid. Simulated
   above: OK.
3. Merge with `git merge --no-ff`. Only a merge commit makes a reviewed reference. A squash or rebase would also
   drop `61f7ac5e`, the baseline's `provenance.machlib_commit`, which a fresh clone refuses as
   `[baseline-provenance-unresolvable]`.
4. If master moves before the merge, re-check:
   - if it changes the baseline or any of the 158 rows, rerun regen + `--update` + the script (update `OLD_REV`) and
     re-review;
   - if it only adds theorems, the report is still exact.

   GitHub master is `f572de8a` as of this review.
5. The stamp authenticates content, not a person. Under the shared-account limit recorded in OWNER_RULINGS, this
   review and the owner's sign-off are the record.

## Recommendation

**Accept with changes.**
- Statements are identical.
- The proofs are genuine and rest only on trusted axioms.
- No gate-held sub-theory, spine, headline or registered claim is disturbed.
- The transition report reproduces byte for byte, binds exactly the gate's own recompute from the correct reviewed
  baseline, and a stamped copy passes the full gate before and after a `--no-ff` merge, with negative controls
  refused.

Before or with the merge:
- Make the owner's explicit ruling on **F1** (or trust `u_le_one` instead, separately approved) and fix
  FPModel line 43.
- Fix the **F4** prose.

Follow-ups: **F2** (add a statement-identity check to future conversion reports), **F3** (retire the monogate-lean
witness), **F5** (convert `exp_exp_minus_exp_strictly_increasing`, check `exp_one_lt_three`, and correct CLAUDE.md's
"still conditional" list).

## Scratch evidence (all under `/tmp/claude-1000/-home-monogate/1e310cfa-129e-41fe-bf8e-88a49f35db3d/scratchpad/review/`)

`probe_branch.lean` / `.out` / `.tsv` (Q1–Q2), `axiomledger_branch.out`, `AxiomLedger_mut1.lean` /
`axiomledger_mut1.out` (Q3 control), `theorem_ledger_branch.json` / `ledger_branch.out` (Q2),
`c_mutation_harness.py` (Q4 C-check mutants; it ran against a worktree at `59f991bb`, since removed),
`forge_registry.txt`, `forge_trail_theorems.txt` (Q5), `eemes_derivable.lean` (F5).
