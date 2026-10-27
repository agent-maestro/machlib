# Independent review: branch `implicit-continuity-and-witnesses` (gate-14 rebaseline), 2026-10-27

Scope: machlib `ee38b6e0` (the implicit-function repair and fifteen trusted axioms) and `1c8cb712` (UNREVIEWED gate-14
baseline, transition report, statement probe), on top of master `2431d705`; monogate-lean `9979c8b` (the Mathlib
witnesses). `git ls-remote origin` shows GitHub master at `2431d705` for machlib and `76835b9` for monogate-lean. Neither
branch is pushed, so no CI has run on either.

I took no commit message, docstring or report at its word. Every Lean run went through `tools/capped_lean.sh` (16G, or
24G for AxiomLedger, the ledger and the claim audit), one job at a time. Peak RSS was about 3 GB. I modified no tracked
file in machlib, monogate-lean or forge, with one disclosure: `tools/gen_axiom_manifest.py` has no `--check` flag, so
running it rewrote `AXIOM_MANIFEST.md`; the content was byte-identical and `git status` stayed clean. The scratch worktree
and the scratch clone were removed afterwards, and `git status` is clean in all three repositories. Each pass below sits
next to a negative control that shows the instrument can fail.

The main checkout's `.olean`s are current for the branch tip: `lake build --no-build MachLib` printed
`All targets up-to-date (829 jobs)`, and `lake build --no-build MonogateEML.AxiomWitnessBridge` in monogate-lean printed
`All targets up-to-date (3569 jobs)`.

| Q | verdict |
|---|---|
| 1 Soundness of the restated axioms | **HOLDS**; **FINDING F3** (the bridge reads MachLib definitions by fiat; follow-up) |
| 2 The eight `HasDerivAt2` rules and the `floor` laws | **HOLDS**; **FINDING F1** (two of the fifteen are derivable) |
| 3 The refutations | **HOLDS** (the old LOCAL form is refuted only by implication; F7f) |
| 4 The repair downstream | **HOLDS** |
| 5 Transition report and gate mechanics | **HOLDS**; **FINDINGS F4, F5** (C1 does not pin the binder's domain; an unenforced baseline key) |
| 6 Side effects | **HOLDS**; **FINDING F8** (push order and merge mechanics) |
| 7 Other | **FINDINGS F2** (two FALSE axioms in the environment), **F6** (the approval is not recorded), **F7** (prose), and a pre-existing derivable axiom (in F1) |

Recommendation: **accept with changes.** No finding is a defect of this change's soundness: the restated axioms are true,
every trusted axiom outside the float bridge holds in one model, and the gate passes a stamped copy before and after a
`--no-ff` merge. F1 and F6 need the owner's ruling before the stamp. F7a-c should be fixed with the merge. F2, F3, F4 and
F5 are follow-ups.

---

## 1. Soundness of the restated axioms — HOLDS; FINDING F3

**The statements.** In a scratch file importing `MachLib`, I wrote both restated axioms out by hand and compared their
elaborated `Expr`s with the environment's (`Expr ==`, which ignores binder names and binder info). Both are equal; the
same hand-written text without `ContinuousAt` is NOT equal to either (control). So the axioms are exactly "the old
statement plus `ContinuousAt yc x` before the curve identity".

**They are true at the interpretation, and the proof has no gap.** `implicit_deriv_core` (monogate-lean) assumes
`HasFDerivAt F L (x, yc x)`, `L (0, 1) ≠ 0`, `ContinuousAt yc x` and `F (s, yc s) = 0` eventually near `x`, and concludes
`HasDerivAt yc (−L (1,0) / L (0,1)) x`. I read the proof: continuity makes the curve tend to `(x, yc x)`, so the Fréchet
remainder gives `a u + b v = o(‖(u, v)‖)` along it; that gives `v = O(u)`, then `a u + b v = o(u)`, which is the
derivative. This is the standard argument and uses exactly the hypotheses stated. Kernel evidence: `#print axioms` on
`implicit_deriv_core`, both implicit witnesses, all eight rule witnesses, the three `floor` witnesses and
`old_implicit_statement_false` gives `[propext, Classical.choice, Quot.sound]` for all fourteen.

The bridge check, rerun in a scratch file that imports `MonogateEML.AxiomWitnessBridge` and calls its own `mkMap` and
`checkWitnessed`:

| check | result |
|---|---|
| `hasDerivAt_implicit` ⊣ `hasDerivAt_implicit_witness` | true |
| `hasDerivAt_implicit_local` ⊣ its witness | true |
| `floor_zero` ⊣ `floor_zero_witness` | true |
| control: `hasDerivAt_implicit` ⊣ the LOCAL witness | false |
| control: `HasDerivAt2_projX` ⊣ the `projY` witness | false |
| control: `floor_le` ⊣ the `lt_floor_add_one` witness | false |
| control: a scratch axiom with the OLD statement ⊣ the restated witness | false |
| control: the same scratch axiom ⊣ `sorry` | false |

The committed bridge build (replayed) reports `110/110 registered axioms verbatim-witnessed` and coverage
`109 witnessed + 3 standard + 14 mapped + 32 float-bridge + 0 tracked-gap = 158, against 158 trusted axioms`.

**The interpretation of `ContinuousAt` is faithful.** MachLib's `ContinuousAt` is a `def` (ε-δ, with MachLib's `abs`), and
the bridge reads it by fiat. I interpreted the def's BODY with the bridge's own map and asked `isDefEq` against the fiat
reading: true. Control: the same with `≤ ε` in place of `< ε` is false. MachLib's `abs` is
`if 0 ≤ x then x else -x` (classical decidability), equal to `|x|` at every point (a two-line proof in the scratch file).

**The interpretation of `HasDerivAt2` is faithful to its use.** `HasDerivAt2` is an opaque axiom, fixed only by the
eight rules and the two implicit axioms. Its docstring says "joint (Fréchet) differentiability", and the reading is
`HasFDerivAt` of `(a, b) ↦ f a b` with derivative `fx • fst + fy • snd`. A weaker reading (partial derivatives only)
would falsify `HasDerivAt2_comp` already, so the axioms force a Fréchet-like reading anyway. Every `HasDerivAt2` fact the
corpus concludes is built from the rules (for example `hasDerivAt2_exp_sum`), and those hold at the reading.

**Joint satisfiability (old trusted set plus new).** The bridge interprets every trusted axiom with ONE map, so the 126
non-float trusted axioms (109 witnessed, 14 mapped, 3 standard) hold together in one structure over Mathlib's `ℝ`. The
fifteen new ones share no symbol with the 32 float-bridge axioms except the arithmetic of `ℝ`. I dumped all 212 axioms in
the environment (`MachLib.*` and `Certcom.*`, with types): `floor` occurs in exactly its own four axioms, and
`HasDerivAt2`/`ContinuousAt` occur only in the bivariate family, the two implicit axioms and `hasDerivAt_continuousAt`. So
the new set cannot make the trusted set jointly unsatisfiable, and an approved-policy theorem cannot be false at this
reading.

**FINDING F3 (soundness methodology, pre-existing, follow-up).** The bridge reads MachLib DEFINITIONS by fiat as well as
opaque axioms: `log`, `abs`, `ContinuousAt`, `BoundedAbove`, `RealSetFinite`, `Ioi`/`Icc`/`Ioo`. Only `natCast` and
`realOfScientific` carry an `interp_agrees_*` check. A fiat reading that disagrees with the definition certifies a
statement MachLib does not mean, and one does today: MachLib's `log` is `0` on nonpositives, while the bridge reads
`Real.log`, for which `Real.log (-x) = Real.log x`. Demonstrated in scratch:
- a scratch axiom `∀ x, log (-x) = log x` is "witnessed" by the bridge (`checkWitnessed` with `Real.log_neg_eq_log`:
  true; control with a wrong witness: false);
- in MachLib the same statement gives `False` from `log`'s own definition (`log_nonpos`, `log_exp`, `zero_ne_one_ax`;
  scratch `logEven_inconsistent`).

No trusted axiom is affected: the five that mention `log` use it only on positive arguments, where the two readings agree,
and `ContinuousAt` and `abs` agree as shown above. But `ContinuousAt` is now inside two trusted axioms, and nothing would
notice if its definition changed. Gate 14 would see it as `redefined` through the 110 theorems that mention it; the bridge
would not. Add `interp_agrees_ContinuousAt` and `interp_agrees_abs`, and one for `log` on its domain. Note also that
`checkWitnessed` compares types with the elaborator's `isDefEq`; the witness theorems are kernel-checked, the match is
not. The kernel could re-check it by adding the elaborated term as a declaration.

## 2. The eight rules and the `floor` laws — HOLDS; FINDING F1

**The rules.** Each rule's Mathlib witness typechecks at the rule's interpreted type, and a swapped witness is rejected
(Q1 table). As calculus statements they are correct:
- `projX`/`projY`/`const` are the coordinate and constant maps;
- `add`/`sub` are linear;
- `mul` is the product rule `(fx·g + f·gx, fy·g + f·gy)`;
- `scomp` is the chain rule for a one-variable function after a bivariate one;
- `comp` is the chain rule along a curve.

**`floor`.** Its laws are `floor x ≤ x`, `x < floor x + 1` and `floor 0 = 0`. With `floor ↦ (⌊·⌋ : ℤ) cast to ℝ`, all three
hold (`Int.floor_le`, `Int.lt_floor_add_one`, `⌊0⌋ = 0` by `simp`). That answers the `floor_zero` question directly. No
other axiom in the environment mentions `floor` (axiom dump). `natCast` is a definition (a recursion) with its own
agreement check, and no axiom relates it to `floor`, so nothing about integers can clash with the reading. Observation,
not a defect: the three laws do not say `floor` is integer-valued. The identity function satisfies all three, so every
theorem resting on them holds for every function with values in `(x − 1, x]` and `0 ↦ 0`, `Int.floor` among them. The
`Forge.lean` docstring says as much.

**FINDING F1 (policy, owner's ruling).** Two of the fifteen newly trusted axioms are DERIVABLE from trusted axioms. The
owner's "provable means proved" policy (2026-10-04) says a derivable axiom must be converted, not kept:
- `hasDerivAt_implicit` follows from `hasDerivAt_implicit_local` on `(x + -1, x + 1)` (scratch
  `hasDerivAt_implicit_derived`, about 15 lines). Its type is `Expr`-equal to the axiom's (control: unequal to the local
  axiom's). Its footprint is 20 axioms, all trusted, and it does not use `hasDerivAt_implicit`. 127 theorems use the
  global form.
- `HasDerivAt2_sub` follows from `HasDerivAt2_add`, `HasDerivAt2_mul` and `HasDerivAt2_const` at `−1`, plus field laws
  and `funext` (scratch `HasDerivAt2_sub_derived`). Its type is `Expr`-equal, and its footprint is 21 axioms, none of them
  `HasDerivAt2_sub`. 31 theorems use it.
- Pre-existing, found on the way: `HasDerivAt_of_eq`, trusted for a long time and registered by Forge as primitive, is
  derivable from `funext` alone (`fun h hf => (funext h) ▸ hf`; footprint `[MachLib.Real, Quot.sound, HasDerivAt]`;
  `Expr`-equal type). 1 323 theorems rest on it. Forge's registry gives its reason as "MachLib's HasDerivAt is opaque, so
  nothing else fixes how it behaves under pointwise equality". That is false: equality of the function argument fixes it
  for every predicate, and `funext` turns pointwise equality into equality.

Converting any of them swaps footprints and needs its own transition report. **Owner's call:** convert the two new ones
inside this rebaseline (a new `--update`, transition report and re-review of the delta), or admit them as approved and
convert them, and `HasDerivAt_of_eq`, next. `HasDerivAt_of_eq` also needs Forge's registry reason corrected.

## 3. The refutations — HOLDS

**C6, re-derived by two instruments.**
1. I reran the committed statement probe into scratch (its output path changed, nothing else). Its TSV is byte-identical
   to the committed one, 257 rows. Its two serializers are textually identical to `extract_trust.lean`'s `serExpr` and
   `extract_statement.lean`'s `ser`, and `tools/machsig/` is unchanged from master apart from the baseline.
2. Independently of any serializer, I wrote master's text verbatim (`git show 2431d705:…BivariateDeriv.lean:63-65` and
   `…TwoExpCurveCount.lean:29-41`, binders as `∀`) into a scratch file and compared `Expr`s:
   - master's `hasDerivAt_implicit` == `OldImplicitStatement`: true;
   - master's `khovanskii_rolle_count_curve` == `OldCurveCountStatement`: true;
   - control: master's text with `fy ≠ 0` changed to `fx ≠ 0`: false;
   - control: master's old statement == the NEW axiom: false (and false for the local form too).

**The refutations rest on what they claim.** Ledger footprints (both approved-policy):
- `implicit_without_continuity_inconsistent` (40 axioms) uses the four `HasDerivAt2` rules it names (`projY`, `sub`,
  `const`, `mul`), `rolle_ct` (through the mean value theorem) and the one-variable rules. It does not use either implicit
  axiom: the old statement is a hypothesis.
- `old_curve_count_false` (30 axioms) uses only `HasDerivAt2`, `_const`, `_mul`, `_projX`, `_projY`, `_sub` and field and
  order laws.

The mathematics checks out:
- `b (b − 1) = 0` on both values of the step, and `fᵧ = 2 yc − 1 = ±1`, so the old axiom gives `yc' = 0` everywhere, and
  the mean value theorem on `[−1, 0]` gives `1 = 0`;
- for the curve count, `g = a − b` vanishes along the step at `0` and at `1`, while the Jacobian is `−fᵧ ≠ 0`, so the
  bound `0 + 1` is beaten by two zeros.

**monogate-lean's `old_implicit_statement_false`.** I interpreted the scratch old-statement axiom's type with the bridge's
map and asked whether `old_implicit_statement_false : ¬ ⟦old⟧`: defeq, true. It is also `¬ ⟦OldImplicitStatement⟧`
(true). Control: `¬ ⟦new axiom⟧` is false. So it refutes exactly the old statement at the interpretation, and not the new
one.

The old LOCAL form has no refutation in the corpus. It implies the old global form (take `(x − 1, x + 1)`), so it is
refuted too. Scratch `old_local_implies_old_global` and `old_local_inconsistent` compile (see F7f).

## 4. The repair downstream — HOLDS

**Who uses the implicit axioms.** The new theorem ledger (`THEOREM-LEDGER OK`: 9 449 theorems, 9 320 approved, 128
conditional, 1 unchecked) against the 2026-10-26 one (9 440):
- 130 theorems rest on `hasDerivAt_implicit(_local)`, the same 130 as before;
- exactly 110 changed statement, and all 110 are among the 130;
- the other 20 do not take a generic curve. They fix it (`hyc : ∀ t, arc.yc t = c − t`, or a literal `c − x`,
  `c e^{−x}`, `log(eˣ + c)`, `log(c − eˣ)`) and discharge continuity from the curve's own derivative through
  `hasDerivAt_continuousAt`. Each is a kernel-checked proof of the transparent ε-δ `ContinuousAt` from a true
  (witnessed) axiom, so none is vacuous, and none of the 20 statements changed;
- no theorem outside these 130 uses either axiom;
- the old curve-count statement survives only as the hypothesis of its refutation.

So no theorem still takes the curve identity without continuity and concludes a derivative or a count. Independently of
that bookkeeping, every approved-policy theorem holds at the Q1 model, so none of them can be false.

**The guards.** A script (scratch `guard_check.py`) parsed every theorem with an `hcont` binder in the 16 changed `MachLib/` files:
110 found. For each, it compared the `hcont` guard with the guard of the `hfy` binder before it. All 110 are equal:
- 38 per-arc `∀ arc ∈ (hd :: s), ∀ z, arc.lo < z → z < arc.hi →`;
- 37 `∀ z, arc.lo < z → z < arc.hi →`;
- 32 `∀ z (: Real), a < z → z < b →`;
- 3 pointwise `ContinuousAt yc x` beside a pointwise `hfy : fy ≠ 0`.

The curve in `ContinuousAt` is the curve of the identity (`yc` or `arc.yc`) in every case. Negative control: with one
binder in a scratch copy changed to `∀ z, ContinuousAt yc z`, the script reports `DIFF … total 110 diff 1`.

**Sufficiency.** A guard that is too weak would not compile. One that is too strong compiles, and makes the theorem
weaker. None is too strong: each `hcont` asks continuity exactly where `hf2`/`hfy` already hold, which is where the
derivative is taken. Mathematically, continuity on the open interval plus `HasDerivAt2` there makes `g ∘ yc`
differentiable on every closed sub-interval, which is all Rolle's step needs. The 199 theorems that moved from conditional
to approved are 138 on the bivariate family and 61 on `floor` (CLAUDE.md's estimate said 63: two `floor` users stay
conditional on `HasDerivAt_sqrt`/`arcsin_zero`).

## 5. Transition report and gate mechanics — HOLDS; FINDINGS F4, F5

**Reproduction.** `python3 docs/machsig/transition_2026-10-27.py` in a detached worktree at `1c8cb712` printed
`rows 139 {'restated': 110, 'grew': 20, 'new': 9}; checks C1=ok … C7=ok`. The regenerated JSON's sha256 is
`e767692a…cdc`, equal to the committed one. `git status` was clean afterwards, so the `.md` is byte-identical too.

**Every check can fail.** I ran the script's own source with only the input and output paths substituted, against
mutants of the new baseline or of the probe TSV. The harness asserts that each mutant changes its input. Its first C1
mutant was a no-op (it replaced a token the row did not contain), so I replaced it and record that here. The unmutated
control passes all seven checks; every mutant fails its own check.

| mutant | result |
|---|---|
| C1: a restated theorem's stripped statement differs | C1 fails |
| C1: two `hcont` binders | C1 fails |
| C1: the stripped binder used by the rest | C1 fails |
| C1: an unrelated theorem restated in the baseline | C1 fails |
| C2: `hasDerivAt_implicit` stripped ≠ master's pin | C2 fails |
| C2: a third axiom (`rolle_ct`) restated | C2 fails (and C7, which pins `rolle_ct`) |
| C3: `floor_zero` not admitted / `HasDerivAt_sqrt` admitted too | C3 fails / C3 fails |
| C4: a grew row gains untrusted `HasDerivAt_sqrt` | C4 fails |
| C5: a fake new theorem outside the controls | C5 fails |
| C6: either control Prop's serialization changed | C6 fails (both) |
| C7: a serializer control's pin changed | C7 fails |

**Nothing in the transition is unexplained.**
- 110 restated: C1, plus the guard check in Q4.
- 20 grew: the entered axioms are `hasDerivAt_continuousAt` (all 20) and what the explicit curves' derivatives use
  (`HasDerivAt_add/_mul/_const/_comp/_log_pos/_of_eq`).
- 3 restated rows also grew, by `Classical.choice`, `leR`, `ltR`, `subR`, `propext` and `Quot.sound`. These come from
  `ContinuousAt` entering the statements: `abs` decides `0 ≤ x` classically, and `Classical.em` brings `propext` and
  `Quot.sound`.
- 9 new: the controls module and two helpers.
- Axioms: exactly the two implicit forms restated, none new or gone. Policy: `trusted` +15, `known` and `allowed_sorry`
  unchanged.

**The full gate on a stamped copy.** I made a scratch clone with `origin/master` = `2431d705`, branch at `1c8cb712`, and
the signature set from the main checkout's `artifacts/`. That set is bound to `ee38b6e0`, with sources `b6a2b01b…`
matching the tree.

| run | result |
|---|---|
| unstamped | `REFUSED [baseline-unreviewed]`, rc 3 |
| stamped (REVIEWED; `baseline_sha256` = `--content-digest` = `sha256:69701400…5b72` = the report's `binding.new_baseline_sha256`) and committed | `MACHSIG-TRUST OK`: 9 449 compared; 0 acquired, restated, redefined, removed, violations, axiom-restated, policy-widened. Only advisory: the standalone `MACHSIG_RUN_ID` one |
| the same, `--anchor 2431d705` (the CI judge) | OK |
| after `git merge --no-ff` onto master at `2431d705`, local and `--anchor` | OK; `reviewed_chain` at the merge now returns `sha256:69701400…` "the baseline reviewed at e302e61b" |
| control: a report with one row dropped | `REFUSED [review-report-rows] … 138 theorem row(s) reported, 139 recomputed` |
| control: a stamp with the wrong digest | `REFUSED [review-unbound]` |

The report's `binding.old_baseline_sha256` (`sha256:21b595e8…`) is master's baseline content, and the stamp in master's
baseline names the same digest.

**FINDING F4 (gate, follow-up).** C1 strips the binder NAMED `hcont` whatever its domain says (`strip` tests only the name
and that its conclusion's head is `ContinuousAt`). So C1 proves "old statement plus one continuity binder", not "plus the
RIGHT one". An over-strong `hcont`, for example `∀ z, ContinuousAt yc z`, would pass C1 and the gate. The kernel catches
only one that is too weak. For this change the Q4 guard check closes the gap. For the template's next use, have C1 also
compare the binder's domain with the `hfy` binder's (`Expr`-level), and name the curve.

**FINDING F5 (gate/prose, minor).** The commit says `hypothesis_baseline.json` records the two control Props as a third
kind, REFUTED STATEMENTS, "which must never gain a producer". `hypothesis_audit.py` never reads the new
`_refuted_statements` key. If either Prop gained a producer, which would mean the trusted axioms prove a statement they
refute, the audit would fail (DRIFT, rc 1) with `FIXED … now has a producer — remove it from the baseline`. That message
invites exactly the wrong fix. Teach the audit the key (a producer of a refuted statement is an alarm, never `FIXED`), or
reword the claim. `HYPOTHESIS-AUDIT OK — 35 … exactly the pinned set` on the branch.

## 6. Side effects — HOLDS; FINDING F8

| place | check | result | control |
|---|---|---|---|
| machlib | `lake env lean AxiomLedger.lean` | `AxiomLedger OK: 212 axioms pinned; 112 headline footprints ⊆ trusted (158); … 266 trust-list entries resolved to live axioms` | a copy with `BivariateImplicitControls.OldImplicitStatement` added to `trustedFootprint` FAILS (rc 1): `1 trustedFootprint entr(y/ies) name no live axiom` |
| machlib | gate 13, `soundness_witness_audit.py` | `SOUNDNESS-WITNESS OK — 158 trusted axioms, all accounted, toolchains agree` | `--selftest`: `SELFTEST PASS (7 specimens, 4 perturbations)` |
| machlib | `prose_counts_check.py` | `94 tracked figures match` | — |
| machlib | `check_aggregator.sh` | `823 of 1088 modules reachable` | — |
| machlib | `claim_audit.py` | `CLAIM-AUDIT PASS — all 579 claims resolve against #print axioms`, rc 0 | — |
| machlib | claims on the 139 rows | none of the 579 claims names one; no `forbid_axioms` rule changes verdict | — |
| machlib | files outside the environment (12 documented-unreachable modules, `Discovered/`) | none uses a changed name | — |
| forge | `gen_lean_visible_names.py --check` | `up to date: 2740 names`; `BivariateDeriv` is not in Forge's header, so the two new helpers are not visible | the same check against a copy with `tanh_zero` deleted: `DRIFT: 1 names added`, rc 1 |
| forge | `axiom_statements.py --check` | rc 0, 58 registered, none of the fifteen or the restated two among them | `test_axiom_policy_statements.py` (16 tests, including the "not in trustedFootprint" case) pass |
| forge | `verify_grounding.py --self-test` | `VERIFY-GROUNDING PASS 73`, `canary OK` | — |
| forge, monogate, monogate-lean | `git grep -w` of the 130 changed theorem names | no hits | — |
| monogate.org | Lean-claims registry (`lean_claims.json`, 78 claims) | pins machlib `2431d705` and monogate-lean `cc6abad`; no claimed theorem is a changed or reclassified row; nothing changes until someone re-pins | — |

The forge visible-names check was run through its own `main` with `OUTPUT` pointed at the scratch copy. Forge registers
nothing new; a Forge artifact citing `floor_le` still fails closed until Forge registers it, which it now may, since
`floor_le` is trusted. The only hit for the changed names in the sibling repos is a research roadmap in
`monogate-research`.

**FINDING F8 (mechanics).** Steps for the owner:
1. Record the rulings (F6) and decide F1.
2. Stamp ONLY the `review` block: `status: REVIEWED`, `reviewer`,
   `transition_report: docs/machsig/transition_2026-10-27.json`, and
   `baseline_sha256: sha256:697014002eee4349c648e21a56f16f18c99c3ff08d1fe3ba1b3f5b17b0e85b72`. The digest excludes the
   block, so the report stays valid (simulated above).
3. Run `check_all.sh` once on the stamped tip. The commit message says the hypothesis audit and prose counts were re-run
   separately after a 33-gate run, so no single green run of the final tree exists yet.
4. Merge with `git merge --no-ff`, never squash or rebase: `ee38b6e0` is the baseline's `provenance.machlib_commit`.
5. Push monogate-lean `9979c8b` right after the machlib merge. Neither repository's CI couples them (monogate-lean has no
   CI, and machlib's workflows do not run gate 13), but a clone pair at the two GitHub masters is inconsistent in
   between:
   - machlib first: gate 13 finds the fifteen trusted axioms unaccounted;
   - monogate-lean first: its bridge fails on both implicit axioms, because the restated witnesses do not inhabit the old
     types (the Q1 control).
6. A future re-pin of monogate.org's registry past monogate-lean `9979c8b` must move its machlib source pin to the merge
   at the same time.
7. If master moves before the merge, rerun regen, `--update` and the script (update `OLD_REV`), and re-review the delta.

## 7. Other — FINDINGS F2, F6, F7

### F2 — two FALSE axioms in the environment (soundness, pre-existing, follow-up)

The same family as this change's finding: an axiom whose hypothesis was written in prose and not in its type.
- `interval_scale_unit_lit_le {k} (hk_pos : 0 < k) (hk_lit_le_one : 0 < k) : k ≤ 1` (`Forge.lean:550`). Its second
  hypothesis repeats the first. The docstring's condition ("only when `k` is statically known ≤ 1") is nowhere in the
  type. At `k = 1 + 1` it says `1 + 1 ≤ 1`.
- `interval_weight_sum_le {j k} : 0 < j → 0 < k → j ≤ 1 → k ≤ 1 → j + k ≤ 1` (`Forge.lean:579`). At `j = k = 1` it says
  `1 + 1 ≤ 1`.

Scratch `interval_scale_unit_lit_le_false : False` and `interval_weight_sum_le_false : False` compile, each with its axiom
in its footprint. Both axioms are untrusted. Each has 2 conditional dependents (`ForgeTest.lean`), which are therefore
vacuous. Neither is in Forge's registry, and Forge emits neither. Forge's `lean_visible_names.py` lists them only as
names. Fix in a later change: delete them, or state the real hypothesis, which makes them trivial.

**Everything else I could find holds.** I read all 180 `MachLib.*` axiom types for the shape the brief names, an axiom
about "the" solution, inverse, branch or curve that does not pin which one. Each of the following holds at the bridge's
reading, and each one that defines a branch pins it:
- `sqrt`: `sqrt_sq_nonneg` and the two order laws pin the principal root; `sqrt_neg_zero` sends negatives to 0.
- `arccos`: `cos_arccos` with `arccos_nonneg`/`arccos_le_pi`.
- `arcsin`: `sin_arcsin`, `arcsin_zero` and the positive derivative.
- `atan`, `arctan`, `atan2`: values and bounds only.
- `lambertW`: values at 0 and 1 only. The real branch at 1 is unique.
- `log`: a definition through `exp_surj` with `exp` injective.
- `exists_unique_root_of_deriv_pos`: a theorem, with uniqueness by strict monotonicity.
- `eml_tree_analytic_on_interval` and `eml_tree_analytic_on_pos`: they carry the log-argument positivity they need.

### F6 — the approval of the policy widening is not recorded (process, owner's ruling)

The fifteen admissions are justified in the commit message and CLAUDE.md as "on the owner's approval of 2026-10-27 (asked
in the session that made the change)". No rulings file records it. `OWNER_RULINGS_2026-10-27.md` covers the 2026-10-26
rebaseline only. The two earlier rebaselines put the owner's rulings in a file that the stamp's `review.rulings` cites.
Record this one the same way, per axiom, together with F1's decision, before the stamp.

### F7 — stale or misleading prose (fix a-c with the merge; the rest optional)

- **a.** monogate-lean `AxiomWitnessBridge.lean`, above the 13 new registry entries: "None of these is in machlib's
  `trustedFootprint` yet; the witnesses come first, the trust decision after." False since `ee38b6e0`.
- **b.** `BivariateDeriv.lean`'s module docstring: "the arc `yc` exists and is unique in-model (`exists_unique_root`, from
  `sup_exists`), and is differentiable with the right derivative by these bridges". The `hasDerivAt_implicit` docstring
  says "Existence + uniqueness of `yc` are in-model via `exists_unique_root`; this axiom is only the derivative." Both
  read as if the in-model root supplies everything. It gives a root at each point. Nothing in the corpus proves the root
  curve continuous, and the derivative now needs that.
- **c.** `hasDerivAt_implicit_local`'s docstring: "Strictly weaker than `hasDerivAt_implicit` … so this does not replace
  it". Its HYPOTHESIS is weaker. As a statement it is stronger: it implies the global form (F1).
- **d.** CLAUDE.md, "Five derivable axioms proved": "Still conditional, and not derivable from the trusted axioms as far
  as checked: the `HasDerivAt2*` family and `hasDerivAt_implicit` … `floor` (63)". The sentence after it updates the
  status, but `hasDerivAt_implicit` and `HasDerivAt2_sub` are derivable (F1), and 61, not 63, `floor` users moved.
- **e.** CLAUDE.md, "How to run the gates": `lake env lean AxiomLedger.lean  # "217 axioms pinned; …"`. The run prints
  212. This is pre-existing, and no prose-counts entry covers it.
- **f.** The prose says a step inside `(p, q)` "refuted the old statement just as it refuted the global one" (the local
  axiom's docstring, CLAUDE.md), but no Lean theorem refutes the old local form. The ten-line implication in scratch
  (`old_local_implies_old_global`, `old_local_inconsistent`) could join the controls module.
- **g.** The CHANGELOG has no entry for this change or for 2026-10-26, only the `floor` erratum (correct as written). The
  last dated entry is 2026-09-08. monogate-research's `roadmap/multivariate-khovanskii-chainN-scoping.md` still describes
  the old statements as closing the IFT gate. Both are historical and optional.

Checked and correct: README's and `Numbers.tsx`'s figures and dates (2026-10-27), `what_is_proven.md`'s counts and the
`floor` paragraph, the regenerated AXIOM_MANIFEST, the SELF_ASSESSMENT figures, and the CLAUDE.md arithmetic. On that
arithmetic: 327 conditional + 3 new conditional (two controls and `hd2_quad`) = 330; trusting the fifteen frees 202 (199
old + 3 new), leaving 128.

## Recommendation

**Accept with changes.**
- The restated axioms are true at a faithful interpretation, proved by `implicit_deriv_core` with no gap, and the trusted
  set has one model.
- The refutations refute exactly master's statements, by two independent instruments.
- All 110 restatements add continuity exactly where the derivative is taken, and the other 20 users discharge it
  non-vacuously.
- The transition report reproduces byte for byte, its seven checks each fail under a mutant, and a stamped copy passes
  the full gate before and after a `--no-ff` merge, with negative controls refused.

Before the stamp, the owner's rulings:
- **F1:** convert `hasDerivAt_implicit` and `HasDerivAt2_sub` now, or trust them and convert next;
- **F6:** record the approval of all fifteen.

With the merge: **F7a-c**, and a single green `check_all.sh` on the stamped tip (F8).

Follow-ups: **F2** (the two false interval axioms), **F3** (agreement checks for the bridge's fiat readings of
definitions), **F4** (C1 should pin the binder's domain), **F5** (the refuted-statements key), **F1's**
`HasDerivAt_of_eq` and Forge's reason for registering it.

## Scratch evidence

All under `/tmp/claude-1000/-home-monogate/1e310cfa-129e-41fe-bf8e-88a49f35db3d/scratchpad/review2/`:

| file | for |
|---|---|
| `axiom_dump.lean`, `axioms.tsv`, `axioms_annot.tsv` | every axiom with its type and trust (Q1, Q2, Q7) |
| `theorem_ledger_branch.json`, `ledger_branch.out`, `ledger_diff.py` | Q4 |
| `bridge_controls.lean`, `bridge_controls.out`, `witness_fp.lean` | Q1, Q3 |
| `c6_independent.lean` | Q3 |
| `statement_probe_rerun.lean`, `statement_probe_rerun.tsv` | Q3, Q5 |
| `guard_check.py`, `guard_check_wt.py` | Q4 |
| `c_mutation_harness.py` | Q5 |
| `gate_*.out` | Q5 |
| `AxiomLedger_mut.lean`, `axiomledger*.out`, `claim_audit.out` | Q6 |
| `scratch_refutations.lean` | F2, F7f |
| `implicit_derivable.lean`, `more_derivable.lean` | F1 |
| `log_fiat_machlib.lean`, `log_fiat_bridge.lean` | F3 |
