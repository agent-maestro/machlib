# Gate 14: the owner's rulings on the implicit-function rebaseline (2026-10-27)

The owner ruled on 2026-10-27 in the session that made the change, answering questions put to them there. This file
records the answers. The REVIEWED stamp in `tools/machsig/trust_baseline.json` cites this file, the independent review
(`INDEPENDENT_REVIEW_2026-10-27.md`) and the transition report it binds (`transition_2026-10-27.json`). It is the
second rulings file of the day; `OWNER_RULINGS_2026-10-27.md` covers the five-axiom rebaseline of 2026-10-26.

The change: `hasDerivAt_implicit` and `hasDerivAt_implicit_local` asked nothing of the curve `yc` but the curve
identity, and were false (`BivariateImplicitControls` derives `False` from each old statement; monogate-lean refutes the
old global form in Mathlib's `ℝ`). Both were restated with `ContinuousAt yc x`, and every theorem that passed the curve
identity on gained an `hcont` hypothesis.

## Rulings

| id | question | ruling |
|---|---|---|
| T1 | Admit `HasDerivAt2`, its eight rules and both implicit forms AS RESTATED (eleven axioms) to `trustedFootprint`? Each is witnessed in monogate-lean (`HasDerivAt2` read as Mathlib's `HasFDerivAt` of `(a, b) ↦ f a b`). | **TRUST ALL ELEVEN.** Asked before the review. |
| T2 | Admit `floor`, `floor_le`, `lt_floor_add_one` and `floor_zero`, witnessed by Mathlib's `Int.floor` cast to `ℝ`? | **TRUST FLOOR.** Asked before the review. |
| F1 | The review found two of the fifteen derivable from the others: `hasDerivAt_implicit` (from `hasDerivAt_implicit_local` on `(x − 1, x + 1)`) and `HasDerivAt2_sub` (from `_add`, `_mul`, `_const` and field algebra). Convert them in this rebaseline, or trust all fifteen and convert later? | **CONVERT BOTH NOW.** Both are theorems of the same name and type; thirteen axioms join `trustedFootprint` (143 -> 156) and the pinned count goes 212 -> 210. Their monogate-lean witnesses are retired. |
| F2 | The review found two false axioms outside this change, `interval_scale_unit_lit_le` and `interval_weight_sum_le` (`Forge.lean`; untrusted; two `ForgeTest` theorems rest on them). Fix here or separately? | **A SEPARATE CHANGE RIGHT AFTER THIS ONE.** |
| S | Accept the rebaseline (with the review's changes: this file, its prose items, the hypothesis-audit gap, one full green `check_all.sh` on the stamped tip), stamped REVIEWED with the owner as reviewer; push, open the pull request, merge with a merge commit (`--no-ff`) once its checks pass; then push monogate-lean and re-pin monogate.org's claims? | **ACCEPTED; MERGE AFTER CI.** |

## The review's other findings, and what was done

| id | finding | outcome |
|---|---|---|
| F3 | The bridge interprets MachLib definitions it meets in axiom types (`ContinuousAt`, `abs`, `log`) by assumption; only `natCast` and `realOfScientific` are checked against their definitions, and MachLib's totalised `log` disagrees with Mathlib's `Real.log` on negatives. No trusted axiom is affected. | Follow-up: agreement checks for `ContinuousAt`, `abs` and `log` in monogate-lean. |
| F4 | C1 strips the binder named `hcont` without comparing its interval guard with its `hfy` binder's, so an over-strong guard would pass. The review checked all 110 guards separately. | Follow-up: a future transition template compares the guard too. |
| F5 | `hypothesis_audit.py` did not read `_refuted_statements`, so a refuted statement gaining a producer would have read as a fix. | Fixed: it reports `REFUTED-BUT-PRODUCED` instead, and canary 8 shows it fires (a mutant disabling the branch fails the self-test). |
| F7 | Prose: (a) a stale "not trusted yet" comment in monogate-lean's bridge; (b) `BivariateDeriv` and `TwoExpCurveCount` implied `exists_unique_root` supplies the curve's continuity; (c) the local form was called "strictly weaker" though as a statement it is the stronger; and minor items in CLAUDE.md. Optional: a Lean refutation of the old local form. | Fixed, including the optional one: `implicit_local_without_continuity_inconsistent`. |
| F8 | Merge mechanics: stamp only the `review` block; run `check_all.sh` on the stamped tip; merge `--no-ff`; push monogate-lean right after, since a clone pair at the two GitHub masters is inconsistent in either order until both land. | Followed. |
| — | `HasDerivAt_of_eq` (1323 users, registered in Forge's axiom policy) follows from `funext` alone. | Follow-up, with Forge's policy registry. |
