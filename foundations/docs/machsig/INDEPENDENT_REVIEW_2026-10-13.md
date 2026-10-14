# MachSig gate 14: independent review of the candidate baseline (steps 5 and 6)

> Copied into the repository on 2026-10-14 for the step-7 landing, which this review's stamp cites. Verbatim except that local paths are redacted: `<scratchpad>` is the reviewer's private working directory, not part of this repository.

Written 2026-10-13 by an independent review agent (Claude), not the agent that built the repair. I didn't rely on the repair agent's conclusions, tools or build products. I made my own clones, ran my own cold builds and wrote my own Lean extractor and scripts. The only commits were made in a throwaway clone for the gate attacks (`<scratchpad>/gate-attack`, with its origin remote removed). Nothing was pushed, and none of the shared worktrees, the main MachLib checkout or Forge was modified. Review time: 20:28 to 21:04 PDT (36 minutes).

Subject: branch `machsig-gate` at `b6ad5d05`, candidate `docs/machsig/trust_baseline.candidate-2026-10-13.json` (sha256 `6ed24033…`, 7,948 theorems, derived from `fb806c09`, Lean sources equal to master `c3046961`), against the 2026-09-03 baseline committed at `23e0d047`.

## 0. Verdict

**Candidate baseline: ACCEPT EXCEPT E1–E3.** Do not stamp it REVIEWED until the owner rules on E1–E3. None of them needs the candidate's bytes to change unless the owner rejects one. Rejecting E3 means reverting the clamp change. Rejecting E1 in a way that removes `pi_lower_bound` from 181 footprints means re-proving `pi_pos`/`pi_gt_one` without it. Either case changes the sources, so it would need a new candidate and a new transition report.

* The candidate is an accurate record of `c3046961`. I reproduced it independently: 7,948 of 7,948 axiom sets match both `Lean.collectAxioms` and `#print axioms` in my own cold build. Its bytes are exactly `trust_gate.py --update` applied to the evidence signature set.
* Every one of the 4,317 transitions is reproduced exactly, row by row, and attributed to a commit window by building two intermediate revisions:
  * 3,801 changed only in the three 2026-10-04 commits: 3,760 by the discharge mechanism itself and 41 by proofs those commits rewrote;
  * 32 changed in those commits and again in `203cc854` (owner option (b));
  * 2 restatements come from `9802f19e` (clamp);
  * the 2 removals come from `e7b91de7` and `5841ea60`;
  * the 480 new theorems are recorded as they are.
* **No REJECT.** No sorryAx, compiler-trust or undeclared axiom moved anywhere, in any scope. The only sorry is `MachLib.Real.halve_in_unit_sorry`, on both sides.
* **One headline claim is true only relative to the new policy.** The packet says "no conditional axiom entered any footprint". That holds because `transition.py` classes ENTERED axioms under the NEW policy. Under the 2026-09-03 policy, `MachLib.Real.pi_lower_bound` was conditional, and it entered **181** existing footprints (see E1). It was moved into `trustedFootprint` in the same commit that made it enter (5841ea60), and no owner ruling for that promotion was found.
* **The gate on its own is weaker evidence than its docs suggest** (section 4). Three gaps remain:
  * a REVIEWED stamp is not bound to the baseline it stamps;
  * a footprint growth passes if the statement digest also changes or the theorem leaves the watched set;
  * an axiom restated under the same name is invisible, and 16 were restated in this window.

  The CI proposal itself is mechanically correct.

Counts by sign-off outcome (all rows of section 2): **ACCEPT 76, ACCEPT-WITH-NOTE 10, ESCALATE-TO-OWNER 5, REJECT 0.**

## 1. What I reproduced, independently

Setup:

* Fresh `git clone`s of the MachLib repository (its main checkout) under `<scratchpad>` (`mlrev-old` at `23e0d047`, `mlrev-new` at `c3046961`, `mlrev-mid` at `9bfe0380` then `2d2f59c0`). Each had a cold `lake build MachLib`: 788 or 828 jobs, about 2.3 min each.
* My extractor, `review/rv_extract.lean`, was written from scratch. For every theorem it records the `collectAxioms` set and a structural serialization of the stored type. Unlike MachSig's `ser`, mine keeps universe levels and binder info.
* A full `#print axioms` sweep over every watched theorem at both ends.
* My own Python for the transition, mechanism, policy and attribution. Scripts and outputs are in `<scratchpad>/review/`.

| repair agent's claim | my result |
|---|---|
| watched population 7,470 → 7,948 | identical name sets: `MachLib.*` theorems, not internal, not matching the substring filter |
| 2026-09-03 baseline rebuilt byte-identically | not re-run with the old tool chain. The committed file (sha `cc859678…`) equals the evidence copy. All 7,470 names and axiom counts equal my fresh 23e0d047 extraction and `#print axioms`. The 'd' digests change for exactly the 2 theorems my serialization flags. |
| candidate = new side | 7,948/7,948 sets equal my `collectAxioms` and `#print axioms` at c3046961. The file is byte-identical to `--update` of `sigs_new.jsonl`. |
| grew 1816 / shrank 1642 / swap 375 / restated 2 / new 480 / removed 2 / unchanged 3633 | **identical**, 0 row disagreements. No statement change is invisible to MachSig's digest: 0 binder-info-only and 0 universe-only changes. |
| 0 extractor-caused changes | supported: an extractor sharing no code with MachSig gives the same transition |
| 39 axioms became theorems/defs on 2026-10-04 in 5841ea60 / 2d2f59c0 / e25e0cd1 | **confirmed from `git show`.** `-axiom` lines: 23 + 7 + 9 = 39. `tan_def` was only moved, and `count` is a docstring false positive. The 39 equal exactly the set of axioms at 23e0d047 that are not axioms at c3046961: 36 are theorems now, 3 are defs (`natCast`, `realOfScientific`, `exp10`). |
| 3,761 of 3,835 explained, 74 not | **identical sets.** A stronger test also holds for all 3,761: new footprint = (old − discharged) ∪ ⋃ footprint(new proof of each discharged axiom used), so nothing else moved. |
| 869 groups in C2 | identical partition |
| 119 conditional→approved, 0 approved→conditional | confirmed with my own parse of `AxiomLedger.lean` at both revisions (243/149 → 217/143). 116 are real discharges. **3 are pure policy promotions** (realPow ×2, pi_lower_bound ×1). |
| no conditional axiom entered; 11 left (342 departures) | 11/342 confirmed. "None entered" holds under the new policy only. Under the 0903 policy, `pi_lower_bound` entered 181 (E1). |
| no post-0903 axiom entered an existing theorem | confirmed, because the 13 new axioms are used by **no** watched theorem at all (section 5) |
| "the 10 growths all sit in OperatorBasisGeneral.lean" (GATE14_REPAIR.md:55) | **wrong in the prose, right in the data.** 6 are in OperatorBasisGeneral and 4 (`aerr_ln`, `aerr_pow`, `ln_step`, `ln_lipschitz_bound`) in OperatorBasisComplete. All 10 come from 203cc854, as verified below. The doc needs fixing. |

**Attribution by intermediate builds.** I extracted at `9bfe0380` (last Lean-source commit before the 2026-10-04 commits) and at `2d2f59c0` (after them; MachLib sources are byte-identical to `203cc854^`):

* 3,760 of the C2 changes moved **only** between 9bfe0380 and 2d2f59c0, the three discharge commits.
* Of the 74 unexplained changes:
  * 41 moved only in that window. These are the proofs those commits rewrote, for example `natCast_mul` re-proved in Basic.lean.
  * 32 moved in that window **and** in 203cc854.
  * 1 (`lo_le_clamp`) moved in September.
* `clamp_le_hi` and the `div_one_eq` move fall in September; `mul_succ_eq` falls in the discharge window.
* 203cc854's window changed **exactly 32** footprints and restated nothing:
  * 22 lost only `one_add_le_exp`;
  * 6 traded it for `rolle_ct`, `HasDerivAt`, `_add`, `_const`, `_exp`, `_id`, `_mul`, `_of_eq` and `_unique`;
  * 4 traded it for `HasDerivAt_exp`.
* It added 4 theorems, none of which uses `one_add_le_exp` or sorry. `one_add_le_exp_of_mvt`'s stored type is Expr-identical to the axiom's, universe levels included. `one_add_le_exp` is still an `axiom`. This matches the 203cc854 message and the owner's option (b).
* All nine entering axioms are in `trustedFootprint` at **both** revisions (no promotion) and are registered in Forge's `software/verification/axiom_policy.py`. Forge's `tools/proof_discharge_baseline.json` is bound to `machlib_sources sha256:261f3d99…`, the candidate's sources.
* c3046961's 10 hand edits to the old baseline equal the extraction exactly: 6 re-pinned and 4 added. The candidate supersedes them.
* All 39 discharged axioms' new proofs rest only on axioms trusted under the new policy. Under the old policy, only `pi_lower_bound` was outside it, through `pi_pos`, `pi_gt_one` and `pi_gt_three`.

## 2. Sign-off table

### A. Removals (2)

| id | theorem | outcome | reason |
|---|---|---|---|
| A1 | `MachLib.div_one_eq` → `MachLib.Real.div_one_eq` | **ACCEPT** | A pure move (e7b91de7, MachLib/EMLRationalGerm → FieldLemmas). The stored types are identical, universe levels and binder info included, and the footprints are the same 13 axioms. No tracked file in MachLib, Forge (any worktree) or monogate-lean names the old fully-qualified `MachLib.div_one_eq`. Forge's emitter uses bare `div_one_eq`, which resolves to the new name, and Forge's proofs are bound to these sources. |
| A2 | `MachLib.Real.mul_succ_eq` (`x*y + x = x*(y+1)`) | **ACCEPT** | Deleted in 5841ea60 as an orphaned helper. Its only user at 23e0d047 was `natCast_mul` (Decimal.lean:75). 5841ea60 moved `natCast_mul` to Basic.lean, re-proved it with `mul_distrib, mul_one_ax` (Basic cannot use `mach_mpoly`), and kept its statement. Nothing at c3046961 references the name except the old baseline JSON: no MachLib .lean or claims file, nothing in Forge (all worktrees) or monogate-lean. No watched theorem holds the same statement. It is a trivial ring identity, so nothing is lost. |

### B. Restatements (2), both from 9802f19e "clamp is max lo (min x hi)"

What changed is the **definition**: `clamp x lo hi := min (max x lo) hi` became `max lo (min x hi)`. The two agree whenever `lo ≤ hi`. When `lo > hi`, the old form returns `hi` and the new one returns `lo`. The hypothesis had to move with it:

* **old `clamp_le_hi`** (unconditional) was true of the old definition, and would be **false** of the new one for `lo > hi`;
* **old `lo_le_clamp`** needed `lo ≤ hi` under the old definition; the new one is unconditional and true.

Both new statements are proved, so both are true of the new definition.

The new definition matches Forge everywhere I checked:

* `docs/language-reference.md` §`clamp`;
* `docs/FIXED_POINT_SEMANTICS.md` ("max(lo, min(x, hi)), also when lo > hi (then it is lo)");
* `lang/numerics/fixed_point_semantics.clamp`;
* `lang/numerics/evaldag.py`;
* `lang/profiler/eml_interpreter.py` (`ieee_clamp`);
* `tests/test_fixed_point_semantics.py::test_clamp_is_max_of_lo_and_min_of_x_and_hi_even_when_lo_exceeds_hi`;
* `LeanBackend.py`, which emits `(max lo (min x hi))`.

Who relied on the stronger, unconditional `clamp_le_hi`:

* **Forge's Lean emitter**, whose bare `apply clamp_le_hi` arm stalled. That arm is fixed on master: `(apply clamp_le_hi <;> (first | assumption | mach_positivity))`, with an `h_clamp : lo ≤ hi` hypothesis emitted for every clamp. The census was 137/137 before and after.
* **Stale copies of the bare arm** remain only in **untracked** generated output (`forge/reproduce/out/**`, `forge/build/audit_sweep/**`). Those would not re-check against today's MachLib, but they are not tracked.
* **In MachLib**, the four call sites (`OperatorBasisGeneral:205`, `FixedPointCertifier:99`, `AntiWindupPITracking:341`, `Forge.lean` doc) supply `hlohi`. The tree builds.

| id | theorem | outcome | reason |
|---|---|---|---|
| B1 | `MachLib.Real.clamp_le_hi` (GAINED `lo ≤ hi`, weaker) | **ESCALATE-TO-OWNER** (recommend accept) | It now says less, and Forge relied on the old form. The change was forced by aligning MachLib's clamp with the language definition, which I verified. Every reliance I could find was updated. The owner rules on behaviour someone may have relied on. |
| B2 | `MachLib.Real.lo_le_clamp` (LOST `lo ≤ hi`, stronger; `lt_total` left) | **ACCEPT-WITH-NOTE** | It is stronger, so no caller can break. `lt_total` left because the proof is now `le_max_left`. The note: it is a statement about a different function when `lo > hi` (see E3). |

### E. Escalations that are not a single packet row

| id | item | outcome | reason |
|---|---|---|---|
| E1 | `MachLib.Real.pi_lower_bound` (`3.141592 < π`) joined `trustedFootprint` in 5841ea60 | **ESCALATE-TO-OWNER** (recommend ratify) | A **trust increase**. On 2026-09-03 this axiom was conditional. 5841ea60 proved `pi_pos`, `pi_gt_one` and `pi_gt_three` from it and added it to the trusted list in the same commit; I found no owner ruling for the promotion. CLAUDE.md:240 and the commit message record it as the agent's decision, inside the owner's "provable ⇒ proved" ruling. It **entered 181 existing watched footprints**: 178 in C2, 3 in C1. In 174 of them it replaced the weaker trusted facts `π > 0`/`π > 1`, and in 7 the conditional `π > 3`. Watched theorems resting on it: 3 → 187. The packet reports all of them as `assumption-foundation`, because entered axioms are classed under the new policy. The risk is low (the statement is true, and monogate-lean witnesses it with Mathlib's `Real.pi_gt_d6`), but it is a policy decision. |
| E2 | `MachLib.Real.realPow`, `realPow_nonneg` joined `trustedFootprint` in e25e0cd1 | **ESCALATE-TO-OWNER** (recommend ratify) | A trust increase. The commit cites "the owner's axiom audit (2026-10-04)"; I could not find the text of that ruling to verify. Effect on the baseline: 2 watched theorems (`HighDimensional.eml_first_layer_log_domain_survival_decay`, `firstLayerSurvival_decay`) went conditional→approved by policy alone; their footprints barely changed (5→6). |
| E3 | Silent meaning change: the `clamp` definition (9802f19e) | **ESCALATE-TO-OWNER** (recommend accept) | The statement digest hashes the TYPE, so a changed **definition** is invisible. 32 watched theorems' statements reach `MachLib.Real.clamp` directly or through definitions, but only 2 were flagged as restated. Among the other 30 are `clamp_lipschitz`, `clamp_abs_le`, `pid_fx_fwd_error`, `pid_q16_fwd_error`, `forge_clamp_sq_certified`, `aerr_clamp`, `fxerr_clamp`, `nonlinear_drift_clamp_safe` and `two_mode_clamp_envelope`. They now describe the language's clamp, and the old function only where `lo ≤ hi`. Every one is proved for the new definition. Anything published before 2026-09-22 that cites them describes the old function for inverted bands; I did not audit external publications. The other definition changes I found are benign: `natCast`, `realOfScientific` and `exp10` went from axiom to def, consistent with their old characterizing axioms (842 / 86 / 1 statements). `pconsN`, `polyIsZeroConst`/`OneConst`, `normalizeCoeff`, `insertUniqueRoot` and `multiIs*Const` have unchanged source; their elaborated `Decidable (c = 0)` instance switched to the new classical `instDecEq` (40add282), which leaves the value unchanged. |
| E4 | Gate 14 as evidence for step 7 | **ESCALATE-TO-OWNER** | This does not concern the baseline's contents. Section 4: a growth passes the gate if the statement digest also changes or the theorem leaves the watched set; the REVIEWED stamp can be copied onto any `--update` output; axiom statements are not pinned (16 were restated in this window); and the population leaves out 301 Certcom, 65 filtered and 39 root-namespace hand-written theorems. Decide which to close before CI green is cited as evidence. |

### C1. The 73 individually listed assumption changes (packet order)

The rows fall into two mechanisms, each verified by the intermediate builds:

* **203cc854** (owner ruling of 2026-10-11, option (b)): 32 rows. 6 grew by the derived tangent line's 9 calculus axioms, 4 grew by `HasDerivAt_exp`, and 22 shrank by `one_add_le_exp`.
* **The 2026-10-04 commits re-proving a dependency**: 41 rows, of which 40 shrank and 1 is a swap (`decimal_scaled`). In each, only trusted or standard axioms left, and anything that entered is covered by a discharged axiom's new proof. 3 of these 41 gained `pi_lower_bound` (E1).

None of the 73 involves sorry or an undeclared axiom, and none moved a conditional axiom in. 7 C1 rows lost a conditional axiom (`realOfScientific*`).

| row | theorem | kind | module | ax | outcome | reason |
|---|---|---|---|---|---|---|
| C1.1 | `R.aerr_exp` | grew | OperatorBasisGeneral | 35→44 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out; rolle_ct + 8 HasDerivAt rules in (trusted 0903 and now; in Forge policy); rest = 10-04 discharges |
| C1.2 | `R.aerr_exp_upper` | grew | OperatorBasisGeneral | 35→44 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out; rolle_ct + 8 HasDerivAt rules in (trusted 0903 and now; in Forge policy); rest = 10-04 discharges |
| C1.3 | `R.aerr_ln` | grew | OperatorBasisComplete | 37→45 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out; rolle_ct + 8 HasDerivAt rules in (trusted 0903 and now; in Forge policy); rest = 10-04 discharges |
| C1.4 | `R.aerr_pow` | grew | OperatorBasisComplete | 42→46 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out; rolle_ct + 8 HasDerivAt rules in (trusted 0903 and now; in Forge policy); rest = 10-04 discharges |
| C1.5 | `R.aexpr_fwd_error` | grew | OperatorBasisGeneral | 47→49 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out, HasDerivAt_exp in (trusted); rest = 10-04 discharges |
| C1.6 | `R.aexpr_sound` | grew | OperatorBasisGeneral | 47→49 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out, HasDerivAt_exp in (trusted); rest = 10-04 discharges |
| C1.7 | `R.cos_sq_mixed_via_meta` | grew | OperatorBasisGeneral | 47→49 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out, HasDerivAt_exp in (trusted); rest = 10-04 discharges |
| C1.8 | `R.exp_sq_via_meta` | grew | OperatorBasisGeneral | 47→49 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out, HasDerivAt_exp in (trusted); rest = 10-04 discharges |
| C1.9 | `R.ln_lipschitz_bound` | grew | OperatorBasisComplete | 37→45 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out; rolle_ct + 8 HasDerivAt rules in (trusted 0903 and now; in Forge policy); rest = 10-04 discharges |
| C1.10 | `R.ln_step` | grew | OperatorBasisComplete | 37→45 | **ACCEPT** | owner option (b), 203cc854: one_add_le_exp out; rolle_ct + 8 HasDerivAt rules in (trusted 0903 and now; in Forge policy); rest = 10-04 discharges |
| C1.11 | `R.decimal_scaled` | swap | Decimal | 24→24 | **ACCEPT** | 5841ea60 realOfScientific becomes a def; out Classical.choice, Quot.sound, add_comm, subR, sub_def (trusted/std), in add_lt_add_left, divR, div_def, leR, le_iff_lt_or_eq, ltR, lt_irrefl_ax, lt_trans_ax, mul_inv, zero_lt_one_ax = realOfScientific_clears proof; all trusted |
| C1.12 | `R.bcRatio_even_le` | shrank | BallCubeRatio | 38→32 | **ACCEPT-WITH-NOTE** | 10-04 proof changes (live trusted/std out: Classical.choice, subR, sub_def); entered lt_total, pi_lower_bound, zero_ne_one_ax; pi_lower_bound arrived via pi_pos discharge, see E1 |
| C1.13 | `R.bcRatio_factor_le_half` | shrank | BallCubeRatio | 37→31 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, subR, sub_def); entered lt_total, zero_ne_one_ax (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.14 | `R.bcRatio_odd_le` | shrank | BallCubeRatio | 38→32 | **ACCEPT-WITH-NOTE** | 10-04 proof changes (live trusted/std out: Classical.choice, subR, sub_def); entered lt_total, pi_lower_bound, zero_ne_one_ax; pi_lower_bound arrived via pi_pos discharge, see E1 |
| C1.15 | `R.bcRatio_step_le` | shrank | BallCubeRatio | 38→32 | **ACCEPT-WITH-NOTE** | 10-04 proof changes (live trusted/std out: Classical.choice, subR, sub_def); entered lt_total, pi_lower_bound, zero_ne_one_ax; pi_lower_bound arrived via pi_pos discharge, see E1 |
| C1.16 | `R.decimal_add_same` | shrank | Decimal | 28→23 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); entered div_def (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.17 | `R.decimal_normalize` | shrank | Decimal | 33→25 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, subR, sub_def); entered div_def (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.18 | `R.eight_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.19 | `R.five_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.20 | `R.forge_abs_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.21 | `R.forge_atan_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.22 | `R.forge_clamp_sq_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.23 | `R.forge_cosh_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.24 | `R.forge_deadzone_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.25 | `R.forge_deadzone_cross_target` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.26 | `R.forge_gaussian_tight` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.27 | `R.forge_length_sq2_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.28 | `R.forge_magnitude_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.29 | `R.forge_powerlaw_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.30 | `R.forge_quad_inlined_let_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.31 | `R.forge_sigmoid_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.32 | `R.forge_surprisal_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.33 | `R.forge_tanh_certified` | shrank | ForgeBindingDemo | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.34 | `R.four_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.35 | `R.frac5_15` | shrank | TanhTaylorRemainder | 31→25 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, subR, sub_def); nothing entered; trust decrease |
| C1.36 | `R.fxmul_real_trunc_lt_ulp` | shrank | FixedPointRealBridge | 28→19 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, mul_assoc, mul_comm, subR, sub_def); nothing entered; trust decrease |
| C1.37 | `R.fxmul_real_trunc_nonneg` | shrank | FixedPointRealBridge | 28→19 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, mul_assoc, mul_comm, subR, sub_def); nothing entered; trust decrease |
| C1.38 | `R.fxpid_real_trunc_lt_3ulp` | shrank | FixedPointRealBridge | 28→19 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, mul_assoc, mul_comm, subR, sub_def); nothing entered; trust decrease |
| C1.39 | `R.gexpr_cross_target` | shrank | OperatorBasisComplete | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.40 | `R.gexpr_fwd_error` | shrank | OperatorBasisComplete | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.41 | `R.gexpr_sound` | shrank | OperatorBasisComplete | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.42 | `R.halfPi_rtl_eq` | shrank | AcosHardwareForwardError | 31→24 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, subR, sub_def); nothing entered; trust decrease |
| C1.43 | `R.half_scale_match` | shrank | AcosHardwareForwardError | 31→25 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, subR, sub_def); nothing entered; trust decrease |
| C1.44 | `R.iterated_kernel_trajectory` | shrank | TrajectoryCertified | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.45 | `R.lorentzian_cross_target` | shrank | OperatorBasisComplete | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.46 | `R.lorentzian_via_gfold` | shrank | OperatorBasisComplete | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.47 | `R.meshPoint_double_even` | shrank | RiemannIntegralMonotone | 32→28 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice); nothing entered; trust decrease |
| C1.48 | `R.meshPoint_double_odd_ge` | shrank | RiemannIntegralMonotone | 36→31 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice); entered lt_total (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.49 | `R.meshPoint_double_odd_le` | shrank | RiemannIntegralMonotone | 36→31 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice); entered lt_total (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.50 | `R.meshWidth_double` | shrank | RiemannIntegralMonotone | 32→28 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice); nothing entered; trust decrease |
| C1.51 | `R.natCast_frac_eq` | shrank | TanTaylorRemainder | 31→24 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, subR, sub_def); nothing entered; trust decrease |
| C1.52 | `R.natCast_frac_to_nat` | shrank | TanTaylorRemainder | 31→24 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, subR, sub_def); nothing entered; trust decrease |
| C1.53 | `R.natCast_mul` | shrank | Basic | 22→11 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, add_comm, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.54 | `R.natCast_mul_meshWidth` | shrank | RiemannIntegralContinuous | 26→22 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); nothing entered; trust decrease |
| C1.55 | `R.natCast_ne_zero` | shrank | NatCastArith | 16→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); nothing entered; trust decrease |
| C1.56 | `R.natCast_pos` | shrank | Basic | 15→11 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); nothing entered; trust decrease |
| C1.57 | `R.natCast_succ_pos` | shrank | Basic | 15→11 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); nothing entered; trust decrease |
| C1.58 | `R.natCast_two_pow_frac_pos` | shrank | FixedPointRealBridge | 15→11 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); nothing entered; trust decrease |
| C1.59 | `R.natcast_arith_template_frac_reduce` | shrank | NatCastArith | 31→24 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, subR, sub_def); nothing entered; trust decrease |
| C1.60 | `R.ofSci_zero` | shrank | SignTactic | 30→25 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); entered div_def (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.61 | `R.one_dot_zero_from_clears` | shrank | Decimal | 26→21 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); entered div_def (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.62 | `R.pi_half_hi` | shrank | AcosHardwareForwardError | 36→31 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, subR, sub_def); entered lt_total, mul_pos, zero_ne_one_ax (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.63 | `R.pi_half_lo` | shrank | AcosHardwareForwardError | 36→31 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, subR, sub_def); entered lt_total, mul_pos, zero_ne_one_ax (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.64 | `R.pi_le_four` | shrank | BallCubeRatio | 36→31 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, subR, sub_def); entered lt_total, mul_pos, zero_ne_one_ax (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.65 | `R.rOS_zero` | shrank | SignTactic | 30→25 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); entered div_def (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.66 | `R.ratio_via_gfold` | shrank | OperatorBasisComplete | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.67 | `R.realOfScientific_eq_of_nat` | shrank | Decimal | 33→25 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, add_comm, subR, sub_def); entered div_def (trusted; from the discharged axioms' new proofs); trust decrease |
| C1.68 | `R.scaling_iteration_certified` | shrank | TrajectoryCertified | 77→66 | **ACCEPT** | 203cc854 removed one_add_le_exp (gexpr_sound path); other departures = 10-04 discharges; trust decrease |
| C1.69 | `R.seven_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.70 | `R.six_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.71 | `R.three_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.72 | `R.two_mul_natCast` | shrank | TanTaylorRemainder | 22→12 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (Classical.choice, Quot.sound, mul_assoc, mul_comm, propext, subR, sub_def); nothing entered; trust decrease |
| C1.73 | `R.ulp_scale` | shrank | FixedPointRealBridge | 19→15 | **ACCEPT** | 10-04 commits re-proved a dependency (natCast/realOfScientific now defs); only trusted/std live axioms left (add_comm); nothing entered; trust decrease |

### C2. The 3,760 grouped changes (869 groups), by group class

For every class, all of the following hold:

* every member moved only between 9bfe0380 and 2d2f59c0;
* every axiom that left is one of the 39 discharged in 5841ea60 / 2d2f59c0 / e25e0cd1;
* the exact equation holds: new = (old − D) ∪ ⋃ footprint(proof of d);
* every entered axiom is trusted under the new policy;
* the seed-777 sample agrees (section 3).

My partition into (entered, left) groups is identical to the packet's 869.

| class | size | pi_lower_bound entered | outcome | reason |
|---|---:|---:|---|---|
| grew · assumption-foundation | 1,715 | 76 | **ACCEPT-WITH-NOTE** | Mechanical discharge. A count growth here is a trust *decrease*: an axiom is replaced by its proof's axioms, all already trusted. Note E1 for the 76. |
| grew · assumption-conditional | 91 | 6 | **ACCEPT-WITH-NOTE** | The conditional axioms only LEFT: div_lt_one_of_pos_lt 35, realOfScientific* 107 departures, pi_gt_three 6, lit_zero_eq 2, exp10/exp10_def 1 each, cos_periodic 1. These are real discharges into trusted axioms. Note E1 for the 6. |
| shrank · assumption-foundation | 1,497 | 93 | **ACCEPT-WITH-NOTE** | Mechanical discharge with fewer axioms. Note E1 for the 93. |
| shrank · assumption-conditional | 83 | 1 | **ACCEPT-WITH-NOTE** | The conditional axioms only left (div_lt_one_of_pos_lt 51, realOfScientific* 112 departures, pi_gt_three 1). Note E1 for 1. |
| swap · assumption-foundation | 363 | 2 | **ACCEPT-WITH-NOTE** | The same mechanism with the same count. The old count-only gate could not see these; the set comparison does. Note E1 for 2. |
| swap · assumption-conditional | 11 | 0 | **ACCEPT** | `div_lt_one_of_pos_lt` (conditional) left in all 11, replaced by its proof's trusted axioms. |

### N/P. New theorems and policy moves

| id | item | outcome | reason |
|---|---|---|---|
| N1 | 465 new theorems, approved-policy | **ACCEPT** | Recorded as they are. All footprints are trusted. None uses sorry or any of the 13 axioms added since 0903. Of all 480 new theorems, 436 first appeared in September, 40 in the 10-04 commits and 4 in 203cc854. |
| N2 | 15 new theorems, conditional | **ACCEPT** | Honestly labelled. Conditional on existing declared axioms `Real.floor`/`floor_le`/`lt_floor_add_one` (4, FixedPointPIDLoop), `Real.exp_gt_two_x` (8, EML research) and `eml_tree_analytic_on_interval` (3). |
| P1 | 119 conditional→approved | **ACCEPT-WITH-NOTE** | Confirmed as exactly the agent's 119. 116 are real discharges of a conditional axiom. 3 are policy-only (E1: `pi_half_lo`; E2: 2 realPow theorems). The 10 seed-777 spot checks are in section 3. |
| P2 | 0 approved→conditional | **ACCEPT** | Confirmed from my own tier computation over all 7,470 theorems that exist at both revisions. |

### Overall

| | outcome | reason |
|---|---|---|
| **Overall** | **ACCEPT EXCEPT E1, E2, E3** (+ B1, folded into E3) | The candidate is accurate and every transition is explained. Stamp it REVIEWED only after the owner rules on the three trust or meaning changes that no owner ruling covers. E4 is for step 7, not the baseline. |

Tally: ACCEPT 76 (A 2, C1 70, C2 1, N 2, P 1). ACCEPT-WITH-NOTE 10 (B 1, C1 3, C2 5, P 1). ESCALATE-TO-OWNER 5 (B1, E1, E2, E3, E4). REJECT 0.

## 3. Targeted checks (step 6): seed 777

**Method.**

* I built the classes myself, using the packet's semantics (kind × trust class, with entered axioms classed under the new policy and departed ones under the old), and confirmed the class sizes equal the agent's.
* I added two strata of my own: the 74 changes that discharge does not explain, and the 181 where `pi_lower_bound` entered.
* Sample: `random.Random(777).sample` over each sorted class. 6 per class (all of a class if it is smaller), 10 per stratum, and 20 drawn at random from all 7,950 theorems on either side. That makes 98 distinct theorems.
* For each, I ran `#print axioms` through `lake env lean` in **my** cold-built clones at every revision where the theorem exists.
* The output had to match all of: my `collectAxioms` set; the old baseline's count at 23e0d047; the transition JSON's old set; the candidate's new set; and the kind recomputed from the printed sets. For unchanged controls, both sides had to be identical.

**Result: 98/98 agree, 0 mismatches.**

Beyond the sample, I swept `#print axioms` over **every** watched theorem: old 7,470/7,470 counts match the 0903 baseline, and new 7,948/7,948 sets match the candidate.

| class | checked | agree | sample |
|---|---:|---:|---|
| `grew · assumption-conditional` | 6 | 6 | `R.growthCompetition_hApos_negside`, `R.halve_in_unit_sorry`, `R.log_2_0_lt_1_02`, `R.log_2_2_lt_one`, `R.one_lt_1_02`, `M.not_eventually_K_over_x_one_eml_eml_var_const_eml_const_const` |
| `grew · assumption-foundation` | 6 | 6 | `M.Gaming.SpringCriticallyDamped.spring_critical_positive`, `R.sin_one_recurring`, `M.deepDecay_below_floor`, `M.exact_meeting_gap_zero`, `M.good_positive_chain_pos`, `M.omega_point_exists` |
| `new · new:approved_policy` | 6 | 6 | `R.clamp_sub_between`, `R.qval_nonneg`, `R.toNat_oneVec`, `M.exp_margin_ge`, `M.leftLeaf_recipTree`, `M.rightSpine_ld` |
| `new · new:conditional` | 6 | 6 | `R.fxpidloop_tracks_exact`, `M.compLt_not_wf`, `M.one_query_level_set_two_sided`, `M.pair_route_exits_are_the_conjecture`, `M.peelTerminalNoCancel_iff_growthEnvelope`, `M.peel_terminal_cells_are_the_conjecture` |
| `random-any` | 20 | 20 | `M.ChainExp2Explicit.length_polyCoeffs_mP2PFL_le`, `M.InnerKhovanskiiMod.InnerKhovanskii.zero_count_scaledReduction_transfer_raw`, `M.IterExpDepth3Bridge.dropLastY_prodVarYUpTo`, `M.Model.RealCoreSpec.le_iff_lt_or_eq`, `M.MultiVarMod.pow_pred_mul`, `M.MultiVarMod.reduceStep_vanish_at`, `R.Rtanh6_deriv`, `R.hAsin_zero`, `R.hD_hAsinPow`, `R.no_tree_eq_log_positive_side_given_validon_via_barrier`, `R.size_domTree`, `R.sqrt_diff_mul`, `R.sum_step_slack`, `R.two_lt_u3PointS`, `M.bimul_concat`, `M.floorHeight_of_deepDecay`, `M.hasDerivAt_of_agrees_off_finite`, `M.iter_exp_tree_depth`, `M.one_hole_level_is_affine`, `M.pev_pnsum` |
| `removed · removed:approved_policy` | 2 | 2 | `R.mul_succ_eq`, `M.div_one_eq` |
| `restated · assumption-foundation` | 1 | 1 | `R.lo_le_clamp` |
| `restated · no-axiom-change` | 1 | 1 | `R.clamp_le_hi` |
| `shrank · assumption-conditional` | 6 | 6 | `R.Rasin7_bound`, `R.eml_acos_full_fwd_error`, `R.growthCompetition_quad_neg_2_3`, `M.depth_le_two_growth_ceiling`, `M.inv_x_size_nine_isPath`, `M.not_eventually_K_over_x_one_eml_eml_const_var_eml_var_var` |
| `shrank · assumption-foundation` | 6 | 6 | `M.EMLExplicitBound.log_step_general_explicit`, `M.MultiVarMod.TwoExp.Chain2DescentPackage.genericCertificate`, `R.eml_atan_fx_vs_acc_exact`, `R.habs24th_le1`, `R.upperSumCont_const_eq`, `M.bipevE_logArgPos` |
| `stratum:pi_lower_bound-entered` | 10 | 10 | `R.cos_piQuarter_pos`, `R.eml_depth2_witness_of_const_gt_one_sibling_right_children_everywhere_positive`, `R.gaussianMeanSymInt_tendsto_zero`, `R.no_tree_eq_nested_target_of_BChainOrPositive`, `R.x_mul_sin_not_tailSign`, `M.cos_zeros_list_nodup`, `M.eml_depth2_witness_of_const_sibling_trivial_via_cont58`, `M.no_T1_with_simple_right_children`, `M.sin_not_in_eml_t1_var_t2_eml_vc`, `M.sin_not_in_eml_t1_vv_t2_const` |
| `stratum:unexplained` | 10 | 10 | `R.aerr_exp_upper`, `R.decimal_add_same`, `R.forge_deadzone_certified`, `R.forge_quad_inlined_let_certified`, `R.frac5_15`, `R.meshPoint_double_odd_ge`, `R.meshPoint_double_odd_le`, `R.natCast_pos`, `R.natCast_succ_pos`, `R.six_mul_natCast` |
| `swap · assumption-conditional` | 6 | 6 | `R.concreteC_expwrapped_exists`, `R.concreteC_open_class_member_and_validon_resistant`, `R.hAsinPow15_asinR_nonneg`, `M.not_eventually_K_over_x_one_eml_eml_const_var_var`, `M.not_eventually_K_over_x_one_eml_eml_var_const_eml_var_const`, `M.not_eventually_K_over_x_one_eml_eml_var_var_eml_var_const` |
| `swap · assumption-foundation` | 6 | 6 | `M.MultiVarMod.TwoExp.expSumJacobianExpr_nonzero_somewhere`, `M.MultiVarMod.xbound_linlin`, `M.PolynomialRootCount.zero_count_bound_of_subset_poly`, `R.Patan_deriv`, `R.final_assembly`, `R.geom_le_inv_one_sub` |
| `unchanged · control` | 6 | 6 | `M.ChainExp2Capstone.chain2_trim_eval`, `M.ChainExp2YPIT.listEvalAuxN_eq_pow_mul_evalCoeffs_map`, `M.QuadraticRoots.two_distinct_roots`, `R.hasDerivAt2_exp_sum`, `R.log_zero`, `M.pev_pscale` |

**Policy spot checks (E): 10 of the 119 conditional→approved moves, seed 777, plus the 3 policy-only ones.** Each row is checked against `#print axioms` and my own policy parse.

| theorem | conditional on (0903) | still in the footprint, now trusted | ax |
|---|---|---|---|
| `M.EventuallyAboveOne.not_eventually_K_over_x_one` | div_lt_one_of_pos_lt | none | 18→28 |
| `R.expWrappedNonMonotonicWitnessC_not_constant` | div_lt_one_of_pos_lt | none | 31→37 |
| `R.expWrappedNonMonotonicWitness_upper_bound` | div_lt_one_of_pos_lt | none | 36→37 |
| `R.motor_envelope_relation` | realOfScientific, _clears | none | 33→29 |
| `R.nonMonotonicWitness_not_monotone` | div_lt_one_of_pos_lt | none | 31→37 |
| `R.one_lt_1_3` | realOfScientific, _lt_of_nat, _one_dot_zero | none | 6→29 |
| `R.one_sub_point996` | realOfScientific, _clears | none | 33→29 |
| `R.realOfScientific_eq_of_nat` | realOfScientific, _clears | none | 33→25 |
| `M.inv_x_not_depth2_right_var` | div_lt_one_of_pos_lt | none | 33→35 |
| `M.not_eventually_K_over_x_one_eml_eml_const_var_eml_var_const` | div_lt_one_of_pos_lt | none | 39→37 |
| `M.HighDimensional.eml_first_layer_log_domain_survival_decay` | realPow | **realPow (E2)** | 5→6 |
| `M.HighDimensional.firstLayerSurvival_decay` | realPow | **realPow (E2)** | 5→6 |
| `R.pi_half_lo` | pi_lower_bound | **pi_lower_bound (E1)** | 36→31 |

All 10 random picks are real discharges, with nothing outside the new trusted list remaining. 0 approved→conditional moves, confirmed from the data.

## 4. The gate, adversarially (F)

**Setup.** A throwaway `git clone` of the MachLib repository, with its `origin` remote removed, at `b6ad5d05` (`<scratchpad>/gate-attack`). Its local commits exist only in that clone. Gate under test: `tools/machsig/trust_gate.py` at b6ad5d05.

* **Baseline case:** the candidate, stamped REVIEWED, plus the evidence signature set gives **OK, rc 0**. The live content digest `88fb8df9…` and extractor digest `fd09ae46…` match.
* **Control:** the committed legacy baseline is **REFUSED** `[baseline-provenance-absent]`, as documented.

| # | attack | result | judgment |
|---|---|---|---|
| 1 | Stale set: the 23e0d047 v0.3 set, and the legacy 2026-09-03 local set | REFUSED `[signatures-stale]` / `[signatures-unidentified]`, rc 3 | **Closed.** Accidental staleness, the 2026-09-03 failure mode, is refused. |
| 2 | Edit a Lean source, commit, then give the PRE-change set a header recomputed from the live tree (`sig.provenance_record`, the same call the selftest uses) | **OK, rc 0** | **Open by design.** The set's identity is self-declared, not authenticated: any stale set can be relabelled. In CI this is harmless only because `regen.py` regenerates the set in the job. Locally, a green gate proves nothing unless you ran `regen.py` yourself. |
| 3 | A footprint growth (sorryAx enters `gexpr_sound`) | FAIL, rc 1, names the theorem | **Works.** |
| 3b | The same growth, then `--update`, then paste back the old `review` block (status/reviewer/report), then commit | **OK, rc 0**, with sorryAx now in the committed baseline | **Fail-open.** The REVIEWED stamp is not bound to the baseline it sits in: a 3-field edit turns any `--update` into a "reviewed" baseline. This is the "automatic rebaseline to make CI green" the ruling forbids, done by hand. |
| 4 | The never-reviewed candidate, stamped `REVIEWED`, reviewer `"x"`, transition_report `"lakefile.lean"` | **OK, rc 0** | **Fail-open.** Any committed file inside foundations/ counts as the "transition report". The gate does not check that it is a transition report, that it describes this baseline, or that the reviewer is a real person. |
| 5 | Statement digest changes AND sorryAx enters (`gexpr_sound`) | **OK, rc 0** ("restated: 1") | **Fail-open.** `compare()` skips the footprint check whenever the digest changed (I confirmed with the pure `compare()` call too). Any cosmetic restatement launders a growth. Worse, until someone rebaselines, that theorem is permanently exempt, because every later run sees "restated" again. |
| 6 | A watched theorem disappears from the set (renamed into the generated-name filter, e.g. `…_proof_`, made `private`, moved out of `MachLib.*`, or deleted) | **OK, rc 0** ("removed: 1") | **Fail-open.** Removal is INFO. New theorems are never ratcheted until the next reviewed rebaseline. |

**Not attacked but found by inspection:** the baseline pins axiom NAMES, not axiom STATEMENTS. **16 Certcom axioms were restated under the same name** in this window: `real_fpbridge`, `real_tanh_rounds`, `real_exp_rounds`, `real_log_rounds`, `real_round_bounds` and 11 more `*_rounds`. Several were "measured false" and repaired (fab243da, ae59d0e8). A footprint containing them looks unchanged. None has a watched dependent (section 5), so this window's transition is unaffected, but the gate is structurally blind to it.

**Recommended before CI green is cited as evidence (E4):**

* (a) Bind the stamp. The report should record the sha256 of the baseline minus its `review` block (the transition JSON already records the candidate's sha), and the gate should check it.
* (b) Make `restated` and `removed` refuse until the baseline is updated, or at least FAIL when a restated theorem's footprint grew.
* (c) Store `(axiom, statement digest)` pairs in the baseline.
* (d) Widen the population (section 5).

**The CI proposal (`PROPOSED_CI_machsig-trust.yml`): mechanically correct.** It does run the gate on the checked-out revision:

* `regen.py` binds the set to `git rev-parse HEAD` and to the content digest of the checked-out tree, and refuses if the tree moves.
* The gate recomputes both before comparing.
* On `pull_request`, HEAD is the merge commit. That is correct, since digests are content-based.
* `fetch-depth: 0` is needed for `[baseline-provenance-unresolvable]` and is set.
* No step has `|| true`, so REFUSED (3) and UNAVAILABLE (2) fail the job.
* The selftest sets its own git identity (`GIT_AUTHOR_*`, `GIT_CONFIG_GLOBAL=/dev/null`), so it will commit on a runner without a configured user.

Caveats:

* (i) It inherits every fail-open in the table above. Green means "no axiom entered an unchanged statement of a watched theorem whose digest did not change", not "the trust surface is unchanged".
* (ii) The extract.lean memory peak on a 7–16 GB hosted runner is unmeasured; nothing in this review measured it.
* (iii) elan is installed from `elan/master` by curl, unpinned (as build-time.yml already does).
* (iv) `capped_lean.sh` runs uncapped on a runner, which is acceptable as the file says.
* (v) It must land in the same commit as the reviewed baseline, and `machsig-gate` must not be squash-merged (the provenance commit `fb806c09` has to stay reachable). Both are stated correctly in GATE14_REPAIR.md.

## 5. Coverage gap (G): confirmed, and larger than reported

Counted at c3046961 from my own extraction. A declaration counts as hand-written when it has a source declaration range (`findDeclarationRanges?`).

| unwatched population | count | the agent said |
|---|---:|---|
| `Certcom.*` theorems, hand-written (548 non-internal; 247 auto-generated) | **301** | 301: confirmed |
| `MachLib.*` hand-written theorems dropped by the substring filter (of 1,462 names it drops, 1,397 have no source range, i.e. generated) | **65**: `.rec` 39 (`recip_*`, `reconstructY_*`), `.eq_` 18 (`eq_of_*`…), `.below` 5 (`below_*`, `belowIdentityUnbounded_*`), `.inj` 2, `proof_` 1 | "~70": confirmed (65) |
| hand-written theorems in a MachLib module **outside** the `MachLib.`/`Certcom.` namespaces (all in `MachLib.SinTaylorRemainder`, root namespace: `R0_bound` … `R5_zero`, `abs_mvt_step`, `my_two_pos`, …) | **39** | not reported |
| `private` theorems in MachLib/Certcom modules (1,092 with a source range) | **1,641** | not reported. Their axioms flow into public theorems that use them, so this matters less. |

Every one of the 65 filtered theorems is approved-policy today. Of the 548 non-internal Certcom theorems, 539 are approved-policy and 9 are conditional.

**What is invisible as a result.** 35 axioms are used **only** by unwatched theorems. The gate cannot see any movement in them:

* all 16 restated Certcom float-bridge axioms (`real_fpbridge` alone has 96 Certcom dependents);
* all 13 axioms added since 0903, of which 10 are Certcom: `real_*_finite`, `float_lit_*`, `real_abs_eps_eq_zero`, `real_fpfinite`, `real_round_finite`. The other 3 are `MachLib.Real.u_le_half`, `u_le_inv_two_pow_52` and `u_lt_one`. Their trusted status was set in d50dfe15, bceff6ee and 3333c7bf. bceff6ee says two of them were owner-approved; I did not review the rest, because they are outside this baseline.

So "no post-0903 axiom entered an existing theorem" is true because nothing watched can see those axioms, not because nothing changed.

## 6. Reproduce this review

Everything is in `<scratchpad>/review/`, and the clones are in `<scratchpad>/mlrev-{old,new,mid}` and `<scratchpad>/gate-attack`.

```
# per revision R in {23e0d047, 9bfe0380, 2d2f59c0, c3046961}: fresh clone, checkout, cold build
lake build MachLib
lake env lean review/rv_extract.lean  > review/rv_<R>.tsv     # axioms + type serialization (~2 min)
lake env lean review/rv_extract2.lean > review/rv2_<R>.tsv    # axiom statements, def bodies, statement constants
lake env lean review/paall_<side>.lean > review/paall_<side>.out   # #print axioms, every watched theorem (~4 s)
python3 review/rv_transition.py   # kinds; row-by-row comparison with transition_2026-10-13.json
python3 review/rv_mech.py         # 39 discharged vs git show; explained / unexplained; exact equation
python3 review/rv_policy.py; python3 review/rv_tiers.py   # policy parse, tiers, E1/E2
python3 review/rv_sample.py; python3 review/rv_check.py   # seed-777 sample and #print axioms check
```

Key outputs:

* `my_kinds.json`, `my_unexplained.json`, `attribution.json`, `my_cond_to_appr.json`, `axioms_restated.json`, `defs_changed.json`;
* `stmt_mentions_changed_defs.json`, `G_handwritten_excluded.json`, `my_sample_777.json`, `my_check_results.json`;
* gate-attack helpers: `forge_set.py` and `stamp.py`.

Nothing in the `machsig-gate` worktree, the main checkout or Forge was modified.
