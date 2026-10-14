# MachSig gate 14: second independent review (hardening, narrow candidate, widening)

> Copied into the repository on 2026-10-14 for the step-7 landing, which this review's stamp cites. Verbatim except that local paths are redacted: `<scratchpad>` is the reviewer's private working directory, not part of this repository.

Written 2026-10-14 by the same independent review agent (Claude), not the repair agent. I used my own clones (`<scratchpad>/mlrev-fa1b` at `fa1b47fc`, `mlrev-cab7` at `cab7a801`, `gate-attack2`, and the first review's `mlrev-old`/`mlrev-new` cold builds), my own Lean extractor and scripts, and my own seeds. Nothing was pushed. The only commits are local, in throwaway clones whose `origin` remote I removed. I did not touch the main checkout, Forge or any shared worktree. Review time: 08:43 to 09:13 PDT (30 minutes).

## 0. Verdicts

| subject | verdict |
|---|---|
| **Hardening** (3f297f7f…f5b45a37) | **ACCEPT EXCEPT H1.** Attacks 3b, 4, 5 and 6 from the first review, which all passed before, now fail or are refused. So do new attacks on redefinition, axiom restatement, policy widening and run reuse. **H1 is a new fail-open:** a two-commit rebaseline with a 4-line hand-written "transition report" gets an unreviewed footprint growth through to `MACHSIG-TRUST OK`. Fix it before step 7, or before CI green is cited as evidence. |
| **Narrow candidate** | **ACCEPT EXCEPT E1, E2, E3**, unchanged from review 1. The content claim is confirmed, the 297 `redefined` match my E3 analysis, and the step-7 flow ends in OK at `cab7a801`. |
| **Widened candidate** | **ACCEPT EXCEPT E1 (now 222 footprints), E2, E3 (+ the Certcom runtime-model redefinitions), R1, U1.** The population rule is confirmed independently: 9,431 = 8,969 / 461 / 1. All 16 restated axioms are strictly weaker and pass my own measurement. All 13 new axioms are true under binary64 and glibc 2.39, but the policy questions in U1 need the owner. |

The widening sign-off rows in section 3 total ACCEPT 33, ACCEPT-WITH-NOTE 5, ESCALATE-TO-OWNER 4 (R1, U1, and E1 and E2 again), REJECT 0. Across the whole document there are 7 distinct ESCALATE items: H1, H2, E1, E2, E3, R1 and U1.

## 1. Hardening (item 1)

**Setup.** A throwaway clone of `fa1b47fc` with its origin remote removed. The signature set was **my own** `regen.py` run at `fa1b47fc` (my build, `MACHSIG_RUN_ID=review2-run1`). The widened candidate was stamped as step 7 prescribes (`baseline_sha256 = --content-digest`, report = `transition_widened_2026-10-13.json`).

**Baseline case: OK, rc 0, all seven conviction counters 0.** Standalone (no run id) gives OK plus `ADVISORY`, as documented.

| # | attack | first review | now | judgment |
|---|---|---|---|---|
| A1a | stale v0.3 set (23e0d047) | REFUSED | REFUSED `[signatures-corrupt]` (no v0.4 digests) | closed |
| A1b | legacy 2026-09-03 local set | REFUSED | REFUSED `[signatures-unidentified]` | closed |
| A1c | the first review's v0.3 set (same sources) | — | REFUSED `[signatures-corrupt]` | closed |
| A1d | honest set, but another run's id | — | REFUSED `[signatures-not-this-run]` | closed |
| A2 | commit a Lean edit, relabel the pre-edit set with the live identity **and this run's id** | OK | **OK, rc 0** | **Open by design, and documented.** The header is self-declared. In CI the job regenerates the set itself, so this needs a modified workflow or gate (see H2). |
| A3 | sorryAx enters `gexpr_sound` | FAIL | FAIL `[acquired]` + `[policy-violation]` | works |
| A3′ | a trusted axiom (`pi_lower_bound`) enters `clamp_lipschitz` | — | FAIL `[acquired]` | works |
| A3b | grown `--update` with the old review block pasted back | **OK** | REFUSED `[review-unbound]` | **closed** |
| A3c | the same, with `baseline_sha256` recomputed and a 4-line JSON "report" citing previous → this | — | REFUSED `[review-report-mismatch]` (see H1 for the variant that passes) | closed in one commit |
| A4 | reviewer "x", `lakefile.lean` as the report | **OK** | REFUSED `[review-report-invalid]` | **closed** |
| A4b | widened baseline citing the narrow report | — | REFUSED `[review-report-mismatch]` | closed |
| A5 | cosmetic restatement, axioms unchanged | **OK** (with sorry) | FAIL `[restated]` | **closed** |
| A6 | `gexpr_sound` leaves the watched set | **OK** | FAIL `[removed]` | **closed** |
| A7 | the set's policy adds `exp_gt_two_x` to trusted | — | FAIL `[policy-widened]` | works |
| A8 | `DefClosureDigest` of `clamp_lipschitz` changes | — | FAIL `[redefined]` | works |
| A9 | `AxiomStatementDigest` of `real_fpbridge` changes | — | FAIL `[axiom-restated]` | works |
| A12 | narrow candidate committed on `fa1b47fc` (widened extractor) | — | REFUSED `[extractor-mismatch]` | correctly closed: narrow lands only with the hardening commits (≤ cab7a801) |
| **A10** | **two-commit laundering** (H1) | — | **OK, rc 0** | **FAIL-OPEN, see H1** |

**H1, two-commit laundering (ESCALATE-TO-OWNER; must fix before step 7).** The steps:

1. **Commit 1** rebaselines with `--update` after a real footprint growth (`pi_lower_bound` entering `clamp_lipschitz`). The gate refuses at commit 1, but CI on a PR normally checks only the head.
2. **Commit 2** adds `status: REVIEWED`, the correct `baseline_sha256`, and a hand-written 4-line JSON: `{"schema": "machsig-transition/v2", "binding": {"old_baseline_sha256": D, "new_baseline_sha256": D}}`. Here D is the digest of commit 1's file.
3. The gate prints **`MACHSIG-TRUST OK`**. The committed baseline now holds the growth, and no report ever listed it.

Why it passes: `previous_baseline()` takes the file at the parent of the *last* commit touching the baseline, which is the unreviewed commit 1. The report is also checked only for its schema prefix and two hashes, never against the transition it claims to describe.

With sorryAx as the growth, only `[policy-violation]` stopped it; every review check passed.

Fixes, either of which closes it:
* (a) Bind to the last **reviewed** baseline: walk back past commits whose baseline was not validly stamped.
* (b) Recompute `compare(old, new)` from the two baselines and require the report's rows or counts to equal it, so a hollow report fails.

(a) plus (b) also make an honest-but-careless rebaseline visible, in that the changes must appear in the report. Neither authenticates a reviewer, as the docs already say.

**H2, the gate's own code is not pinned (ESCALATE-TO-OWNER, recommend CODEOWNERS).** `trust_gate.py` and `trust_gate_selftest.py` are deliberately outside `EXTRACTOR_FILES`. A PR that edits the gate, for example to make it return OK, passes CI on that PR, because CI runs the PR's own gate. Edits to the extractor files are refused by `[extractor-mismatch]`; edits to the gate are not. This is the usual limit of in-tree CI gates. Recommend required review (CODEOWNERS) on `foundations/tools/machsig/**` and `AxiomLedger.lean`, or running the gate from the base branch.

**False positives at an unchanged revision: none.** My cold-built regenerations reproduce both candidates' signature sets **byte-for-byte on records**:

* `fa1b47fc`: `records_sha256 03316b54…`, equal to the widened candidate's;
* `cab7a801`: `7124d415…`, equal to the narrow candidate's.

`judge()` against each candidate gives 0 in every list: no false `redefined`, `axiom-restated` or `policy-widened`. Two independent extractions, from different builds and processes, give identical `DefClosureDigest` and `AxiomStatementDigest` values, so the digests are deterministic. The selftest passes (Part A 8+4, Part B 41 faults + 1 control) and the mutation test reports 28/28 killed (1 min 42 s).

**Design notes:**
* Theorems and opaque constants stop the closure walk, so a pure proof change can't trigger `redefined`. A definition whose body inlines a proof term would, but that fails closed.
* All 232 axioms used in footprints are pinned; none is used without a pin.
* `axioms-gone` is reported but is not a conviction. This is harmless, because a renamed axiom shows up as `acquired`.

## 2. Narrow candidate (item 2)

* **Content claim: confirmed.** Its `axiom_sets` table is equal (as a dict) to the candidate I reviewed on 2026-10-13, which I recovered from git at `b6ad5d05`, sha `6ed24033…`. The compact sorted-JSON sha256 is `1d946b0e` in both. Every theorem's `ax`/`d`/`set` is identical, and the population is the same 7,948. All 7,948 axiom sets equal my own `collectAxioms` extraction.
* The policy block equals my own parse of `AxiomLedger.lean` (217 known / 143 trusted). `allowed_sorry` = `[halve_in_unit_sorry]`.
* My regeneration at `cab7a801` reproduces its signature set byte-for-byte (records sha `7124d415…`).
* **The 297 `redefined` match my E3 analysis.** I predicted 296: watched theorems with an unchanged footprint whose statement reaches a changed definition, by my own walk over def bodies. The one extra, `SingleExpKhovanskii.ExpPoly.autoWitness_length_one`, is reached through the constructors of the inductive `IsKhovanskiiReducibleExp`. My walk did not follow inductives; MachSig's correctly does.
* The agent's 20 in-place changed constants agree with my list. They are `clamp`, `natCast`, `realOfScientific`, `exp10`, `pconsN`, `polyIs*Const`, `multiIs*Const`, `normalizeCoeff`, `insertUniqueRoot`, `emlTreeErrorBound`, plus the Certcom runtime model (`Prims`, `stdI1`, `stdR1`, `leanPrims`, `Trans1.cName`).
* My 16 restated axioms equal its `axiom_moves.restated`.
* **End to end:** at `cab7a801`, copied to `tools/machsig/trust_baseline.json`, stamped as GATE14_REPAIR step 7 says, committed, then gate run with this run's id gives **OK, rc 0**. The report's `binding.old` (`4994f4ea…`) equals my computed content digest of c3046961's committed baseline.

## 3. Widening (item 3)

### 3a. Population rule

I wrote my own rule without reading the agent's code. A theorem is watched when all of these hold:
* it is in a MachLib module, or its user name is under `MachLib.` or `Certcom.`;
* it has a **source declaration range**;
* its last name component is not a generated suffix (`congr_simp`, `eq_def`, `eq_unfold`, `eq_N`, `inj`, `injEq`, `sizeOf_spec`, `induct`, `proof_N`, `match_N`);
* no component of its user name is internal (`_`-prefixed or numeric).

Private theorems are judged by their user name.

| check | result |
|---|---|
| my rule at c3046961 | **9,431**, identical name set (0 / 0 difference) |
| my rule at 23e0d047 | **8,584**, equal to the packet |
| tiers of the 9,431 under my policy parse | **8,969 approved / 461 conditional / 1 unchecked** (`halve_in_unit_sorry`), equal to status.json |
| the widened candidate's 9,431 axiom sets vs my `collectAxioms` | 0 mismatches |
| added 1,497 | 301 Certcom + 1,092 private + 65 filter-dropped + 39 root-namespace (`MachLib.SinTaylorRemainder`), equal to my first review's counts |
| what the range rule excludes beyond reserved names | 73 theorems, all compiler-generated (`*.brecOn`, `*.brecOn.eq`, `*.ofNat_ctorIdx`) |
| the 14 `congr_simp` dropped | no source range. Lean generates them on demand, so whether one exists depends on whether some `simp` call happened to need it, and their statement is fixed by the definition, which `DefClosureDigest` covers. **Dropping them is right.** The widened rebaseline must list them as removed, and it does (16 removed = 2 real + 14 congr_simp). |

### 3b. The 16 restated Certcom axioms

**Method.**
* Old and new statements were pretty-printed with `#check` at 23e0d047 and c3046961.
* For the numeric ones, I measured myself on this machine (glibc 2.39, aarch64; CPython `math` calls the same libm as Lean's `Float.*`) against mpmath at 160 bits. Seed 778, about 34–39k inputs per function, including binade edges, values near 1, the branch thresholds of the runtime composites, and up to ±710.
* sinh/cosh/tanh were measured through **the transcribed runtime bodies** of `stdI1`, which use expm1, not libm's sinh.
* Every axiom was instantiated at its **tightest** choice of quantified bounds: R = |a|, hi = a, and lo or hi = 1 for log. "Max ratio" is error/bound, and must stay ≤ 1.

**Every one of the 16 is strictly weaker than before:** it adds `isFinite` or range hypotheses and/or loosens the bound, and the old form implies the new, given `u ≥ 0`. For `real_fpbridge`, the in-tree theorem `FPBridge.finite` proves this. **No restatement strengthens what is assumed.** None is suspicious, and the old forms were false: my sample violates old `tanh` (u, 9 hits, 1.26u) and old `log10` (relative u, 349 hits, 1.90u). The in-tree theorem `abs_exact_inconsistent_with_unrestricted_forms` derives `False` from the pre-09-14 forms plus `real_abs_eps = 0` and glibc's behaviour at +∞; it is a hypothetical, not an inconsistency of today's axioms.

| axiom | change (old → new) | measured max ratio (new) | outcome |
|---|---|---:|---|
| real_abs_rounds | + `a.isFinite` | — (fabs is exact) | **ACCEPT** |
| real_acos_rounds | + `a.isFinite`; bound u·π unchanged | 0.64 | **ACCEPT** |
| real_asin_rounds | + `a.isFinite`; u·π/2 unchanged | 0.64 | **ACCEPT** |
| real_atan_rounds | + `a.isFinite`; bound is the opaque `real_atan_eps` | — (no numeric content) | **ACCEPT** |
| real_sin_rounds / real_cos_rounds | + `a.isFinite`; opaque eps | — | **ACCEPT** |
| real_cosh_rounds | + result finite; u·cosh R → **4u**·cosh R | 0.63 (max at the a > 709.78 branch) | **ACCEPT** (loose, not false) |
| real_sinh_rounds | + result finite; u·cosh R → **4u**·cosh R | 0.63 | **ACCEPT** |
| real_exp_rounds | + a finite, result finite, `dblMin ≤ exp a`; u → **2u** | 0.50 (old u: 0.9995, at the edge) | **ACCEPT** |
| real_fpbridge | `FPBridge` → `FPBridgeFinite` (finite results; products 0 or ≥ DBL_MIN) | — (IEEE round-to-nearest; the ties-to-even DBL_MIN case is argued in the docstring) | **ACCEPT** |
| real_log_rounds | + `a.isFinite`; u → **2u** | 0.50 (old: 0.997) | **ACCEPT** |
| real_log10_rounds | + `a.isFinite`; u → **3u** | 0.63 (old: **1.90, false**) | **ACCEPT** |
| real_round_bounds | + `M ≤ dblMax`, `x = 0 ∨ dblMin ≤ |x|` | — (round-to-nearest, normal range) | **ACCEPT** |
| real_sqrt_rounds | + `a.isFinite`; u·√hi unchanged | 0.997 (sqrt is correctly rounded: tight but true) | **ACCEPT** |
| real_tan_rounds | + `a.isFinite`; u → **2u** | 0.50 | **ACCEPT** |
| real_tanh_rounds | drops the vacuous R; + `a.isFinite`; u → **2u** | 0.63 (old u: **1.26, false**) | **ACCEPT** |

On "looser to make a proof go through": cosh/sinh at 4u and log10 at 3u have 1.6× slack over my maxima, so they are loose but true. A looser assumption is *safer*; it only weakens what the grounded theorems conclude. That is precision, not trust, so it is not escalated.

### 3c. The 13 new axioms

The 13 came from 3333c7bf, d50dfe15 and bceff6ee, all 2026-09-14, and **all 13 entered both `knownAxioms` and `trustedFootprint`.** Each commit message says "owner-approved"; I could not see the rulings themselves. This differs from E1, where no approval is claimed.

| axiom | true of binary64 / glibc 2.39 under MachLib's model? | derivable? | outcome |
|---|---|---|---|
| float_lit_0_05, float_lit_0_4, float_lit_1_5 | yes: Lean's literal bits (`#eval toBits`) equal the correctly rounded doubles (4587366580439587226, 4600877379321698714, 4609434218613702656), i.e. `floatOfR` read as round-to-nearest | no (`Float` and `floatOfR` are opaque) | **ACCEPT** |
| real_abs_eps_eq_zero | yes (fabs is exact) | **a definition in disguise:** `real_abs_eps` is an opaque axiom constant, and this axiom fixes it to 0. This is exactly the `exp10` precedent (e25e0cd1 made it a `def`) | **ACCEPT-WITH-NOTE → U1** |
| real_exp_finite (a ≤ 709) | yes: exp(709) = 8.2e307 | no | **ACCEPT** |
| real_cosh_finite, real_sinh_finite (\|a\| ≤ 710) | yes: the runtime bodies give 1.117e308 at ±710 (finite through the `exp(a/2)²/2` branch) | no | **ACCEPT** |
| real_log_finite | yes: log over positive finite doubles lies in [−744.44, 709.78] | no | **ACCEPT** |
| real_fpfinite (`FPFiniteOfRange`) | yes: round-to-nearest overflows only from DBL_MAX + 2^970 | no | **ACCEPT** |
| real_round_finite | yes | no | **ACCEPT** |
| u_le_inv_two_pow_52 (u ≤ 2⁻⁵²) | yes, at u = 2⁻⁵³ | no (the strongest of the chain) | **ACCEPT** |
| u_le_half (u + u ≤ 1) | yes | **yes**, from `u_le_inv_two_pow_52` (its own docstring says so) | **ESCALATE → U1** |
| u_lt_one (u < 1) | yes | **yes**, from `u_le_half` + `u_nonneg` (its own docstring says so) | **ESCALATE → U1** |

**U1 (ESCALATE-TO-OWNER): the `u` chain and `real_abs_eps` against "provable means proved".**
* **The chain.** `u_le_one ⇐ u_lt_one ⇐ u_le_half ⇐ u_le_inv_two_pow_52` are four axioms where one would do. The 2026-10-04 policy (`derivableAxioms` empty; "a derivation found later is a reason to convert") was not applied to them, because they predate it and nothing detects an unlisted derivable axiom.
* **Tiering incoherence.** The *weakest*, `u_le_one`, is declared but **not trusted**, while the three stronger ones **are** trusted. As a result, 8 Certcom theorems are conditional *only* on `u_le_one`: `bridge_add`, `bridge_mul`, `evalEML_forward_error`, `evalEML_prod3_fwd`, `length_sq2_bridge`, `pipeline_prod3`, `pipeline_sqSum`, `prod3_bridge`. Each would be approved if it used the stronger `u_lt_one`. 14 widened theorems use `u_le_one`.
* **Recommendation:**
  * (i) make `u_le_one` a theorem of `u_lt_one`, which only swaps in an already-trusted axiom;
  * (ii) either derive `u_lt_one` and `u_le_half` from `u_le_inv_two_pow_52`, which makes 71/65 footprints rest on the stronger fact, the trade 5841ea60 accepted for π, or record a sub-theory reason for keeping them, as was done for `zero_ne_one_ax`;
  * (iii) make `real_abs_eps` a `def := 0`, which turns `real_abs_eps_eq_zero` into `rfl`: 16 watched footprints lose `real_abs_eps`, and 9 of them also lose `real_abs_eps_eq_zero`.

  None of this changes the candidate's correctness; it is policy hygiene for the owner.

### 3d. The 18 added conditional theorems and the 8 unexplained movements (W4)

**18 conditional, all confirmed:**
* 17 existed on 2026-09-03 and were already conditional then:
  * 8 on `u_le_one` (see U1);
  * 5 private `EMLAsymptoticClass` lemmas on `MachLib.exp_tangent_line_strict`;
  * 2 on `exp_gt_two_x`;
  * 2 private `GaussianDiskSandwich` lemmas on `sqrt_zero`/`sqrt_neg_zero`.
* 1 is new: `Certcom.abs_exact_inconsistent_with_unrestricted_forms`, on `arccos_zero`/`arcsin_zero`. It is the hypothetical refutation of the old axiom forms: every old form is a *hypothesis*, so it asserts nothing about today's axioms.

**ACCEPT.** The labels are honest, and every out-of-policy axiom is a declared axiom.

**The 8 W4 movements match my own run of the mechanism test**: the same 8, attributed by my intermediate builds.
* `natCast_mul_add_local` (private) shrank only in the 2026-10-04 window, with only trusted and standard axioms leaving through a re-proved dependency. **ACCEPT.**
* The 7 Certcom grounded theorems are **restated**; see R1. Their uncovered entry is `divR` or `div_def`, from new `FloatSafe` hypotheses whose definitions use division (`dblMin = 1/2¹⁰²²`).

**R1 (ESCALATE-TO-OWNER, recommend accept): 27 restated Certcom theorems, the grounded headlines.** All 27 changed statement in September (9802f19e, fab243da, ae59d0e8, bceff6ee, d50dfe15, b0d45311) and footprint on 2026-10-04. Examples, from `#check` at both revisions:

* `pipeline_det_grounded` (the Theorem-A headline) and `pid_grounded` gained a `FloatSafe realToR … env …` hypothesis;
* `pid_tanh_grounded` gained `FloatSafe` and its error went from u to **u + u**;
* `tanhVar_controller_tracking` replaced a uniform bound `|yf k| ≤ R` with `(yf k).isFinite` and doubled its rounding term.

These say less than they did on 2026-09-03 (mostly weaker), because their old forms rested on axioms measured false. Forge relies on them by name: `reproduce/verify_grounding.py` pins their footprints, and its floor already includes `real_log_finite` and `u_le_half`, so Forge has adapted. Anything published before 2026-09-14 that quotes a grounded headline quotes the unconditional form. The owner should know, for the same reason as B1/E3.

**The 18 added `redefined`** are Certcom's compiler-correctness theorems (`emitC_correct`, `runProg_correct_std`, `std_hrt1`/`std_hrt2`, `exec*_correct`, …) plus 5 MachLib/private polynomial lemmas. They now describe the corrected C runtime model: the `log10` Prim (51668f14), and sinh/tanh over expm1 (b0d45311), "as forge now runs". This is the E3 class (definitions changed under unchanged statements). **ACCEPT-WITH-NOTE**, folded into E3.

### 3e. Seed-778 targeted sample over the widened population

**Classes.** My own kind × trust-class labels, with sizes equal to the widened transition's; promoted, restated and redefined each counted as a class. Plus four added-population strata: private, Certcom, filtered, root-namespace.

**Sample.** `random.Random(778)`, 5 per class (all members if fewer), plus 20 random from the 9,433 theorems watched on either side. That makes **116 distinct theorems, 15 of them private.**

**Method.**
* For each, `#print axioms` was run through `elabCommand` at each revision where it exists, in my cold builds.
* A private name has a numeric component, so it can't be written as an identifier. It was built with `Name.mkNum` and passed to `#print axioms` through `mkIdent`; Lean resolved it.
* Each result was checked against: my `collectAxioms`; the transition JSON's old set; the widened candidate's set; kind recomputed from the printed sets; controls unchanged; and congr_simp absent from the candidate.

**Result: 116/116 agree, 0 mismatches**, every class 5/5 (2/2 and 1/1 where smaller), random 20/20. Beyond the sample, all 9,431 candidate sets equal my full extraction, and my regenerated signature set is byte-identical on records.

| class | checked | agree | class | checked | agree |
|---|---:|---:|---|---:|---:|
| grew · conditional | 5 | 5 | shrank · conditional | 5 | 5 |
| grew · foundation | 5 | 5 | shrank · foundation | 5 | 5 |
| grew · promoted | 5 | 5 | shrank · promoted | 5 | 5 |
| new · approved | 5 | 5 | swap · conditional | 5 | 5 |
| new · conditional | 5 | 5 | swap · foundation | 5 | 5 |
| redefined | 5 | 5 | swap · promoted | 2 | 2 |
| removed · congr_simp | 5 | 5 | unchanged (control) | 5 | 5 |
| removed · approved | 2 | 2 | added: private | 5 | 5 |
| restated · foundation | 5 | 5 | added: Certcom | 5 | 5 |
| restated · promoted | 1 | 1 | added: filtered | 5 | 5 |
| restated · no-axiom-change | 1 | 1 | added: root-namespace | 5 | 5 |
| random (any) | 20 | 20 | **total** | **116** | **116** |

Also confirmed from my data:
* 120 conditional→approved across the widened set, 0 the other way;
* `pi_lower_bound` entered **222** existing widened footprints (E1, previously 181), and it is the only promoted axiom that entered any;
* no post-09-03 axiom entered any existing widened theorem;
* the 16 new conditional theorems are the narrow 15 plus `abs_exact_inconsistent_with_unrestricted_forms`.

### Sign-off table: the widening

| id | item | outcome | reason |
|---|---|---|---|
| W1 | population rule (9,431) | **ACCEPT** | My independent rule gives the same set; it equals the ledger's total and tiers. |
| W3 | drop 14 `congr_simp` | **ACCEPT** | Generated on demand with no source range; their meaning is covered by the closure digest. |
| W2a | +301 Certcom.* (292 approved, 9 conditional) | **ACCEPT** | Footprints verified; conditional ones covered below. |
| W2b | +1,092 private (1,083 / 9) | **ACCEPT** | Verified, including 5 private names via `#print axioms`. |
| W2c | +65 filter-dropped, +39 root-namespace | **ACCEPT** | All approved-policy. |
| W2d | 18 added conditional | **ACCEPT-WITH-NOTE** | Honest labels. 8 are conditional only on `u_le_one` (U1). |
| W4a | grew 151 / shrank 152 / swap 27 (added population) | **ACCEPT-WITH-NOTE** | Only the 10-04 window; discharge mechanism. 41 gained `pi_lower_bound` (E1). |
| W4b | 27 restated Certcom grounded theorems | **ESCALATE-TO-OWNER (R1)** | They say less than on 09-03; their old forms rested on false axioms. Recommend accept. |
| W4c | 18 redefined (Certcom runtime-model correctness theorems + 5) | **ACCEPT-WITH-NOTE** | E3 class: the runtime model now matches Forge's C. |
| W4d | `natCast_mul_add_local` (unexplained shrink) | **ACCEPT** | Trusted/std axioms left through a re-proved dependency. |
| W4e | 369 new (368 approved, 1 conditional) | **ACCEPT** | |
| W5 ×16 | restated axioms (one row each in 3b) | **ACCEPT** ×16 | All strictly weaker; the measured ones hold; the old forms were false. |
| W6a | float_lit ×3, *_finite ×4, real_fpfinite, real_round_finite, u_le_inv_two_pow_52 | **ACCEPT** (10 rows) | True; not derivable; commit messages claim owner approval. |
| W6b | real_abs_eps_eq_zero | **ACCEPT-WITH-NOTE (U1)** | True; a definition in disguise. |
| W6c | u_le_half, u_lt_one | **ESCALATE-TO-OWNER (U1)** | Derivable; the tiering is incoherent with `u_le_one`. |
| W7a | 13 new axioms trusted directly | **ACCEPT-WITH-NOTE** | "Owner-approved" per 3333c7bf/d50dfe15/bceff6ee; I could not see the rulings. |
| W7b | `pi_lower_bound` promotion | **ESCALATE-TO-OWNER (E1)** | Now 222 footprints. |
| W7c | `realPow`, `realPow_nonneg` promotion | **ESCALATE-TO-OWNER (E2)** | As in review 1. |
| — | **widened candidate overall** | **ACCEPT EXCEPT E1, E2, E3, R1, U1** | The content is exact and the population is right. |

## 4. Escalations to the owner (new and carried)

| id | item | recommendation |
|---|---|---|
| **H1** | Two-commit laundering through the review binding, with a hollow report (gate OK on an unreviewed growth). | **Fix before step 7.** Bind to the last *reviewed* baseline, and recompute the transition to check the report's contents. |
| **H2** | The gate's code is in the tree and unpinned, so a PR can weaken it. | CODEOWNERS / required review on `tools/machsig/**` and `AxiomLedger.lean`, or run the gate from the base branch. |
| E1 | `pi_lower_bound` promoted with no ruling found; enters 181 (narrow) / 222 (widened) footprints. | Ratify (true, Mathlib-witnessed), or re-prove π facts without it. |
| E2 | `realPow`, `realPow_nonneg` promoted; the ruling text was not found. | Ratify if the 2026-10-04 audit approved it. |
| E3 | Definition changes under unchanged statements: 297 narrow / 315 widened `redefined`, including clamp and the Certcom runtime model. | Accept. The gate now catches these (`redefined`). |
| R1 | 27 Certcom grounded headlines restated (weaker; FloatSafe/isFinite hypotheses, 2u–4u bounds). | Accept. Note it wherever Theorem A or the PID grounding is quoted from before 2026-09-14. |
| U1 | The `u` axiom chain is derivable and incoherently tiered (`u_le_one` conditional, the stronger three trusted); `real_abs_eps` is a definition in disguise. | Make `u_le_one` a theorem; decide derive-or-justify for `u_lt_one`/`u_le_half`; make `real_abs_eps` a `def`. |

## 5. Reproduce

All scripts and outputs are in `<scratchpad>/review2/` and `<scratchpad>/review/`:

* `fpmeasure.py`, `fpmeasure.out`, `fpmeasure_log.out` (float measurement);
* `pa778.lean`, `pa778_{old,new}.out`, `sample_778.json`, `sample_778_results.json` (sample);
* `forge4.py` and `stamp2.py` (attack helpers);
* `my_sigs_fa1b.jsonl` (my regenerated set);
* `regen_cab7.log`, `restated_{old,new}.out`, and `review/my_kinds_widened.json`.

The population rule is `widened()` in `review/rvlib.py`.

---

## 6. Third pass (2026-10-14, 09:26–09:33 PDT): `machsig-gate` at `87675fa3` (H1/H2 fixes)

**Setup.** Throwaway clones: `gate-attack3` at `87675fa3`, plus `review2/ci-sim/{base,tree}` for the CI simulation. Each has its origin remote removed. I used my own signature set from my `fa1b47fc` regeneration; the sources, policy and extractor digest (`b6ed83f1…`) are unchanged at `87675fa3`.

Step 7 was landed in the throwaway clone exactly as GATE14_REPAIR describes: the widened candidate, stamped, citing `transition_widened_2026-10-13.json`, which is now v3 with `gate_transition`. The gate gives **OK**, and a `pi_lower_bound` growth into `gexpr_sound` gives FAIL `[acquired]`.

The gate's selftest passes (Part B: 45 faults + 5 controls).

### 6.1 H1 and the history walk

| # | attack | result |
|---|---|---|
| 1 | **H1 verbatim**: `--update` commit, then a self-bound 4-line report | **REFUSED** `[review-report-mismatch]` (self-binding with 1 row since the last review) |
| 2 | orphan history (L's tree, no past) | **REFUSED** `[baseline-history-unavailable]` |
| 3 | baseline moved away and back (content = reviewed L) | **REFUSED** `[review-report-mismatch]` (fails closed; friction, not a hole) |
| 4 | **report with the true `gate_transition` from L**, but `rows: []` and a human note "NOTHING CHANGED" | **OK.** By design the gate checks only the machine block; the human-readable rows, counts and `.md` can lie. |
| 5 | **RESTART**: commit the pre-review counts-only file again (a "revert"), then `--update` with a growth and a report from the origin | **OK. Hole.** |
| 6 | **MERGE**: a side branch forked from `87675fa3` (baseline = origin) rebaselines with a report from the origin; master has the reviewed L; the merge takes the side branch's file | **OK. Hole.** |

**Why 5 works.** `last_reviewed()` restarts at the **last** occurrence of the origin content (`starts[-1]`). The origin is counts-only, so `gate_transition` from it classes rows by **counts**. The growth (`gexpr_sound` 66 → 67) shows up as `["gexpr_sound", "shrank", 77, 67]`.

The forged report's `gate_transition` differs from the **reviewed** widened report's in exactly one number (77→66 became 77→67) among 5,437 rows, with equal axiom and policy parts. So a reviewer comparing it with what was already accepted would see no difference in kind.

Any equivalent content also counts as the origin: the origin file plus any `review` key hashes to the same digest.

**Why 6 works.** `rev-list -- <path>` uses git's default history simplification. A merge whose result equals one parent's file follows only that parent, so the reviewed L vanishes from the walk: the history is `[23e0d047, c3046961, X]`.

Any branch forked before step 7 can therefore produce a self-consistent "review against the origin", and merging it wins. Under the proposed CI, the base (master after step 7) judges with its own code, which has the same walk, so the merge-commit run passes too.

**Fix, all three parts:**
* (a) After step 7, the judge's anchor must be the **reviewed v3 baseline**, never the counts-only origin. Either replace `ORIGIN_CONTENT` with the step-7 baseline's content digest in the landing commit, or refuse any chain that restarts at the origin once a v3 reviewed version exists.
* (b) Count only the **first** occurrence of the origin, so a later revert does not restart the chain.
* (c) Walk with `--full-history`, or better, in CI take the reference to be **the base commit's committed baseline**, which the base gate has already accepted. The base is then the anchor, not anything the PR's history says.

(c) alone closes 5 and 6 in CI; (a) and (b) close them for standalone runs.

Row 4 is residual. Have transition.py render the packet and `.md` *from* `gate_transition`, and have the gate check that the report's `rows` and `counts` agree with it. Otherwise reviewers must read `gate_transition`, not the prose.

### 6.2 H2: is the judge pinned?

Not against a hostile PR. In the CI simulation (base = landed L, tree = a PR that adds one file and a `sorryAx` growth to `gexpr_sound`), the pin step ran exactly as the workflow does. The tree's `trust_gate.py` was byte-identical to the base's. The **Gate step exited 0**, printing a fake OK. Remove that one file and the same set gives FAIL `[acquired]` + `[policy-violation]`.

The file was `foundations/tools/machsig/json.py`. Python puts the script's directory first on `sys.path`, so the pinned gate's `import json` executes PR code. `hashlib`, `re` and `subprocess` are equally shadowable.

More generally, every PR-controlled program runs **in the same job, before the pinned gate**:
* `lakefile.lean`;
* any MachLib module during `lake build`: Lean elaboration performs arbitrary IO, and I confirmed that an `#eval IO.FS.writeFile` in an elaborated file writes to disk;
* `regen.py`, `extract*.lean`, `probe.py`'s Lean probe of `AxiomLedger.lean`, `census.py`, `sig.py`;
* `capped_lean.sh`, which is in no digest;
* the PR's `lean-toolchain`, which elan installs by name, from any GitHub repo.

Any of these can rewrite `base/…/trust_gate.py` before it is copied, rewrite the signature set after `regen.py`, or, in the case of `sig.py`, which the base selftest imports from the tree, rewrite the pinned gate after the copy.

The extractor digest catches a *changed* extractor file only if the gate that checks it is intact.

**What each side legitimately controls:**

| side | inputs |
|---|---|
| the PR legitimately controls (the tree under test) | MachLib sources, `lakefile`/manifest, `lean-toolchain`, the policy files (`AxiomLedger.lean`, `sorry_audit.lean`), the baseline and its reports. Changes here are *judged*: content digest, `policy-widened`, the review chain. |
| the PR must not control (the judge) | the gate, selftest and `identity.py` (pinned), and also Python's import path for them, the extractor's *executed* code (`regen.py`, `sig.py`, `census.py`, `probe.py`, `extract*.lean`, `capped_lean.sh`), the toolchain binary, and the job's filesystem after the build |

Judgment: the pinning closes the honest case, a change that edits the gate to make itself green, which is the realistic threat here. It is not a boundary against deliberate tampering, because Lean builds run arbitrary code.

Make that explicit in GATE14_REPAIR. For a real boundary:
* (i) make CODEOWNERS review **required** by branch protection (an owner setting);
* (ii) run the judge as `python3 -I -S` from a directory outside the tree, with `FOUND` passed in;
* (iii) pin `lean-toolchain` against the baseline's provenance, so a toolchain change is refused unless reviewed;
* (iv) add `tools/capped_lean.sh` to `EXTRACTOR_FILES`;
* (v) ideally, run extraction in one job and the judge in a separate job that checks out only the base. The extraction artifact is still produced by untrusted code, so (i) remains the real control.

CODEOWNERS today covers `tools/machsig/` (which includes the `json.py` and `sig.py` routes) and the policy files. It does not cover `MachLib/**`, `lakefile.lean`, `lean-toolchain` or `tools/capped_lean.sh`. The handle `@agent-maestro` was inferred by the repair agent; the owner should confirm it.

### 6.3 Candidates

Both candidate files at `87675fa3` are **byte-identical to `fa1b47fc`**: narrow sha `445c6e99…`, widened `218bf67f…`. These are the files I verified in sections 2–3. My regenerated records equal theirs: `03316b54…` (widened) and `7124d415…` (narrow, at `cab7a801`). Only the two transition JSONs changed (v3, `gate_transition` added). Both bind old = `4994f4ea…` (the origin), new = the candidate's content digest.

### 6.4 Readiness for step 7

**READY AFTER:**
1. **The history-walk fix (6.1 a–c).** Without it, the first post-step-7 PR can reset the chain to the counts-only origin, by revert or by merging a pre-step-7 branch, and launder a growth that the report shows as a shrink.
2. **The owner's rulings** on E1, E2, E3, R1, U1 and the choice of candidate. These are unchanged; none needs the candidate's bytes to change.
3. **An explicit statement of the trust model** (6.2): the CI pin stops self-judging edits to the gate, not hostile code. Owner: make CODEOWNERS required, and extend it to `lean-toolchain`, `lakefile.lean` and `tools/capped_lean.sh`. Runner hygiene (ii) and (iv) is cheap and worth doing in the same change.

Items 1 and 3 are code and doc changes in the gate; they do not touch either candidate. The step-7 landing itself is fine. The holes open on the **next** baseline change after it.

---

## 7. Fourth pass (2026-10-14, 09:56–10:00 PDT): `machsig-gate` at `63d53094`

**Setup.**
* Throwaway clone `gate-attack4` (origin removed), using my own signature set.
* Step 7 landed as documented (widened candidate, stamped) as commit L.
* The judge runs the CI way: `python3 -I -S <frozen copy of L's tools/machsig>/trust_gate.py --tree <tree> --anchor <L>`.
* L itself gives OK, both with `--anchor L` and with the pre-landing base (bootstrap).
* A `pi_lower_bound` growth into `gexpr_sound` gives FAIL `[acquired]`.
* Selftest: PASS (Part B 53 faults + 9 controls).

| # | attack | result |
|---|---|---|
| 1 | RESTART (re-commit the origin content, then a report from the origin) | **REFUSED** `[review-report-mismatch]`: the last reviewed is L |
| 2 | MERGE (a pre-step-7 side branch reviewed against the origin, merged taking its file) | **REFUSED**: "a merge joined 2 reviewed lines…" (also with anchor = HEAD) |
| 3 | `json.py` placed in the tree's `tools/machsig/`, plus a sorryAx growth | **FAIL** `[acquired]` + `[policy-violation]`: the isolated judge imports nothing from the tree |
| 4 | origin content plus a forged stamp (report L → origin) as hop 1, then a report from the origin | **REFUSED**: a reappearing origin is not accepted as reviewed |
| 5 | report path is a symlink to a file outside the tree | **REFUSED** `[review-report-invalid]` (resolved against `--tree`) |
| 6 | toolchain string | `toolchain_key` keeps version + full commit; a truncated commit or another version mismatches (fails closed). Only a binary that lies about itself defeats it, which is the documented hostile case. |
| 7 | **QUIET TWO-HOP, one PR, anchored at L**: commit 1 drops `gexpr_sound` from the baseline (report: 1 row, `removed`); commit 2 runs `--update` with a growth (report: 1 row, `new, 67 axioms`) | **OK, rc 0. Hole.** |
| 7′ | the same through an empty v3 baseline (9,431 `removed`, then 9,431 `new`) | **OK, rc 0** |

**Why 7 works.** Each stamp is valid for its own hop, and the anchor check only asks that L is in the lineage, which it is (L → B₁ → B₂). No report ever compares `gexpr_sound`'s new footprint with the reviewed one. A reader of the two one-row reports sees one removal and one addition. "A footprint that grows" escapes by delete-then-re-add.

**Fix (small).** When `--anchor` is given, require the committed stamp's report to start at the anchor's reviewed baseline (`binding.old == anchor ref`), i.e. one reviewed hop per change against the base. Alternatively, recompute `gate_transition(anchor_ref, HEAD)` and require the report to equal that net transition.

Standalone, also classify a "new" theorem whose name exists in any reviewed ancestor as a comparison against that entry.

**`capped_lean.sh` changed together with its provenance.** This needs a new reviewed baseline whose provenance commit holds the new runner. That is the self-stamp path: it is visible in git and covered by CODEOWNERS, and the documented hostile-committer limit applies. Not a gate hole.

**Isolated judge.** The judge reads nothing executable from the tree:
* the tree's `json.py` was ignored;
* the policy arrives inside the signature set (JSON), and the judge parses no Lean;
* a symlinked report is refused.

A source file symlinked to `/dev/zero` would hang `content_files`' sha256 until the job times out. That fails closed (denial of service only).

**Trust-model text.** The text is accurate about the hostile committer, the untrusted extraction, content-bound and unauthenticated stamps, and the human-readable rows. It **claims one thing the code does not do**: "It catches … a footprint that grows" and "a stamp [cannot be] made to describe less than the change it accepts". Attack 7 grows a footprint with two exact one-row stamps; the net change is never described as a growth. Fix the code (above), or qualify the sentence.

**Candidates.** Both candidates are byte-identical to `fa1b47fc` (narrow `445c6e99…`, widened `218bf67f…`), the bytes verified in sections 2–3.

**Readiness for step 7: READY AFTER:**
1. **The anchor fix for attack 7.** Code only; no candidate change. Until then the gate stops a single-commit growth, but not a remove-then-re-add across two stamped commits in one PR.
2. **The owner's rulings** on E1, E2, E3, R1 and U1, and the choice of candidate.
3. **Required CODEOWNERS review** set on master by the owner, as the trust model itself states.

Everything else from sections 1–6 is closed: H1, restart, merge, `json.py`, the shadowed import path, the runner and the toolchain.

---

## 8. Fifth pass (2026-10-14, 12:51–12:58 PDT): `machsig-gate` at `da8fbec8` (net-step anchor)

**Setup.**
* Throwaway clone `gate-attack5` (origin removed), using my own signature set.
* Step 7 landed as L (widened candidate, stamped).
* The judge is a frozen copy of L's `tools/machsig`, run as `python3 -I -S … --tree <tree> --anchor <A>`.
* L gives OK both anchored at its pre-landing base (the step-7 run) and anchored at L.
* Selftest: PASS (Part B 59 faults + 15 controls).

| # | attack | result |
|---|---|---|
| T1 | quiet two-hop (drop `gexpr_sound`, then re-add it grown), PR anchored at L | **REFUSED** `[review-report-mismatch]`: the HEAD report starts at the intermediate version, not at L |
| T2 | two-hop through an empty baseline | **REFUSED** (same reason) |
| T3 | limit (b): the two-hop pushed straight onto master; the push run is anchored at `before` = L | **REFUSED** |
| T3′ | **the next run on master** (anchor = the new tip) | **OK, rc 0**: both hop stamps now count as main-line steps |
| T3″ | local run, no `--anchor`, no main ref | **OK**: the default anchor falls back to HEAD |
| T4 | push of a new branch (`before` = 000…) | **REFUSED** `[anchor-unreachable]` |
| T5 | force-push (`before` not in the new history) | **REFUSED** `[anchor-unreachable]` |
| T6 | PR whose base carries an unreviewed stamp (a grown `--update` with a pasted stamp) | **REFUSED** `[review-unbound]`: master stays red until it is fixed (fails closed) |
| T7 | PR into a **stale pre-step-7 branch** (anchor = `da8fbec8`), grown baseline reviewed against the counts-only origin | **OK**, by design: whoever chooses the base chooses the anchor. Harmless as long as the required check is the one on PRs into master; merging that branch into master later is refused (T8′). |
| T8 | `merge -s ours` of that origin-reviewed branch into master | review **passes** (the side branch's stamp is off the first-parent line and does not count; L supersedes the origin). The gate then compares and FAILs `[acquired]` on the growth in the set: correct. |
| T8′ | after that, commit the side branch's file and report | **REFUSED** `[review-report-mismatch]` |
| T9 | local run, no `--anchor`, **stale** `origin/master` (pre-step-7), branch with a counts-masked growth reviewed against the origin | **OK**, with no ADVISORY line |

**Limit (a)**, remove in one reviewed change and re-add grown in a later one: **acceptable as documented.** It takes two separate reviewed changes. The first is a removal, which FAILs until it is reviewed. In the second, the reviewer sees `new gexpr_sound, 67 axioms` under a name the baseline already had.

A cheap improvement, not blocking: classify a "new" theorem whose name exists in any earlier reviewed version as `readded`, showing its last reviewed footprint.

**Limit (b) must be closed before step 7, by repository settings or by code.** T3/T3′ show the mechanics. A multi-stamp branch that reaches master without a merge commit (fast-forward, rebase-merge or direct push) is red on **exactly one run**, the one anchored at its base. Every later run is green, so the laundering becomes permanent once that single red run is ignored or never required.

This is not hypothetical here: this repository's agents fast-forward master directly (e.g. f3db04bb, "…so master can fast-forward"). Either:
* **settings:** PRs required into master, the machsig-trust judge a required status check, no direct or force pushes, no bypass, and rebase-merge disabled (merge commits, or squash, which yields one net stamp); or
* **code:** on the main line count only stamps carried by merge commits (plus the step-7 landing).

  A fast-forwarded *single*-stamp change still passes later runs, because HEAD's own stamp is judged net against the last counted reference. A fast-forwarded *multi*-stamp branch then stays red on every run until it is re-stamped net, so it fails closed. The cost is that reports after several fast-forwarded changes accumulate from the last counted stamp.

**Local default anchor (T3″, T9).** With no main ref, or a stale one, `check_all.sh`'s `machsig-trust` judges against a weak anchor and prints a clean OK. Agents cite `check_all.sh` as "all gates green", so either print `ADVISORY` whenever the anchor is HEAD or a main ref older than the last reviewed baseline, or make `check_all.sh` refuse without a current main ref. This is a small code change; recommended, not blocking for CI.

**Docs.** The doc's description of (a) and (b) matches the code and my results. Its trust-model claims now stay within what the code does.

**Candidates.** Narrow `445c6e99…` and widened `218bf67f…` are byte-identical to `fa1b47fc`, the bytes verified in sections 2–3.

**Readiness for step 7: READY AFTER:**
1. **The owner's rulings** on E1, E2, E3, R1 and U1, and the choice of candidate.
2. **Close limit (b)**, by the branch-protection settings above (which the trust model already relies on for required review) or by the merge-commit-only counting rule in code.
3. *(recommended)* An ADVISORY line, or a refusal, for anchorless or stale-anchor local runs.

Every attack from passes 1–4 stays closed. No change to either candidate is needed.

---

## 9. Sixth pass (2026-10-14, 13:41–13:44 PDT): `machsig-gate` at `8e7b4c41` (only merge commits count)

**Setup.**
* Throwaway clone `gate-attack6` (origin removed), using my own signature set.
* Step 7 landed as L.
* The judge is a frozen copy of L's code, run as `python3 -I -S … --tree … --anchor …`.
* The landing anchored at its base gives OK + `ADVISORY [anchor-before-landing]`, as documented. Anchored at L: OK.
* Selftest: PASS (Part B 70 faults + 19 controls).

| # | attack | push run (anchor = `before` = L) | later run (anchor = the new tip) |
|---|---|---|---|
| F1 | plain two-hop fast-forwarded onto master (the fifth review's limit (b)) | **REFUSED** | **REFUSED**: closed |
| M3 | `git merge --no-ff` of a branch carrying an unreviewed two-hop (hop stamps inside the branch) | **REFUSED** | **REFUSED**: the merge carries a hop report, so it never counts |
| M1 | **each hop merged locally with `--no-ff`** (drop, then re-add grown); the two merges pushed to master in one push | **REFUSED** | **OK, rc 0** |
| M2 | **evil merges built with `git commit-tree`** whose second parent is a trivial empty commit; each merge's file differs from both parents and carries a hop stamp | **REFUSED** | **OK, rc 0** |

**Finding.** "Only merge commits count" closes the plain fast-forward, but limit (b) **reopens through merge commits made locally and pushed directly**. Git cannot tell a merge GitHub made for a reviewed PR from one made on a laptop, or from one fabricated with a trivial parent (M2 needs no real branch at all). The red run happens once, at push time; every later run is green.

No code rule over git history alone can close this. The only control is the one the trust model already names: **branch protection on master**, meaning:
* PRs required;
* the judge job a required status check;
* no direct pushes;
* no force pushes;
* no administrator bypass.

Under that setting every merge commit on master is a PR merge whose run was anchored at its base and judged net. The code change is still worth keeping: without branch protection it narrows the hole from "any fast-forward" to "deliberately constructed merge commits pushed directly".

**`check_all.sh`.** I ran its `run()` classifier verbatim on real gate logs. Anchorless (`[anchor-none]`) gives **UNAVAILABLE** ("rc 0 but ADVISORY"); anchored via a current `origin/master` gives **PASSED**. The canary `canary-advisory` is wired. `[anchor-before-landing]` is matched by the same `^MACHSIG-TRUST ADVISORY` test. Correct.

**Candidates.** Narrow `445c6e99…` and widened `218bf67f…` are byte-identical to `fa1b47fc`.

**Readiness for step 7: READY AFTER:**
1. **The owner's rulings** on E1, E2, E3, R1 and U1, and the choice of candidate.
2. **Branch protection on master** (the settings above), which also makes CODEOWNERS review required. With it, every attack in sections 1–9 is closed. Without it, a direct push of hand-made merge commits launders a growth after one red run. This is now the gate's single remaining dependency, and it is a setting, not code.
