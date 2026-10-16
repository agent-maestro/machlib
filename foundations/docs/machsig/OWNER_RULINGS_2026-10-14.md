# Gate 14: the owner's rulings for step 7 (2026-10-14)

The owner ruled on 2026-10-14: "proceed with your recommendations". The coordinator relayed the ruling,
and this file records it in substance. It authorizes step 7 of the ruling of 2026-10-13: commit the
reviewed baseline and enable the gate in CI. The REVIEWED stamp in `tools/machsig/trust_baseline.json`
cites this file, the two independent reviews (`INDEPENDENT_REVIEW_2026-10-13.md`,
`INDEPENDENT_REVIEW_2_2026-10-14.md`, sections 0-8), and the transition report it binds
(`transition_widened_2026-10-13.json`).

## Escalations

| id | what the reviews escalated | ruling |
|---|---|---|
| E1 | `MachLib.Real.pi_lower_bound` joined `trustedFootprint` in 5841ea60 with no recorded ruling. It enters 222 footprints of the widened candidate. | **RATIFIED** as the owner's ruling. |
| E2 | `realPow`, `realPow_nonneg` joined `trustedFootprint` in e25e0cd1. | **RATIFIED** as trusted. |
| E2b | The 13 double-precision axioms added on 2026-09-14 (3333c7bf, d50dfe15, bceff6ee), each trusted directly: `float_lit_0_05`, `float_lit_0_4`, `float_lit_1_5`, `real_abs_eps_eq_zero`, `real_exp_finite`, `real_cosh_finite`, `real_sinh_finite`, `real_log_finite`, `real_fpfinite`, `real_round_finite`, `u_le_inv_two_pow_52`, `u_le_half`, `u_lt_one`. | **RATIFIED** as trusted. |
| E3 | Definition changes under unchanged statements: 315 `redefined` in the widened candidate, among them `clamp`, natCast becoming a definition, and the Certcom runtime model. | **ACCEPTED.** |
| R1 | 27 Certcom grounded headlines restated. They are weaker: FloatSafe/isFinite hypotheses, 2u-4u bounds. | **ACCEPTED.** A separate sweep of public quotes of these headlines is handled elsewhere, not in this change. |
| U1 | Two problems. The `u` chain is derivable and incoherently tiered: `u_le_one` is conditional, and `u_lt_one`/`u_le_half` are derivable. `real_abs_eps` is a definition in disguise. | **DEFERRED** to a separate, reviewed MachLib change AFTER step 7. Not in this landing; no MachLib source changes here. |

## Choices

* **Candidate:** the WIDENED one, `trust_baseline.candidate-widened-2026-10-13.json`, file sha256
  `218bf67f1d6c30eb3cc27089a449a11cd24e2056c21fab7775f82fa0fb31502e`, 9,431 theorems. It covers every
  theorem MachLib declares, by the theorem ledger's rule.
* **Strictness:** KEPT closed-by-default. A restatement, a redefinition under an unchanged statement,
  or a removal of a watched theorem FAILS until a reviewed rebaseline accepts it.
* **Branch protection (P):** the owner turns it on for master AFTER the landing. No repository setting
  is changed by this change.

## Known limit, recorded

**Required human review is impossible with the current setup.** The owner and the agents commit and
open pull requests through ONE shared GitHub account. A required review by `.github/CODEOWNERS`
therefore cannot show that a human other than the change's author looked at it. The trust model
(`GATE14_REPAIR.md`) names required human review as the boundary against a hostile committer, so that
boundary does not exist here. What remains:

* the gate catches honest mistakes and unreviewed drift;
* the CI judge runs the BASE commit's gate, isolated, so a change cannot judge itself with an edited
  gate;
* every reviewed baseline is a content-bound record in git.

Anyone who can push with the shared account can still change the gate, the workflow or the policy.
Branch protection with required status checks, set without a bypass for administrators, still stops an
ACCIDENTAL bypass: an agent fast-forwarding master past a red check, for example. The owner plans it
for after the landing.
