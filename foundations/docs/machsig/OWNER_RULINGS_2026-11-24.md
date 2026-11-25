# Gate 14: the owner's rulings on the 2026-11-24 rebaseline (2026-11-24)

The owner ruled on 2026-11-24 (evening), answering two questions put to them in the session that made the change. This
file records the answers verbatim. The REVIEWED stamp in `tools/machsig/trust_baseline.json` cites this file, the
independent review (`INDEPENDENT_REVIEW_2026-11-24.md`), and the transition report it binds
(`transition_2026-11-24.json`).

The change: six axioms that trusted axioms prove became theorems of the same name and type (`sqrt_zero`,
`sqrt_neg_zero`, `exp_exp_minus_exp_strictly_increasing`, `exp_one_lt_three`, `u_lt_one`, `u_le_half`). The owner chose
the round earlier the same day (items A, B and C of that day's MachLib list; C is the rest of ruling U1, 2026-10-14).
Pinned axioms 208 -> 202, trusted 156 -> 154, conditional theorems 126 -> 107. Gate 14 fails on it by design: every
dependent footprint swaps one of the six for the axioms its proof uses.

## Rulings

| id | question | ruling |
|---|---|---|
| S | "Do you sign off the six-axiom rebaseline (A/B/C), on the independent review with its fixes applied?" Options put: "Accept: stamp and merge" (forge fix lands first, after its suite; then stamp the review block, gates, PR, `--no-ff` merge; then the review's follow-ups in order) or "Hold". | **"Accept: stamp and merge (Recommended)".** |
| D | "Merge BoundedGermTranscendence (D) now?" Options put: merge after A/B/C, merge first, or hold for an outside reader. | **"Merge after A/B/C (Recommended)".** (Not a gate-14 matter: that branch only adds theorems.) |

Asked with the review's findings and the state of each fix in front of the owner, including F5 (87 theorems now formally
rest on binary64's `u ≤ 2⁻⁵²` instead of `u < 1`, the direction ruling U1 ordered).

## The review's findings, and what was done

| id | finding | outcome |
|---|---|---|
| F1 (HIGH) | Forge's BLOCKING `reproduce/verify_grounding.py` requires `u_lt_one`/`u_le_half` in 54 of 73 certificate footprints and reaches MachLib through `~/monogate/machlib`; forge goes red once that checkout moves. | Forge `4d20298e` (on master before this merge): need-sets accept `u_le_inv_two_pow_52` when neither old name is present. 73/73 on this branch and on the old checkout; a Lean-free canary fails with the tolerance removed; forge suite 14 434 passed / 119 skipped / 0 failed. |
| F2 (MEDIUM) | Five claims' sqrt-totalisation firewall (`forbid_axioms_exact: [sqrt_neg_zero]`) went silent: a theorem never appears in a footprint. | They also forbid `sqrt_le_of_le_sq`; absent from all five footprints today. |
| F3 (LOW-MED) | C6 classified new rows by short name; a planted collision passed. | C6 classifies by the sources (master's additions since the old provenance, this change's additions = exactly the six + five helpers), from comment-stripped files; `== 1` restored. Five controls each turn C6 or C3 red. |
| F4 (LOW) | Stale prose: a backwards "no smaller step", "tangent line at −1/6", the report's MD, 23 claim comments, CLAUDE.md's after-merge list. | Fixed. |
| F5 (INFO) | 87 theorems now formally rest on `u ≤ 2⁻⁵²`. | Recorded in `FPModel.lean` and CLAUDE.md; ruled in this direction by U1. |
| F6 (INFO) | The after-merge order. | Followed: forge first; then stamp, PR, `--no-ff` merge; then pull `~/monogate/machlib`, retire the two monogate-lean witnesses, re-pin monogate.org, redeploy machlib.org, tighten forge's need-sets. |
| F7 (INFO) | `bounded-germ-transcendence` only adds theorems; either order works without a re-stamp. | Merging after this one, as ruled. |

The fixes moved two Lean docstrings, so the baseline was regenerated on `af925163`; its `gate_transition` is identical
to the one the review checked (`e8e26ae4`), and only the provenance and content digest moved.
