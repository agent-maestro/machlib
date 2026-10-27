# Gate 14: the owner's rulings on the 2026-10-26 rebaseline (2026-10-27)

The owner ruled on 2026-10-27, answering two questions put to them in the session that made the change. This file
records the answers. The REVIEWED stamp in `tools/machsig/trust_baseline.json` cites this file, the independent review
(`INDEPENDENT_REVIEW_2026-10-26.md`), and the transition report it binds (`transition_2026-10-26.json`).

The change: five axioms that trusted axioms prove became theorems of the same name and type
(`exp_tangent_line_strict`, `exp_gt_two_x`, `tanh_zero`, `sqrt_one`, `u_le_one`). 134 theorems moved from conditional
to approved-policy (461 -> 327). The trusted footprint is unchanged at 143. Gate 14 fails on it by design: every
dependent footprint swaps one of the five for the axioms its proof uses.

## Rulings

| id | question | ruling |
|---|---|---|
| F1 | `u_le_one` (`u ≤ 1`) was the defining bound of the abstract float model (`0 ≤ u ≤ 1`). Deriving it from the trusted `u_lt_one` puts `u_lt_one` into 14 footprints, which then no longer cover `u = 1`. Derive it, or keep it primitive and trust it (a policy widening)? | **DERIVE IT.** `u_le_one` is a theorem from `u_lt_one`. `FPModel.lean`'s header now says the model is `0 ≤ u < 1`. This settles the `u_le_one` half of ruling U1 (2026-10-14). U1's other half, `u_lt_one` and `u_le_half` derivable from `u_le_inv_two_pow_52`, stays open. |
| S | Accept the rebaseline, stamped REVIEWED with the owner as reviewer? | **ACCEPTED.** Stamp it, push the branch, open the pull request, and merge it with a merge commit (`--no-ff`) once its checks pass. |

## The review's other findings, and what was done

| id | finding | outcome |
|---|---|---|
| F2 | Neither the gate nor checks C1-C6 compare a converted axiom's statement with its replacing theorem's. | Check C7 added to `transition_2026-10-26.py`. It uses the review's probe (`evidence-2026-10-26/statement_probe.lean`), a copy of the gate's `serExpr`. The copy is shown to reproduce four unchanged axioms' pins. |
| F3 | monogate-lean still registers a witness for `MachLib.Real.tanh_zero`, now a theorem. | Retired in monogate-lean, by the precedent of 2026-10-04/05. |
| F4 | Stale prose in `what_is_proven.md`, four Lean docstrings, the README and site measurement dates, and a CLAUDE.md sentence. | Fixed. |
| F5 | `exp_exp_minus_exp_strictly_increasing` is derivable too, and so probably is `exp_one_lt_three`. | Not in this change. Recorded in CLAUDE.md as the next conversions, by the same reviewed route. |
| F6 | Merge mechanics. | Followed: only the `review` block is stamped, and the merge is a merge commit. |
