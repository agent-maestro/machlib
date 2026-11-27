# Gate 14: the owner's rulings on the Forge-bridge rebaseline (2026-10-27, b)

The owner ruled on 2026-10-27 in the session that made the change. This file records the answers. The REVIEWED stamp
in `tools/machsig/trust_baseline.json` cites it, the independent review (`INDEPENDENT_REVIEW_2026-10-27b.md`) and the
transition report it binds (`transition_2026-10-27b.json`). The change itself was ordered earlier the same day:
ruling F2 of `OWNER_RULINGS_2026-10-27_implicit.md` ("a separate change right after this one").

The change: `interval_scale_unit_lit_le` and `interval_weight_sum_le` (`Forge.lean`) were false. Each docstring said
the Forge emitter would apply it only when a literal condition held, and neither type had the condition. Both are
removed; `interval_add_scale`, whose old statement was false too, takes `j + k ≤ 1`; `ForgeBridgeControls` refutes all
three old statements. Pinned 210 -> 208; conditional 128 -> 125; trusted unchanged at 156.

## Rulings

| id | question | ruling |
|---|---|---|
| S | Accept the rebaseline, stamped REVIEWED with the owner as reviewer; push, open the pull request, merge with a merge commit (`--no-ff`) once its checks pass; then regenerate forge's visible-names list from the merged master? | **ACCEPTED; MERGE AFTER CI.** |
| D | The review's prose findings F2 and F3 (stale docstrings in `Linarith`, `Decimal`, `Forge`, `ForgeTest` and CLAUDE.md): fix them in this change, at the cost of one more signature regeneration, or later? | **FIX NOW.** Done in `7eb1b859`; the regenerated report must show the same nine rows, which checks that the commit changed prose only. |

## The review's other findings, and what was done

| id | finding | outcome |
|---|---|---|
| F1 | Forge's generated `software/verification/lean/lean_visible_names.py` goes stale by exactly the two removed names (`gen_lean_visible_names.py --check`: 2 removed). Forge CI symlinks this machine's machlib checkout, so a forge CI run against the branch checkout fails `test_the_committed_list_matches_the_environment`. | Regenerated in forge right after the merge, with the machlib checkout on the merged master. |
| F4 | C6 is described as "new rows = the module's declarations" but checks containment plus the three refutations. Correct here (the six rows are exactly the module's six theorems). | Follow-up for the template's next use. |
| F5 | machlib.org deploys by hand; its figures changed. | The owner redeploys when convenient. |
