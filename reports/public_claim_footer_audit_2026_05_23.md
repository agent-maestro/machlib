# Public Footer Claim Audit - 2026-05-23

## Audited copy

`50 Lean theorems · 265 equations · EML Cost Conjecture (in development)`

Source: `/home/monogate/monogate/1op/src/components/Footer.tsx`

The same copy is visible on the live 1op homepage.

## Finding

The footer claim is only partially supported.

| Claim part | Audit result | Supporting source |
| --- | --- | --- |
| 265 equations | Supported | `/home/monogate/monogate/1op/src/lib/data/genome-data.js`, `GENOME_STATS.total = 265` |
| EML Cost Conjecture (in development) | Bounded as in-development copy | `/home/monogate/monogate/1op/src/components/Footer.tsx` |
| 50 Lean theorems | No clear supporting source found | No direct source found during this audit. The local lean-graph page references a different larger metadata count, so the footer count needs a direct source before it should remain public. |

## Recommendation

Cleanup is recommended, without deployment in this task.

Safe options:

1. Replace the theorem-count phrase with sourced public copy such as `265-equation catalog`.
2. Add a direct supporting artifact for the theorem count, then keep the footer only if the count is intended and current.
3. Remove the theorem-count phrase until the public evidence source is explicit.

This audit does not introduce a new theorem/proof/open-problem claim. It records that the current footer should be treated as needing cleanup or direct support.
