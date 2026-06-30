# MachLib sorryAx audit

**Question (the muse's standard): does any *claimed* MachLib theorem secretly rest on `sorry`?**
A `sorry` compiles green; `mach_ring` — the all-`try` tactic — can silently swallow an unclosable
goal into one. So "sorryAx-free" must be *checked*, not assumed.

## Result (2026-06-30)

`tools/sorry_audit.lean` walks every MachLib `theorem`/`def` in the environment and flags any that
transitively depend on `sorryAx`:

> **5455 declarations checked · 3 carry `sorryAx` · 5452 clean · ZERO false green.**

All 3 are intentional and documented — none is a claimed/completed result, none is in the public
front door (`docs/what_is_proven.md`), and all 3 are orphans (nothing depends on them; a dependent
would have shown `sorryAx` too):

| declaration | status |
|---|---|
| `MachLib.Real.halve_in_unit_sorry` (ForgeTest) | RED skeleton, paired with the GREEN `halve_in_unit` right below it — a deliberate teaching contrast. |
| `MachLib.HighDimensional.high_dim_ball_cube_ratio_tends_zero` | `HighDimensional.lean` module disclaimer: *"intentionally carry `sorry`; formalization targets, not completed proof claims."* |
| `MachLib.HighDimensional.guarded_lowering_preserves_domain_annotations` | same module / disclaimer. |

So every *completed, claimed* MachLib result is genuinely `sorryAx`-free.

## The gate (regression-proof)

`tools/check.sh` (or `cd foundations && lake env lean tools/sorry_audit.lean`) re-runs the sweep with
those 3 allowlisted; **any other `sorryAx` fails the build (non-zero exit)**. Proven to go red: an
injected `theorem audit_canary_regression : True := by sorry` made it FAIL naming the offender, and
removing it restored PASS. This catches a future `mach_ring`-swallowed sorry the moment it lands.

(Lesson behind this: `mach_ring` is the weak all-`try` normaliser; for identities needing
cancellation use `mach_mpoly`. See the discharge of the quadratic-Lyapunov triangle inequality.)
