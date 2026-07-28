# MachLib sorryAx audit

**Question (the muse's standard): does any *claimed* MachLib theorem secretly rest on `sorry`?**
A `sorry` compiles green; `mach_ring` — the all-`try` tactic — can silently swallow an unclosable
goal into one. So "sorryAx-free" must be *checked*, not assumed.

## Result (2026-07-28 — one closed, was 3)

`tools/sorry_audit.lean` walks every MachLib `theorem`/`def` in the environment and flags any that
transitively depend on `sorryAx`:

> **2 carry `sorryAx` · the rest clean · ZERO false green.**
>
> **2026-07-28: `high_dim_ball_cube_ratio_tends_zero` is CLOSED**, taking the count 3 → 2. It was
> never a hard proof — `TendstoTo` and `ballCubeRatio` were both **opaque axioms**, so there was
> literally nothing to prove about them. The `sorry` marked a gap in the VOCABULARY, not in the
> argument. `MachLib/Limits.lean` supplies the ε–N definition MachLib had never had, and
> `MachLib/BallCubeRatio.lean` defines the ratio by its standard recurrence and proves convergence.
> **Net effect on the ledger: two axioms REMOVED, none added.**

All 3 are intentional and documented — none is a claimed/completed result, none is in the public
front door (`docs/what_is_proven.md`), and all 3 are orphans (nothing depends on them; a dependent
would have shown `sorryAx` too):

| declaration | status |
|---|---|
| `MachLib.Real.halve_in_unit_sorry` (ForgeTest) | RED skeleton, paired with the GREEN `halve_in_unit` right below it — a deliberate teaching contrast. |
| `MachLib.HighDimensional.guarded_lowering_preserves_domain_annotations` | same module / disclaimer. |

So every *completed, claimed* MachLib result is genuinely `sorryAx`-free.

## The gate's own blind spot (found 2026-07-28)

The walk filters on `(\`MachLib).isPrefixOf n`. A canary appended **after `end MachLib`** in
`ForgeTest.lean` — i.e. at the root namespace — **did not fire**; moved inside the namespace it
fires immediately and names the offender. So the gate is **sound for `MachLib.*` and blind outside
it**, which matters because appending to the end of a file is exactly how a declaration lands at
root by accident. Recorded rather than fixed: widening the filter to "everything" would sweep in
Lean core and the toolchain. If a second top-level namespace is ever added, the filter must widen
with it.

Exit codes re-verified in both directions on 2026-07-28: **1 on FAIL, 0 on PASS.**

## The gate (regression-proof)

`tools/check.sh` (or `cd foundations && lake env lean tools/sorry_audit.lean`) re-runs the sweep with
those 3 allowlisted; **any other `sorryAx` fails the build (non-zero exit)**. Proven to go red: an
injected `theorem audit_canary_regression : True := by sorry` made it FAIL naming the offender, and
removing it restored PASS. This catches a future `mach_ring`-swallowed sorry the moment it lands.

(Lesson behind this: `mach_ring` is the weak all-`try` normaliser; for identities needing
cancellation use `mach_mpoly`. See the discharge of the quadratic-Lyapunov triangle inequality.)
