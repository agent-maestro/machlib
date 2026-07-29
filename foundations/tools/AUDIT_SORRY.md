# MachLib sorryAx audit

**Question (the muse's standard): does any *claimed* MachLib theorem secretly rest on `sorry`?**
A `sorry` compiles green; `mach_ring` — the all-`try` tactic — can silently swallow an unclosable
goal into one. So "sorryAx-free" must be *checked*, not assumed.

## Result (2026-07-29 — one closed, was 2; the arc is 3 → 2 → 1)

`tools/sorry_audit.lean` walks every MachLib `theorem`/`def` in the environment and flags any that
transitively depend on `sorryAx`:

> **1 carries `sorryAx` · the rest clean · ZERO false green · allowlist corresponds EXACTLY.**
>
> **2026-07-28: `high_dim_ball_cube_ratio_tends_zero` is CLOSED**, taking the count 3 → 2. It was
> never a hard proof — `TendstoTo` and `ballCubeRatio` were both **opaque axioms**, so there was
> literally nothing to prove about them. The `sorry` marked a gap in the VOCABULARY, not in the
> argument. `MachLib/Limits.lean` supplies the ε–N definition MachLib had never had, and
> `MachLib/BallCubeRatio.lean` defines the ratio by its standard recurrence and proves convergence.
> **Net effect on the ledger: two axioms REMOVED, none added.**
>
> **2026-07-29: `guarded_lowering_preserves_domain_annotations` is CLOSED**, taking the count 2 → 1
> — and *this document said 2 for an unknown number of commits after it stopped being true.* The
> theorem is discharged by `GuardedLowering.guarded_lowering_preserves_domain`, footprint
> `[propext]`, **no foothold axiom** — the outcome the allowlist comment said was the only acceptable
> one. What failed was the *pruning*: the entry, and this prose, outlived the sorry.
>
> **Found by the pre-migration baseline capture, from a count disagreement** — the gate reported 1
> sorryAx decl while the allowlist held 2 entries and this file's prose claimed 2 carried it. Nobody
> read a line of Lean to find it; two independently derived counts simply failed to match. The
> remedy is mechanical, not editorial: the gate now **fails on allowlist rot**, so a stale licence
> cannot sit here silently again. See `sorry_audit.lean`'s header for the firing specimen.

It is intentional and documented — not a claimed/completed result, not in the public front door
(`docs/what_is_proven.md`), and an orphan (nothing depends on it; a dependent would have shown
`sorryAx` too):

| declaration | status |
|---|---|
| `MachLib.Real.halve_in_unit_sorry` (ForgeTest) | RED skeleton, paired with the GREEN `halve_in_unit` right below it — a deliberate teaching contrast. |

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
**that one allowlisted**; **any other `sorryAx` fails the build (non-zero exit)**, and so does an
allowlist entry that no longer carries one. Proven to go red in both directions: an injected
`theorem audit_canary_regression : True := by sorry` made it FAIL naming the offender, and removing it
restored PASS (2026-07-28); a genuinely stale allowlist entry made it FAIL naming the offender *and*
the remedy, and pruning it restored PASS (2026-07-29). This catches a future `mach_ring`-swallowed
sorry the moment it lands, and a stale licence the moment a proof closes.

(Lesson behind this: `mach_ring` is the weak all-`try` normaliser; for identities needing
cancellation use `mach_mpoly`. See the discharge of the quadratic-Lyapunov triangle inequality.)
