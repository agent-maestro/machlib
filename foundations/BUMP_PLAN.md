# Toolchain bump — destination, route, and the pass bar, fixed before the first step

**2026-07-29.** Written before any migration work, because the pass bar for a migration is a
pre-registered acceptance criterion like any other, and "it still builds" is not one.

## The three constraints do NOT intersect

| constraint | satisfied by |
|---|---|
| contains the #14577 kernel fix | **≥ v4.32.2** (confirmed in its release notes: *"This point release fixes a soundness bug in the kernel… nested inductive types with phantom type parameters was incomplete and bypassed the type checker"*) |
| a `lean4checker` tag exists (acceptance gate's far end, and the second opinion we already have) | **≤ v4.28.0** — enumerated: v4.9.0 … v4.28.0, that is the maximum |
| Lean4Lean pins it (genuine independence) | v4.16.0, v4.19.0, v4.20.1, v4.23.0, v4.26.0, **v4.29.0** |

```
fix ∩ lean4checker   = ∅      (32.2 > 28.0)
fix ∩ Lean4Lean      = ∅      (32.2 > 29.0)
lean4checker ∩ L4L   = {v4.16.0, v4.19.0, v4.20.1, v4.23.0, v4.26.0}   ->  newest v4.26.0
```

**And no `v4.14.x` patch release exists** — `v4.14.0` is the only tag on that line, so there is **no
backport**. The soundness exposure cannot be retired for pocket change; it requires the full bump.
The two motivations do *not* separate into two timelines after all.

## Destination: v4.26.0 first, then track to the fix

**v4.26.0 is the recommended first destination** — the newest version where **both** checkers exist.

The tradeoff is real and belongs stated, not buried: **v4.26.0's kernel still contains the #14576
bug.** What v4.26.0 buys instead is **genuine kernel independence** — Lean4Lean is a from-scratch
re-implementation, so a check-omission in the C++ kernel's phantom-parameter handling is an
*implementation artifact* it has no reason to share. If MachLib replays clean through **both**, that
is direct evidence the exploit class is **not present in our code**, whatever either kernel would
accept in principle.

> **Independence covers the class. The patch covers the instance.** Given they cannot be had together
> today, the class is worth more — but sitting deliberately on a known-unpatched kernel is a decision,
> not a default, and it is recorded here as one.

**Then track to v4.32+** when lean4checker and Lean4Lean reach it. That is a watch item, not work.

## Route: step the checkable intermediates, never jump

`v4.16.0 → v4.19.0 → v4.20.1 → v4.23.0 → v4.26.0` — every one has a lean4checker tag *and* appears in
Lean4Lean's own history, which is decent evidence they are stable points.

Replay at each. Two reasons, and the second matters more:

1. Custom-elaborator breakage arrives **attributed to a two-or-three-version window** instead of an
   eighteen-version haystack.
2. **Every clean intermediate is a fallback position.** A stalled stepwise bump leaves the repo at
   v4.23.0 with everything green; a stalled *jump* leaves it at v4.14.0 with a broken branch.

## THE PASS BAR — fixed now, before the first step

**Not artifact identity.** `.olean` format changes across versions, so hashes are meaningless here and
comparing them would fail for reasons that say nothing about correctness.

| # | criterion | why |
|---|---|---|
| 1 | `lean4checker` replay **exits 0 at both ends** | the acceptance gate, and it exists at every intermediate |
| 2 | **`#print axioms` footprint EQUALITY** for all **57** headline theorems the ledger pins | the strong one. Same theorems, same dependencies, different kernel. A footprint that *changes* means the migration altered what something rests on — which is the only thing a bump must never do |
| 3 | `check_ledger.py` PASS, count still **252** | the trust boundary did not move |
| 4 | `check_derivable.py` PASS, still **5**, retained-base clean | the derivations survive |
| 5 | **0 sorries, 0 `sorryAx`** across the library | table stakes |
| 6 | `check_artifact_drift.py` PASS after each step | stepping *will* orphan oleans as modules move; class 8 catches it |

**Criterion 2 is the one that makes this a verified migration rather than a hopeful one.** It is
mechanical: dump the 57 footprints before, dump them after, diff the sets.

## Scope guard

The deliverable is **the same theorems, checked by a newer kernel, replay-clean at both ends.** Not
modernised proofs, not eighteen versions of new tactics, not relaxing the austerity constraints.

**MachLib's Mathlib-free discipline is the asset here:** a base that axiomatises `Real` and forbids
`by_contra` exposes far less surface to elaborator drift than any Mathlib-dependent project. The cost
is concentrated in the custom machinery — `mach_ring`/`mach_mpoly` elaborators, `Nat` pattern-match
compilation, structure-instance syntax — and **anything else moving means the diff is doing something
criterion 2 cannot see.**
