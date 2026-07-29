# Toolchain identity, and a kernel-soundness exposure that is OPEN

**2026-07-29.** Recorded because the trust boundary was never only the axioms.

## Instrument identity

```
pinned:  leanprover/lean4:v4.14.0   (commit 410fab728470, aarch64-linux)
latest:  v4.32.2                    (released 2026-07-28)
delta:   18 minor versions
```

The ledger pins 252 axioms and gates 5 derivations against them. **None of that constrains the
kernel that checks the proofs.** The toolchain is instrument identity in exactly the sense the SymPy
pin is, and it was not recorded — an omission this document closes.

## The exposure

**lean4 #14576** — *"Kernel accepts wrong-structure projections, allowing an axiom-free proof of
False"* — fixed by **#14577** (*"fix: missing check at kernel inductive declaration"*), merged
**2026-07-28**. From the PR: *"When eliminating a nested occurrence `I Ds is`, the parametric
arguments `Ds` are dropped from the generated auxiliary types, so they used to escape type
checking."*

`v4.32.2` shipped the same day the fix merged. **Our pin predates it by 18 minor versions.**

### Exposure is UNKNOWN, and that is the honest word

The tempting move is to argue we are unaffected because our datatypes are simple. **They are not
uniformly simple.** MachLib declares 68 inductives, of which ~10 are **parametric** — including
`MultiVarExpr (k : Nat) : Type`, `MultiVar (k : Nat) : Type`, `ChainTypeTag (k : Nat) : Type`, and
several parametric `Prop`s (`IsFold`, `RDot`, `EMLTreeValid`, `FxRoundedEval`).

The bug concerns **nested** occurrences of parametric inductives. Whether any of ours nests in the
relevant sense is **not something to settle by reading**, and "we inspected it and it looked fine" is
precisely the class of argument this project has learned to distrust — it is the
`assert_normalised_cleanly` shape applied to soundness.

*(A first pass of this note nearly recorded "no parametric inductives" because a `grep` label said
"empty above" while the list beneath it was not empty. Caught on re-read. The misreport would have
been in the reassuring direction, which is the direction to distrust.)*

## Two responses, and only one of them is durable

**1. Bump the pin — necessary, and not an afternoon.** 4.14 → 4.32 is eighteen minor versions of
syntax and API drift. MachLib is Mathlib-free so it has no Mathlib coupling to fight, but it does use
`mach_ring`/`mach_mpoly` (custom elaborators), `Nat` pattern-match compilation, and structure-instance
syntax, all of which moved over that span. Scoped as a **project**, not a task.

**2. Independent re-checking — the durable one.** The trust argument for Lean reduces to a small
kernel *precisely because proof generation and proof checking are separable*, and the kernel has been
independently re-implemented (**Lean4Lean**). Running `lean4checker` or an external kernel over the
compiled environment in CI means **a kernel bug must exist in two independent implementations to
pass**. Same move as the DA2 dual-egress: two physically independent channels for one claim.

Note the asymmetry: bumping the pin fixes *this* bug. Independent re-checking fixes *the class*.

## What the external checker found on its FIRST run

Not a soundness violation — but a real defect the normal build cannot see:

```
lean4checker found a problem in MachLib.ZZZTestSign
uncaught exception: (kernel) constant has already been declared
  'MachLib.Real.growthCompetitionWitness_deriv_pos_of_quad_pos'
```

**26 orphaned `.olean` files** in `.lake/build/lib/MachLib/` with **no source and no importer** —
`ZZZTest*` scratch modules plus `CapstoneGen`, `PidEmitted`, `PidShipped`, `ProbeDot3`. One of them
still declared a theorem that has since **moved** to `WitnessResidualGrowthCompetitionDeriv`, so
replaying the build tree produced a duplicate.

**The live build never notices, because nothing imports them.** That is precisely the class only an
independent replay finds: the build directory contained declarations that no longer exist in source,
and anyone auditing or shipping that tree would have got them. Removed; replay then exits 0.

This is the argument for the checker in one paragraph — it fired on contact, on something no gate here
was looking for.

## Status

| | |
|---|---|
| toolchain recorded as instrument identity | **done** (this file, + ledger gate) |
| exposure to #14576 | **OPEN — unknown, not ruled out** |
| pin bumped | **NOT DONE** — scoped as a project |
| independent kernel re-check | **DONE** — `check_kernel_replay.py`, MachLib replays clean, exit 0 |
| ↳ grade | **SECOND OPINION**, *not* independent kernel — see the caveat below |
| Lean4Lean (genuine independence) | **BLOCKED on the bump** — never pinned v4.14.0 (history jumps 4.13 → 4.16) |
| ↳ consequence | the bump is a **prerequisite** for "independent kernel", not a parallel improvement |
| Collatz exploit as a firing specimen | **NOT OBTAINED** — see below |

## The independence caveat, recorded so the blindness column stays honest

`lean4checker` **shares the kernel's C++ lineage in part.** Against **environment manipulation** —
tactics smuggling unchecked declarations in — it defends at full strength, and its five negative tests
(`AddFalse`, `AddFalseConstructor`, `ReplaceAxiom`, `UseFalseConstructor --fresh`, `ReduceBool`) are
exactly that class; all five verified firing here. Against **kernel-implementation bugs** its
independence is **partial**, because it re-uses the same kernel implementation to do the checking.

**Lean4Lean** is the genuinely independent re-implementation. The strongest configuration is replay
through both, and the registry row must say **which is running**.

> So the earned phrase today is **"second opinion"**. **"Independent kernel"** is not earned by
> lean4checker alone, and the difference is not cosmetic — it is *which class of defect two
> implementations would have to share*.

### And Lean4Lean CANNOT run against this pin — which reorders the plan

Attempted 2026-07-29. Lean4Lean's `lean-toolchain` history, enumerated over all commits that ever
touched that file:

```
  v4.1.0-rc1 · v4.2.0-rc4 · v4.3.0-rc2 · v4.4.0-rc1 · v4.7.0-rc2 · v4.8.0-rc1
  v4.10.0-rc2 · v4.12.0-rc1 · v4.13.0-rc3 · v4.13.0 · v4.16.0 · v4.19.0
  v4.20.1 · v4.23.0 · v4.26.0 · v4.27.0-rc1 · v4.29.0
```

**It goes v4.13.0 (2024-11-02) → v4.16.0. It never pinned v4.14.0.** `.olean` format is
version-locked, so a neighbouring release cannot read our environment — there is no commit to check
out that would work.

**The consequence inverts part of the ordering.** "Checker first, bump second" held for the *weak*
checker, which had an exact `v4.14.0` tag. For the *strong* one it does not:

> **The pin bump is a PREREQUISITE for genuine kernel independence, not merely an improvement
> alongside it.**

That makes the bump's value larger than "retire #14576 plus eighteen versions of drift". It is what
unlocks the second half of the sentence — and it now has an acceptance gate it did not have this
morning: **replay-before / replay-after** with lean4checker, which exists at both ends (v4.14.0 and
v4.32.2 both have tags).

*Deliberately not attempted: running a v4.13 or v4.16 Lean4Lean against v4.14 artifacts. It would
fail on olean version, and if some coercion made it load, a two-year-old research snapshot of a
partial kernel would give a guarantee weaker than its name suggests. An instrument that does not
match the artifact is not a second opinion.*

**On the exploit as a specimen.** A published exploit would be the ideal firing witness — historical
beats synthetic, and the patched kernel *and* an external checker must both reject it. **It is still not recorded, and it is no longer needed for the row to be complete** —
lean4checker's own five negative tests are pre-built historical witnesses of the environment-
manipulation class, and they were verified firing *here* before the gate was trusted. The Collatz
artifact would add a witness for the *kernel-bug* class specifically, which is the class where
lean4checker's independence is only partial; that makes it a **Lean4Lean** row, not this one.
