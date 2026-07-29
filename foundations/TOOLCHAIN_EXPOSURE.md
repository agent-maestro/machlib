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

## Status

| | |
|---|---|
| toolchain recorded as instrument identity | **done** (this file, + ledger gate) |
| exposure to #14576 | **OPEN — unknown, not ruled out** |
| pin bumped | **NOT DONE** — scoped as a project |
| independent kernel re-check in CI | **NOT DONE** — the durable fix, and the next thing to build |
| Collatz exploit as a firing specimen | **NOT OBTAINED** — see below |

**On the exploit as a specimen.** A published exploit would be the ideal firing witness — historical
beats synthetic, and the patched kernel *and* an external checker must both reject it. **It is not
recorded as a specimen here because it has not been obtained and run.** A specimen that has not fired
in this repo is not a specimen; that is the registry's own standard and it applies to this row like
any other.
