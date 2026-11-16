# Halted captures

Captures that HALTED and were therefore not sealed into `snapshots/`. They are kept because the halt
is part of the record: the repo keeps INCOMPLETE and REFUTED outcomes, and a halt that lived only in
`/tmp` would have depended on the machine not rebooting. Each directory carries its own `SHA256SUMS`
(`sha256sum -c SHA256SUMS` from inside it).

## `v4.32.2-r2_2026-10-22T230618/`

`checkpoint.py --label v4.32.2-r2 --compare-to snapshots/v4.14.0-baseline
--void-ok kernel_replay=Amendment-5-destination-externally-unreplayed`, library `73860d13`.

**What it measured.** Every gate green: criterion 7 (Lean4Lean `408edad`) exit 0, and criterion 1
void (lean4checker has no tag ≥ v4.29, Amendment 5 cited). Headline count 112 / 112 / 112 across
all three derivations.

**Why it halted.** Counts and footprints moved against the July v4.14.0 baseline: 252 → 217 axioms
pinned, 57 → 112 headlines, 5 → 0 derivations; 56 footprints changed, 55 theorems gained, 0 lost.
The pin has not moved since 2026-07-30. What moved is the library. The baseline was frozen to
attribute TOOLCHAIN drift, so measuring today's library against it reads development as migration.

**What it led to.** The owner's ruling of 2026-10-22, recorded in `BUMP_PLAN.md` Amendment 7: a grade
change needs a sealed snapshot. `checkpoint.py --same-pin` therefore compares against the newest
sealed capture on the same pin, and seals only if every difference is attributed mechanically. What
that produced is recorded in `MIGRATION_LOG.md`, DESTINATION, UPGRADE.

**The 5 → 0 derivations are not a loss** (measured, `5841ea60` and `2d2f59c0`):

| derivation (July) | now |
|---|---|
| `archimedean` via `archimedean_derivable` | **theorem** at its declaration site (`Basic.lean`, from `sup_exists`) |
| `one_div_pos_of_pos` via `one_div_pos_derivable` | **theorem** (`Basic.lean`) |
| `HasDerivAt_neg` via `hasDerivAt_neg_derivable` | **theorem** (`Differentiation.lean`) |
| `HasDerivAt_sub` via `hasDerivAt_sub_derivable` | **theorem** (`Differentiation.lean`) |
| `zero_ne_one_ax` via `zero_ne_one_derivable` | **still an axiom, deliberately**: primitive in the field, derivable only with the order. Converting it leaked the order into 33 algebra-spine theorems. Its derivation still exists (`AxiomMinimality.lean`) and is checked under `AxiomLedger.subTheoryPrimitives` (check 9) |

The policy behind the 4 conversions is "provable means proved": `derivableAxioms` is empty and must
stay empty, so a derivation is a reason to convert, not to record.
