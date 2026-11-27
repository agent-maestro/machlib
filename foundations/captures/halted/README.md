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

## `v4.32.2-r3_2026-11-27T131210/`

`checkpoint.py --label v4.32.2-r3 --same-pin --freeze --void-ok
kernel_replay=Amendment-5-destination-externally-unreplayed`, library `075f6730` (PR #7's branch with
master `b902cf03` merged in, on the owner's 2026-11-27 ruling to bring PR #7 up to date). Base chosen by
the tool: `snapshots/v4.32.2-r2` (library `50d9c56c`).

**What it measured.** Every gate green: criterion 7 (Lean4Lean `408edad`) exit 0 (832 / 832 modules,
21,300 declarations), criterion 1 void under Amendment 5. Identity identical. Theorems 112 -> 112, 0
lost; axioms 217 -> 202, 15 removed: 13 are theorems now, each tied to the commit that proved it
(`61f7ac5e`, `97d4c6d8`, `1357f71e`).

**Why it halted.** The other two, `interval_scale_unit_lit_le` and `interval_weight_sum_le`, read as
UNATTRIBUTED. Both were removed by `37ff5477` (2026-10-27, "remove the two false Forge-bridge
axioms"), and that commit's new docstrings QUOTE the old declarations ("Until 2026-10-27 this was
`axiom interval_scale_unit_lit_le"). The attribution's patterns were not anchored, so the quote counted
as the axiom still declared, and the pickaxe saw one occurrence removed and one added and never listed
the commit. An instrument defect, the same family as the 3-of-39 halt of 2026-10-22 (`50d9c56c`).

**What it led to.** `same_pin.removal_commit` anchors both patterns at a line start (every real
declaration in the corpus starts its line; git's pickaxe regex is compiled with REG_NEWLINE), and its
history canaries gain these two removals, expected at `37ff5477`. The re-run is the sealed `v4.32.2-r3`.
