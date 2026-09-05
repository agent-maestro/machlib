# Contributing to MachLib

MachLib accepts Lean 4 theorems and proofs about EML kernels, gates and audits that keep the
existing ones honest, and reproduction evidence. Everything below runs from `foundations/`.

## Before you write a proof

1. **Grep for the identifier you are about to type.** Lemmas are filed under the module that first
   needed them, not the family they belong to, and this project has re-proved existing theorems
   verbatim more than once. `grep -rn "theorem name" MachLib/` costs seconds.
2. **Read the tactic notes in [`CLAUDE.md`](CLAUDE.md).** There is no `ring`, `linarith`,
   `by_contra` or `set` here. The normalisers are `mach_ring` and `mach_mpoly`, and each has
   documented failure modes that look like success.
3. **Do the mathematics on paper first**, and check a number numerically if there is one. Price
   the discharges, not the reductions.

## What a change must satisfy

- **Reachable.** A new module must be imported, transitively, from `MachLib.lean`. A module the
  aggregator cannot reach is never built and never gated; `scripts/check_aggregator.sh` fails on
  a new orphan.
- **`sorryAx`-free.** `mach_ring` wraps its body in `try` and can leave a goal that Lean fills
  with a synthetic `sorry`, so a green build is not evidence. Run `#print axioms` on anything you
  care about; `tools/sorry_audit.lean` walks the whole environment.
- **No new axiom without a model.** Every trusted axiom is pinned by `AxiomLedger.lean` and
  witnessed in `monogate-lean`. Adding one means adding its Mathlib witness in the same change
  and regenerating `AXIOM_MANIFEST.md`; gate 13 fails otherwise.
- **Open questions are named, not hidden.** If a result is partial, state what it lacks as a
  `def … : Prop`, consume it as a hypothesis, and add a row to the obligations ledger at the end of
  `MachLib/EMLDepthTameness.lean` and its mirror in `CHANGELOG.md`. `tools/check_obligations.sh`
  checks both directions.
- **Counts are pasted, never remembered.** Any number in prose must be the output of a command;
  `tools/prose_counts_check.py` fails on drift for the ones it tracks.
- **All gates green** on a quiescent tree: `tools/check_all.sh`, exit code 0. It takes about
  fifteen minutes and refuses to certify a tree that changed while it ran.

## Commit messages

The body of a commit is a letter to the next session. Say why, not what; name the trade-off you
took and the one you rejected; record any quirk that cost you time; give the measured numbers,
read from the gate output after it finished, never predicted. See the last hundred commits for
the shape.

## Other contributions

- **Result cards** under `corpus/eml/` — a one-page card naming the theorem, its statement, its
  axiom footprint, and the command that checks it.
- **Reproduction evidence** under `reproduction/` — the package format is documented in
  `reproduction/rb_ekf/README.md`; a reproduction claim that withholds its evidence is not one.
- **Bug reports against claims.** If `foundations/docs/what_is_proven.md` says something you
  cannot reproduce in a few commands, that is a defect in the document. Open an issue naming the
  claim and the command.
