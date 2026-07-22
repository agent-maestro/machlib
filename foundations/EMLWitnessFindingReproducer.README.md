# Reproducing the Option D result

`EMLWitnessFindingReproducer.lean` is the smallest entry point into this arc's result: two
`import` lines (not the whole `MachLib` library — about 240 of ~460 modules, the actual transitive
closure needed, computed directly rather than guessed) and three `#print axioms` commands. No test
framework, no CLI, nothing to install beyond a working `lake` toolchain for this project.

## Run it

```
cd foundations
lake env lean EMLWitnessFindingReproducer.lean
```

Takes a few minutes (compiling the ~240-module dependency chain from scratch if not already built).
Output is three axiom lists, one per `#print axioms` line — the kernel's own, exact account of
what each theorem depends on. Nothing here is a claim you have to take on trust; it's a command you
can run yourself.

## What to look for in the output

Each theorem's footprint (checked 2026-07-22, 83 / 83 / 82 axioms respectively) bottoms out in two
kinds of entries:

- **Lean/Mathlib-independent core axioms** (`propext`, `Classical.choice`, `Quot.sound`) — standard
  for any classical Lean development, not specific to this codebase.
- **`MachLib.Real.*`/`MachLib.analytic_*`/`MachLib.IsAnalyticOnReals`** — MachLib's own foundational
  real-analysis model (basic facts about `sin`, `cos`, `exp`, `log`, `pi`, derivatives). This is the
  standing floor described in the research note's "three kinds of trust" section — untouched by
  this arc, no different in kind than trusting any base number system.

**What should NOT appear, in any of the three lists:** `MachLib.eml_pfaffian_validon_from_sin_equality`
or `MachLib.eml_pfaffian_validon_from_cos_equality` — the two axioms this whole arc was about.
Their absence, for all three headlines including the axiom-discharge theorem itself, is the
non-circularity check: the proof that the axiom is vacuously true does not covertly lean on the
axiom to get there. Confirmed by directly running this file, not asserted.

Cross-check against `AxiomLedger.lean`'s `trustedFootprint` list (same directory) for the
authoritative, CI-enforced version of the same check, run automatically on every build rather than
by hand.

## The three headlines, plainly

1. **`no_tree_eq_sin_unconditional`** — no finite EML tree equals `sin`, at any point, at any depth.
2. **`eml_pfaffian_validon_from_sin_equality_proved`** — the axiom this whole arc set out to route
   around turns out to be provable outright (its hypothesis, from headline 1, is never satisfiable).
3. **`no_tree_eq_nestedTarget_fully_unconditional`** — the same closure, generalized to an entire
   family of nested-log targets (`sin`, `log(c + sin x)`, `log(d + log(c + sin x))`, ... arbitrarily
   deep), no restriction on the tree or the nesting.

See `../EML_WITNESS_FINDING_RESEARCH_NOTE.md` for the argument in full, and
`../EML_WITNESS_FINDING_THEOREM_MAP.md` for how these three connect to the other 13 spine files.
