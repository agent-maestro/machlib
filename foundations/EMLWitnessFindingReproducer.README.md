# Reproducing the Option D result

`EMLWitnessFindingReproducer.lean` is a small, direct entry point into this arc's result: four
`import` lines (not the whole `MachLib` library — 279 of 478 modules, the actual transitive
closure needed, computed directly rather than guessed — see the closing note below for how) and
five `#print axioms` commands. No test framework, no CLI, nothing to install beyond a working
`lake` toolchain for this project.

## Run it

```
cd foundations
lake env lean EMLWitnessFindingReproducer.lean
```

Takes a few minutes (compiling the 279-module dependency chain from scratch if not already built).
Output is five axiom lists, one per `#print axioms` line — the kernel's own, exact account of
what each theorem depends on. Nothing here is a claim you have to take on trust; it's a command you
can run yourself.

## What to look for in the output

Each theorem's footprint (checked 2026-07-22, 83 / 83 / 82 / 70 / 54 axioms respectively) bottoms
out in a few kinds of entries:

- **Lean/Mathlib-independent core axioms** (`propext`, `Classical.choice`, `Quot.sound`) — standard
  for any classical Lean development, not specific to this codebase.
- **`MachLib.Real.*`/`MachLib.analytic_*`/`MachLib.IsAnalyticOnReals`** — MachLib's own foundational
  real-analysis model (basic facts about `sin`, `cos`, `exp`, `log`, `pi`, derivatives). This is the
  standing floor described in the research note's "three kinds of trust" section — untouched by
  this arc, no different in kind than trusting any base number system.
- **`Certcom.realToR`/`Certcom.real_fpbridge`/`Certcom.real_exp_rounds`/`Certcom.real_log_rounds`/
  `Certcom.floatOfR`/`Certcom.real_round_bounds`** — appear ONLY in headline 5's footprint (the
  Certcom-compiled-artifact connection). These are Certcom's own disclosed IEEE-754 rounding model
  — the honest floor any claim about a REAL compiled program has to stand on somewhere, since
  Lean's `Float` is opaque and "every basic float op is correctly rounded" cannot be proved
  in-Lean. Named apart from the ℝ-witnessed axioms above so the trust they carry is explicit (see
  `AxiomLedger.lean`'s own `disclosedTrusted` category).

**What should NOT appear, in any of the five lists:** `MachLib.eml_pfaffian_validon_from_sin_equality`
or `MachLib.eml_pfaffian_validon_from_cos_equality` — the two axioms this whole arc was about.
Their absence, for all five headlines including the axiom-discharge theorem itself, is the
non-circularity check: the proof that the axiom is vacuously true does not covertly lean on the
axiom to get there. Confirmed by directly running this file, not asserted.

Cross-check against `AxiomLedger.lean`'s `trustedFootprint` list (same directory) for the
authoritative, CI-enforced version of the same check, run automatically on every build rather than
by hand.

## The five headlines, plainly

1. **`no_tree_eq_sin_unconditional`** — no finite EML tree equals `sin`, at any point, at any depth.
2. **`eml_pfaffian_validon_from_sin_equality_proved`** — the axiom this whole arc set out to route
   around turns out to be provable outright (its hypothesis, from headline 1, is never satisfiable).
3. **`no_tree_eq_nestedTarget_fully_unconditional`** — the same closure, generalized to an entire
   family of nested-log targets (`sin`, `log(c + sin x)`, `log(d + log(c + sin x))`, ... arbitrarily
   deep), no restriction on the tree or the nesting.
4. **`no_tree_eq_periodic_target`** (added 2026-07-22) — the general case headlines 1 and 3 are
   both instances of: no finite EML tree equals ANY nonconstant, everywhere-continuous, periodic
   target, full stop.
5. **`eml_tree_grounded`** (added 2026-07-22, Certcom compositional handshake) — the abstract
   result connected to a REAL compiled artifact: an explicit, machine-computed closed-form error
   bound between an EML tree's exact mathematical value and a Certcom-compiled program's actual
   `Float`-rounded output, for the full grammar (`const`/`var`/`eml`, any depth or shape).

See `../EML_WITNESS_FINDING_RESEARCH_NOTE.md` for the argument in full, and
`../EML_WITNESS_FINDING_THEOREM_MAP.md` for how these connect to the spine and everything built
past it.

*Module-count methodology, so "279 of 478" isn't an unverifiable assertion*: computed by parsing
every file's own `import MachLib.X` lines and following the closure transitively, starting from
this reproducer's four imports (279 reached) versus starting from `MachLib.lean`, the top-level
aggregator that pulls in the whole library (478 reached) — the same direct-computation approach
this file's original version used, re-run rather than assumed still accurate after the library
grew.
