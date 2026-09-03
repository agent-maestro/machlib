# MachSig Phase 1 — Issues Ledger

## RESOLVED — the 220 / 243 axiom discrepancy is a NAMESPACE SCOPE difference

Carried from Phase 0 as unexplained. Measured directly over the environment:

```
MachLib.*  221      Certcom.*  22      other  15      MachLib + Certcom = 243
```

The live gate's **243 is exactly `MachLib.* + Certcom.*`**, and the residual `other = 15` matches the
count `CLAUDE.md` already gives for Lean's own kernel/compiler trust base (`propext`,
`Classical.choice`, `Quot.sound`, `sorryAx`, …). So the gate is `MachLib`-plus-`Certcom` scoped.

`axiom_ledger.json`'s **220** is `MachLib`-scoped and one short of the live `MachLib` count of 221.
That is *consistent with* the json being stale by one axiom, but it is **not established** — the json
is produced through `liveAxioms`, which additionally filters `isCompilerArtifact`, and no compiler
artifact was found in this scope. Regenerating `emit_ledger.py` and re-diffing is the cheap next step.

**Neither number was "chosen".** The gate's figure is now explained; the json's is narrowed to a
one-axiom question with a named way to settle it.

## RESOLVED — sorry count cross-validates

The census computes `depends_on_sorry` independently, via `Lean.collectAxioms` over every
declaration. It reports **1**. `tools/sorry_audit.lean` reports **1 sorryAx decl, allowlist 1,
exact correspondence**. Two separately-written paths over the same corpus agree.

(A note in this project's memory recalled "3 exceptions". That is stale; the audit's own output is
authoritative and says 1.)

## OPEN — population size differs from the figure in circulation

The census population is **13,486** non-internal `MachLib` constants. Project notes carry ~5,455 for
"declarations". These are different scopes — the smaller figure is theorems reached by the sorry
audit, the larger is every constant including `ctor`, `rec`, `inductive` and compiler-visible `def`s.
Both are correct for their scope; neither should be quoted bare. Recorded so the next reader does
not treat the difference as drift.

Breakdown: `theorem` 8887 · `def` 3645 · `ctor` 450 · `axiom` 221 · `rec` 140 · `inductive` 140 ·
`opaque` 3.

## OPEN — the census has no term-level extractor

Phase 0.5's grammar findings (`EMLTree`, `FTerm`, `EML`, `ElementaryEMLErf`) cannot be exercised
against a declaration-scoped census. Everything interesting about `trans1_head_counts`, `elet`
sharing and `cond` nodes needs a walker over **terms occurring inside declarations**. That is the
single largest gap between this census and the roadmap's intent, and it should be Phase 1b rather
than being smuggled into a signature later.

## OPEN — no canonical view exists for any object in this census

`canonical_views` is empty for all 13,486 records, with availability
`unsupported_representation`. Until a representation-scoped canonicalizer is wired in, **Phase 6's
canonicalisation-drift gate has nothing to watch.** This is a structural blocker on the roadmap's
most operationally useful phase, and it follows directly from Phase 0 Finding 3.

## OPEN — `ElementaryEMLErf` remains unassessed

Carried forward from Phase 0.5 unchanged, deliberately.


---

# Phase 1b additions

## RESOLVED — the term layer is viable but nearly degenerate

1,084 authored term records over 786 declarations. Verified reproducible (byte-identical repeat
run). But the features barely vary: `syntactic_node_count` has median **1**, `emltree_depth` puts
1,051 of 1,084 records into three values, and `elet`/`cond` total **5 occurrences each across the
whole corpus**. Full evidence in `TERM_CENSUS_REPORT.md`.

## OPEN — Phase 1's declaration census silently excluded `Certcom.*`

`extract.lean` filters `isMachLib`. The Forge-facing `EML` grammar lives under `Certcom`, so the
declaration census has no rows for it. This is the same scope boundary as the 220/243 axiom
discrepancy, reappearing in a different tool. The term extractor covers both namespaces; the
declaration extractor should be brought into line, and the population figure of 13,486 restated as
`MachLib`-only.

## OPEN — `FTerm` and `ElementaryEMLErf` have no walker

Both occur (85 and 25 raw constructor occurrences). Neither is extracted. `fOcc` was therefore not
available as a cross-validation partner, which is a real loss given how well the sorry-count
agreement worked in Phase 1.

## CLOSED-NEGATIVE — canonical views cannot be populated honestly

See `CANONICALIZER_BRIDGE.md`. Four clean data-level canonicalizers exist; none applies to the
dominant term population (`EMLTree`, 92% of records), and the representations that do have
canonicalizers appear in the corpus as bound variables rather than literals. Phase 6 is blocked on a
measured finding, not on an unbuilt feature.

## NOTE — `Name.isInternal` does not exclude compiler companions

The first term run yielded 2,685 records, of which **1,601 (60%)** came from `.match_`, `.eq_def`
and similar auto-generated declarations. `isInternal` returns false for these. Any future MachSig
extractor over declarations must filter them explicitly or its counts are inflated by more than
half.
