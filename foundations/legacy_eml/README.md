# `legacy_eml/` — transitional Mathlib-dependent corpus (v0.1)

These 17 Lean files are imported from the original `monogate-lean`
repository as the seed for MachLib's theorem corpus. They depend
on Mathlib for `Real`, `Real.exp`, `Real.log`, and the special-
function machinery.

Files ported up into `foundations/MachLib/` (deleted from here):

  * `SelfMapConjugacy.lean` → `MachLib.SelfMapConjugacy`
    (12 theorems on F16 self-map conjugacies, ported 2026-05-01)

**This is intentional and temporary.** Phase 1 of the MachLib
roadmap (Sessions I-001 through I-004) builds independent
foundations under `foundations/MachLib/` and ports the relevant
theorems off Mathlib. Once a theorem here has been ported, its
file moves up into `foundations/MachLib/` (or a thematic
subdirectory) and the legacy entry is deleted.

The aggregator-text file `_LegacyAggregator.lean.txt` is the
former `MonogateEML.lean` aggregator, kept here as documentation
of what lake used to build. The active `lakefile.lean` lives at
`foundations/lakefile.lean` and starts empty in v0.1; Phase 1
points it at the new `MachLib/` modules as they appear.

Until Phase 1 is complete, this directory IS NOT BUILT by the
default lake target. Building it requires re-installing Mathlib
under `foundations/.lake/packages/` (the same toolchain pin as
the upstream `monogate-lean` repository).
