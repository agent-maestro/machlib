# `legacy_eml/` → `MachLib/` port plan

This document ranks every legacy file by porting difficulty and lists
the missing-from-MachLib lemmas each port needs. Updated 2026-05-01
after the first triage pass.

## Per-file summary

| File | Lines | Mathlib imports | Sorries | Theorems+lemmas | Difficulty |
|------|-------|----------------:|--------:|----------------:|-----------|
| `Float64.lean` | 61 | 0 (imports `MonogateEML.Runtime`) | 0 | 0 | trivial — no theorems to port |
| `Tactics.lean` | 166 | 0 (imports `MonogateEML.EMLDepth`, `Universality`) | 1 | 0 | trivial — no theorems to port |
| `Universality.lean` | 133 | 0 (imports `MonogateEML.EMLDepth`, `UpperBounds`) | 0 | 10 | **blocked**: requires `EMLTree` AST type that MachLib does not yet have |
| `Gamma.lean` | 90 | 3 | 0 | 6 | medium — needs `Gamma` axiomatisation in MachLib |
| `EMLDuality.lean` | 129 | 3 | 0 | 18 | medium — uses Complex, MachLib is real-only today |
| ~~`SelfMapConjugacy.lean`~~ | ~~150~~ | ~~2~~ | ~~0~~ | ~~12~~ | ✅ **PORTED 2026-05-01** — see `MachLib.SelfMapConjugacy` |
| `ModelAudit.lean` | 187 | 2 | 0 | 13 | medium — uses `Real.rpow` which MachLib lacks |
| `Runtime.lean` | 296 | 5 | 0 | 19 | medium — heavy Mathlib `Float` dependence |
| `HyperbolicPreservation.lean` | 224 | 4 | 0 | 34 | medium-high — `sinh`/`cosh` not yet in MachLib |
| `AddLowerBound.lean` | 403 | 4 | 1 | 34 | high — chain-order machinery |
| `MulLowerBound.lean` | 232 | 4 | 0 | 34 | high — chain-order machinery |
| `SubLowerBound.lean` | 226 | 4 | 0 | 31 | high — chain-order machinery |
| `DivLowerBound.lean` | 230 | 4 | 0 | 33 | high — chain-order machinery |
| `DivLowerBound3.lean` | 213 | 1 | 1 | 21 | high — chain-order machinery |
| `EMLDepth.lean` | 237 | 5 | 2 | 23 | high — depends on EMLTree AST |
| `ChainOrderAdditivity.lean` | 237 | 3 | 8 | 3 | hard — many open sorries |
| `UpperBounds.lean` | 1109 | 3 | 0 | **186** | hard volume but flat — biggest single-file payoff |
| `InfiniteZerosBarrier.lean` | 403 | 10 | 12 | 7 | hardest — most imports + most sorries |

## Recommended port order (first 5)

1. ~~**`SelfMapConjugacy.lean`** — 12 theorems, only 2 Mathlib facts not yet in MachLib (`exp_sub`, `log_ne_zero_of_pos_of_ne_one`). Add the helpers to `MachLib/Exp.lean` and `MachLib/Log.lean`, then port. **First port to attempt.**~~ ✅ **DONE 2026-05-01** — `exp_sub` + `log_ne_zero_of_pos_of_ne_one` shipped to `MachLib/Exp.lean` + `MachLib/Log.lean`; 12 theorems live in `MachLib/SelfMapConjugacy.lean`. Built clean in 3.2s, 0 sorries, 0 Mathlib.

2. ⚠️ **`HyperbolicPreservation.lean`** — **PARTIAL 2026-05-01** — 23 of 34 theorems ported to `MachLib/HyperbolicPreservation.lean` against new `MachLib/Hyperbolic.lean` axioms (sinh, cosh + addition / subtraction / double-angle / Pythagorean / ELC-form decomposition / link to existing Trig.tanh). 11 theorems deferred — they need a `norm_num`-equivalent (numeric witnesses like `sinh(log 2) = 3/4`) or a `ring` tactic (Pythagorean rearrangements, alt double-angle forms, squared half-angle). The unported theorems are documented inline in the legacy file. Foundations grew 658 → 952 lines.

3. **`Gamma.lean`** — adds a `MachLib/Gamma.lean` with the 6 Gamma facts the corpus actually uses (the analytic construction is not needed). Small, isolated, clean.

4. **`UpperBounds.lean`** — biggest payoff (186 theorems) but they're mostly algebraic and don't need new MachLib axioms; one big mechanical port that will 5-10x the foundation theorem count.

5. **EMLTree AST + `Universality.lean`** — requires defining `EMLTree`, `EMLTree.depth`, `EMLTree.eval`, `EML_k`, and `IsEMLElementary` in a new `MachLib/AST/` directory. Once that's in, `Universality.lean` ports with namespace-only changes. This is the path to closing out `Tactics.lean` and the chain-order suite.

## Open architecture questions

- **Real vs Complex.** Most legacy files use `Complex`; MachLib is real-only today. Decision: add `MachLib/Complex.lean` as an axiomatic ℂ analogous to `MachLib/Basic.lean`'s ℝ, and port complex-flavoured theorems on top of it. Alternative: port to ℝ-only versions where the legacy theorem doesn't actually need ℂ (some don't).

- **`rpow`.** Several legacy files use `Real.rpow x y = Real.exp (y * Real.log x)`. Adding `MachLib/RPow.lean` that defines this from existing axioms is straightforward — about 20-30 lines.

- **EMLTree AST.** The chain-order / depth / universality cluster all depend on the inductive `EMLTree` and the depth-indexed `EML_k k` family. None of MachLib's current foundations have this. Bringing it in is a one-time ~150-line addition to `MachLib/AST.lean`; everything downstream then ports cleanly.

- **`ring` and `norm_num` tactics.** The Hyperbolic port surfaced this clearly: 11 of 34 theorems need ring algebra (cosh²+sinh² rearrangements, double-angle alt forms) or numeric simplification (sinh(log 2) = 3/4). Without these tactics MachLib has to either axiomatize each identity (heavy) or skip it (incomplete port). A small ring tactic (decision procedure for commutative semirings, ~few hundred lines) and a basic `norm_num` (rational arithmetic on `OfNat` literals) would unblock most of the remaining legacy_eml ports plus future numeric work in industry verticals. **Highest leverage future addition to MachLib.**

## What's NOT in this plan

- Closing the 4 sorries in `Lane7_LogisticGrowth.lean` (the PETAL biological-dynamics file). That's a separate workstream tracked under G-004.

- The `_LegacyAggregator.lean.txt` file is documentation, not code; no port needed.
