import MachLib.Basic
import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.SelfMapConjugacy
import MachLib.Hyperbolic
import MachLib.HyperbolicPreservation
import MachLib.Forge
import MachLib.ForgeTest
import MachLib.Ring
import MachLib.RingTest
import MachLib.Linarith
import MachLib.LinarithTest
import MachLib.Lemmas
import MachLib.LinearCombination
import MachLib.Safety.TemporalFrequency
import MachLib.ProofSpine

/-!
# MachLib — top-level aggregator

The independent foundations for machine-native formal mathematics.

  * `MachLib.Basic`             — axiomatic ℝ (real numbers as an
                                  ordered field with Archimedean +
                                  completeness axioms exposed where
                                  needed)
  * `MachLib.Exp`               — real exponential
  * `MachLib.Log`               — real natural logarithm
  * `MachLib.Trig`              — sine, cosine, π, periodicity
  * `MachLib.EML`               — the eml(x,y) = exp(x) − log(y)
                                  primitive
  * `MachLib.SelfMapConjugacy`  — F16 self-map conjugacies (EAL/EXL,
                                  EML/EDL) ported from legacy_eml
  * `MachLib.Hyperbolic`        — sinh, cosh + ELC-form decomposition
                                  axioms (`tanh` lives in `Trig`)
  * `MachLib.Forge`             — derived lemmas for Forge-emitted
                                  kernel proofs (order, nonneg
                                  combinators); shipped 2026-05-01
                                  to ground the @verify(lean)
                                  binding chain identified in C-127
  * `MachLib.Ring`              — `mach_ring` tactic v1: closes
                                  the "linear-in-zeros" polynomial
                                  identities Forge emits for matrix
                                  cells, vector components, and lerp
                                  endpoints. Full polynomial
                                  reflection (Lagrange, four-square)
                                  is v2.
  * `MachLib.Linarith`          — `mach_positivity` + `mach_linarith`
                                  v1: closes `0 ≤ expr` / `0 < expr`
                                  via recursive structural
                                  decomposition over the Forge
                                  combinators. Fourier-Motzkin
                                  elimination for hypothesis-driven
                                  linear arithmetic is v2.
  * `MachLib.Lemmas`            — specific named lemmas filling the
                                  Forge-shape gaps in Basic / Trig
                                  / Exp (`max_le`, `exp_le_one`,
                                  `arccos_*`, `sqrt_pos`,
                                  `abs_cos_le_one`).
  * `MachLib.Safety.TemporalFrequency` — formal contract for the
                                  Phase 1 safety-verification
                                  protocol's `temporal_frequency`
                                  class. Provides
                                  `ForgeAnalyzerWitness` +
                                  `of_analyzer_witness` +
                                  `mul_bound_additive` +
                                  `add_bound_max`. Lands 2026-05-11
                                  as step 4 of 5 to close Moat 1's
                                  Phase 1 gating criterion.
  * `MachLib.ProofSpine`         — ten small checked obligations that
                                  connect EML / Forge / Explorer /
                                  CapCard surfaces to concrete MachLib
                                  artifacts.

Zero Mathlib dependency. `lake build` verifies the entire library
in seconds.
-/
