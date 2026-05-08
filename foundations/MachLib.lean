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

Zero Mathlib dependency. `lake build` verifies the entire library
in seconds.
-/
