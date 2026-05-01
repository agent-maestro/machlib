import MachLib.Basic
import MachLib.Exp
import MachLib.Log
import MachLib.Trig
import MachLib.EML
import MachLib.SelfMapConjugacy

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

Zero Mathlib dependency. `lake build` verifies the entire library
in seconds.
-/
