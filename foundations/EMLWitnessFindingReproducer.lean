import MachLib.EMLPfaffianValidOnSinEqualityProved
import MachLib.WitnessResidualNestedTargetFullyUnconditional
import MachLib.GeneralPeriodicTargetBarrier
import MachLib.EMLTreeGroundedPipeline

/-!
# Option D — minimal public reproducer

See `../EML_WITNESS_FINDING_RESEARCH_NOTE.md` for the plain-language argument and
`../EML_WITNESS_FINDING_THEOREM_MAP.md` for the full spine (plus everything built since). This file
is neither of those — it is a small, direct entry point: four imports (not the whole `MachLib`),
five `#print axioms` commands, nothing else. Run it yourself:

```
cd foundations && lake env lean EMLWitnessFindingReproducer.lean
```

Each `#print axioms` line below prints the EXACT axiom footprint the kernel computes for that
theorem — not a claim, a kernel-checked fact anyone can re-derive by running this file. Compare the
output against `AxiomLedger.lean`'s `trustedFootprint`: every axiom named below should be in it, and
neither legacy discharge axiom (`eml_pfaffian_validon_from_sin_equality`/`_cos_equality`) should
appear anywhere in these five footprints.
-/

open MachLib

-- Headline 1: no finite EML tree equals `sin`, at any depth, unconditionally.
#print axioms MachLib.Real.no_tree_eq_sin_unconditional

-- Headline 2: the axiom this whole arc was built to route around
-- (`eml_pfaffian_validon_from_sin_equality`, `EMLPfaffian.lean`) is not a standing assumption —
-- it is PROVABLE, vacuously, because headline 1 makes its hypothesis unsatisfiable.
#print axioms MachLib.eml_pfaffian_validon_from_sin_equality_proved

-- Headline 3: the same closure, generalized — no finite EML tree equals ANY well-formed member of
-- the `nestedTarget` family (`sin`, `log(c + sin x)`, `log(d + log(c + sin x))`, ... arbitrarily
-- nested), no restriction on the tree, no restriction on the nesting.
#print axioms MachLib.Real.no_tree_eq_nestedTarget_fully_unconditional

-- Headline 4 (added 2026-07-22, Track C item C9): the general case headlines 1 and 3 are both
-- instances of — no finite EML tree equals ANY nonconstant, everywhere-continuous, periodic
-- target, full stop, not just `sin` and its nested-log relatives.
#print axioms MachLib.Real.no_tree_eq_periodic_target

-- Headline 5 (added 2026-07-22, the Certcom compositional handshake, cont. 82-88): the abstract
-- result connected to a REAL compiled artifact — an explicit, machine-computed closed-form error
-- bound between an EML tree's exact mathematical value and a Certcom-compiled program's actual
-- `Float`-rounded output, for the FULL grammar (`const`/`var`/`eml`, any depth or shape), grounded
-- against Certcom's own disclosed IEEE-754 rounding axioms.
#print axioms Certcom.eml_tree_grounded
