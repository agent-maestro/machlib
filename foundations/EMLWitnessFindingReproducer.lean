import MachLib.EMLPfaffianValidOnSinEqualityProved
import MachLib.WitnessResidualNestedTargetFullyUnconditional

/-!
# Option D — minimal public reproducer

See `../EML_WITNESS_FINDING_RESEARCH_NOTE.md` for the plain-language argument and
`../EML_WITNESS_FINDING_THEOREM_MAP.md` for the full spine. This file is neither of those — it is
the smallest possible entry point: two imports (not the whole `MachLib`), three `#print axioms`
commands, nothing else. Run it yourself:

```
cd foundations && lake env lean EMLWitnessFindingReproducer.lean
```

Each `#print axioms` line below prints the EXACT axiom footprint the kernel computes for that
theorem — not a claim, a kernel-checked fact anyone can re-derive by running this file. Compare the
output against `AxiomLedger.lean`'s `trustedFootprint`: every axiom named below should be in it, and
neither legacy discharge axiom (`eml_pfaffian_validon_from_sin_equality`/`_cos_equality`) should
appear anywhere in these three footprints.
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
