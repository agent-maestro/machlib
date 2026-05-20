# MachLib EML Coverage Gap Ledger (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

Gap rows: 10

## gap_algebraic_identities_v0
- Lane: 1
- Description: algebraic identities
- Current status: COVERED_BY_EML_TRANSFORM
- Blockers: none listed
- Next safe local experiment: add identity-vs-constraint classifier tests
- EML record need: identity and rewrite records
- Zero-dependency risk: LOW
- Recommended priority: HIGH

## gap_polynomial_factorization_v0
- Lane: 1
- Description: polynomial factorization
- Current status: NEEDS_MACHLIB_PRIMITIVE
- Blockers: owned factorization primitive design
- Next safe local experiment: prototype finite-degree factorization cases
- EML record need: factorization seeds and exact solution records
- Zero-dependency risk: MEDIUM
- Recommended priority: HIGH

## gap_inequalities_v0
- Lane: 1
- Description: inequalities
- Current status: NEEDS_STRUCTURE_LAYER
- Blockers: ordered carrier assumptions
- Next safe local experiment: draft local ordered-carrier records
- EML record need: inequality rule records with assumptions
- Zero-dependency risk: MEDIUM
- Recommended priority: MEDIUM

## gap_exp_log_trig_pow_v0
- Lane: 2
- Description: exp/log/trig/pow symbolic functions
- Current status: NEEDS_MACHLIB_PRIMITIVE
- Blockers: owned primitive definitions, domain side-condition design
- Next safe local experiment: write placeholder records and primitive API notes
- EML record need: special-function primitive seeds
- Zero-dependency risk: MEDIUM
- Recommended priority: HIGH

## gap_finite_graphs_v0
- Lane: 3
- Description: finite graphs
- Current status: COVERED_BY_EML_TRANSFORM
- Blockers: none listed
- Next safe local experiment: validate bounded path witness records
- EML record need: graph object and witness records
- Zero-dependency risk: LOW
- Recommended priority: MEDIUM

## gap_sat_like_constraints_v0
- Lane: 3
- Description: SAT-like constraints
- Current status: COVERED_BY_EML_TRANSFORM
- Blockers: none listed
- Next safe local experiment: validate small assignment tables
- EML record need: boolean clause evaluation records
- Zero-dependency risk: LOW
- Recommended priority: MEDIUM

## gap_recurrences_v0
- Lane: 3
- Description: recurrences
- Current status: COVERED_BY_EML_TRANSFORM
- Blockers: none listed
- Next safe local experiment: validate bounded unfolding traces
- EML record need: finite recurrence records
- Zero-dependency risk: LOW
- Recommended priority: MEDIUM

## gap_typeclass_lite_structures_v0
- Lane: 4
- Description: typeclass-lite algebraic structures
- Current status: NEEDS_STRUCTURE_LAYER
- Blockers: record-local law schema
- Next safe local experiment: draft magma/monoid/order carrier records
- EML record need: structure records with local law checks
- Zero-dependency risk: LOW
- Recommended priority: HIGH

## gap_evidence_records_v0
- Lane: 5
- Description: evidence and proof records
- Current status: NEEDS_PROOF_LAYER_DESIGN
- Blockers: evidence schema needs validation policy
- Next safe local experiment: draft evidence rows with limitations
- EML record need: artifact status and limitation records
- Zero-dependency risk: LOW
- Recommended priority: HIGH

## gap_legacy_compatibility_v0
- Lane: 6
- Description: legacy Mathlib compatibility
- Current status: LEGACY_COMPAT_ONLY
- Blockers: must stay opt-in and outside release dependency
- Next safe local experiment: keep adapter boundaries as draft records
- EML record need: legacy boundary records only
- Zero-dependency risk: HIGH_IF_DEFAULTED
- Recommended priority: MEDIUM
