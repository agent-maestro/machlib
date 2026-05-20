# MachLib EML Lane Seed Records (2026-05-20)

Tier: OBSERVATION
Status: DRAFT_INTERNAL

Seed records created: 19

Each seed record is local-only and carries false guardrail flags for public readiness, upload allowance, external formal-library dependency, hardware requirement, and Forge compiler change requirement.

## cubic_dyadic_equilibrium_v0
- Lane: EML algebra core
- Title: Cubic dyadic equilibrium constraint normalization
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: cube, add, multiply, subtract, factor, root
- Path: `corpus/eml_lanes_draft/lane_1_algebra_core/cubic_dyadic_equilibrium_v0.json`

## linear_dyadic_identity_v0
- Lane: EML algebra core
- Title: Linear dyadic identity normalization
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: add, multiply, normalize
- Path: `corpus/eml_lanes_draft/lane_1_algebra_core/linear_dyadic_identity_v0.json`

## quadratic_zero_product_v0
- Lane: EML algebra core
- Title: Quadratic zero-product seed
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: square, subtract, factor, root
- Path: `corpus/eml_lanes_draft/lane_1_algebra_core/quadratic_zero_product_v0.json`

## inequality_sign_flip_v0
- Lane: EML algebra core
- Title: Bounded additive inequality rule seed
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: less_than, add, rewrite
- Path: `corpus/eml_lanes_draft/lane_1_algebra_core/inequality_sign_flip_v0.json`

## exp_log_formal_inverse_draft_v0
- Lane: Calculus and special functions
- Title: Formal exp/log inverse placeholder
- Coverage status: NEEDS_MACHLIB_PRIMITIVES
- Operator atoms: exp, log, compose, rewrite
- Path: `corpus/eml_lanes_draft/lane_2_calculus_special_functions/exp_log_formal_inverse_draft_v0.json`

## trig_pythagorean_symbolic_draft_v0
- Lane: Calculus and special functions
- Title: Symbolic trigonometric relation placeholder
- Coverage status: NEEDS_MACHLIB_PRIMITIVES
- Operator atoms: sin, cos, square, add
- Path: `corpus/eml_lanes_draft/lane_2_calculus_special_functions/trig_pythagorean_symbolic_draft_v0.json`

## pow_square_root_symbolic_draft_v0
- Lane: Calculus and special functions
- Title: Power and square-root symbolic placeholder
- Coverage status: NEEDS_MACHLIB_PRIMITIVES
- Operator atoms: sqrt, pow, square, domain_check
- Path: `corpus/eml_lanes_draft/lane_2_calculus_special_functions/pow_square_root_symbolic_draft_v0.json`

## finite_graph_path_check_v0
- Lane: Discrete algorithms
- Title: Finite graph path existence check
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: graph, edge, path, search
- Path: `corpus/eml_lanes_draft/lane_3_discrete_algorithms/finite_graph_path_check_v0.json`

## tiny_sat_clause_eval_v0
- Lane: Discrete algorithms
- Title: Tiny SAT-like clause evaluation
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: bool, or, and, not, evaluate
- Path: `corpus/eml_lanes_draft/lane_3_discrete_algorithms/tiny_sat_clause_eval_v0.json`

## recurrence_fib_step_v0
- Lane: Discrete algorithms
- Title: Finite recurrence step seed
- Coverage status: DRAFT_NEEDS_VALIDATION
- Operator atoms: recurrence, add, unfold, natural_index
- Path: `corpus/eml_lanes_draft/lane_3_discrete_algorithms/recurrence_fib_step_v0.json`

## typeclass_lite_magma_record_v0
- Lane: Typeclass-lite structures
- Title: Magma-like carrier record seed
- Coverage status: NEEDS_STRUCTURE_LAYER
- Operator atoms: carrier, binary_op, closure
- Path: `corpus/eml_lanes_draft/lane_4_typeclass_lite/typeclass_lite_magma_record_v0.json`

## typeclass_lite_monoid_record_v0
- Lane: Typeclass-lite structures
- Title: Monoid-like record with local laws
- Coverage status: NEEDS_STRUCTURE_LAYER
- Operator atoms: carrier, binary_op, identity, law_check
- Path: `corpus/eml_lanes_draft/lane_4_typeclass_lite/typeclass_lite_monoid_record_v0.json`

## typeclass_lite_ordered_carrier_v0
- Lane: Typeclass-lite structures
- Title: Ordered carrier draft record
- Coverage status: NEEDS_STRUCTURE_LAYER
- Operator atoms: carrier, relation, add, monotonicity
- Path: `corpus/eml_lanes_draft/lane_4_typeclass_lite/typeclass_lite_ordered_carrier_v0.json`

## lean_checkable_artifact_record_v0
- Lane: Proof and evidence records
- Title: Lean-checkable artifact evidence row
- Coverage status: NEEDS_PROOF_LAYER_DESIGN
- Operator atoms: evidence, checker_status, snapshot
- Path: `corpus/eml_lanes_draft/lane_5_proof_evidence_records/lean_checkable_artifact_record_v0.json`

## evidence_row_with_limitations_v0
- Lane: Proof and evidence records
- Title: Evidence row with explicit limitations
- Coverage status: NEEDS_PROOF_LAYER_DESIGN
- Operator atoms: evidence, limitation, classification
- Path: `corpus/eml_lanes_draft/lane_5_proof_evidence_records/evidence_row_with_limitations_v0.json`

## failed_attempt_record_v0
- Lane: Proof and evidence records
- Title: Failed attempt evidence record
- Coverage status: NEEDS_PROOF_LAYER_DESIGN
- Operator atoms: failure, diagnostic, next_step
- Path: `corpus/eml_lanes_draft/lane_5_proof_evidence_records/failed_attempt_record_v0.json`

## legacy_mathlib_header_opt_in_note_v0
- Lane: Legacy compatibility
- Title: Legacy header opt-in boundary note
- Coverage status: LEGACY_COMPAT_ONLY
- Operator atoms: legacy_flag, adapter_boundary, policy_check
- Path: `corpus/eml_lanes_draft/lane_6_legacy_compatibility/legacy_mathlib_header_opt_in_note_v0.json`

## legacy_adapter_boundary_record_v0
- Lane: Legacy compatibility
- Title: Legacy adapter boundary record
- Coverage status: LEGACY_COMPAT_ONLY
- Operator atoms: adapter, review_gate, translation
- Path: `corpus/eml_lanes_draft/lane_6_legacy_compatibility/legacy_adapter_boundary_record_v0.json`

## legacy_to_machlib_migration_stub_v0
- Lane: Legacy compatibility
- Title: Legacy-to-MachLib migration stub
- Coverage status: LEGACY_COMPAT_ONLY
- Operator atoms: migration, mapping, primitive_need
- Path: `corpus/eml_lanes_draft/lane_6_legacy_compatibility/legacy_to_machlib_migration_stub_v0.json`
