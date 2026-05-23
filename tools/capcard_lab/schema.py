"""Shared schema constants for the local CapCard Lab."""

from __future__ import annotations

from dataclasses import dataclass


FALSE_ACTION_FIELDS = [
    "marketplace_upload_performed",
    "production_marketplace_modified",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "public_claim",
    "certified_safety_claim",
    "production_controller_claim",
    "theorem_proof_claim",
]

OPTIONAL_FALSE_FIELDS = [
    "deploy_performed",
    "hardware_action_performed",
    "upload_performed",
]

NOT_CLAIMED = [
    "not theorem prover",
    "not open-problem result",
    "not certified safety",
    "not production controller evidence",
    "not PETAL/API uploaded",
    "not Hugging Face uploaded",
    "not production marketplace modified",
]

FORBIDDEN_POSITIVE = [
    "theorem proved",
    "open problem solved",
    "certified safety",
    "production controller",
    "PETAL verified",
    "Hugging Face uploaded",
    "CapCard certified",
    "hardware validated",
    "medical advice",
    "veterinary advice",
]

SOURCE_FAMILIES = [
    "capcard_draft",
    "capcard_spec",
    "capcard_validator",
    "qwen_evidence",
    "puzzle_kernel_evidence",
    "petal_style_record",
    "capcard_style_record",
    "package_publish_record",
    "pypi_upload_record",
    "oneop_senses_record",
    "machlib_package_record",
    "evidence_reel_record",
    "electronics_curated_summary",
    "command_center_feed",
    "stale_command_center_reference",
    "reviewer_workflow",
    "adversarial_fixture",
    "unknown",
]

REQUIRED_CANDIDATES = [
    "eml_puzzle_evidence_kernel",
    "qwen_puzzle_curriculum_pack",
    "zero_mathlib_checker_package",
    "claim_boundary_package",
    "eml_records_package",
    "review_branch_packet_package",
    "machlib_package_readiness",
    "machlib_workbench_package",
    "eml_harness_package",
    "hybrid_trace_eml_package",
    "oneop_senses_animal_models",
    "machlib_evidence_reel",
    "capcard_tevv_lab",
    "electronics_curated_manifest_support",
    "mobius_pair_kernel_future_candidate",
]

DISPLAY_NAMES = {
    "eml_puzzle_evidence_kernel": "EML Puzzle Evidence Kernel",
    "qwen_puzzle_curriculum_pack": "Qwen Puzzle Curriculum Pack",
    "zero_mathlib_checker_package": "zero-mathlib-checker package",
    "claim_boundary_package": "claim-boundary package",
    "eml_records_package": "eml-records package",
    "review_branch_packet_package": "review-branch-packet package",
    "machlib_package_readiness": "MachLib package readiness",
    "machlib_workbench_package": "machlib-workbench package",
    "eml_harness_package": "eml-harness package",
    "hybrid_trace_eml_package": "hybrid-trace-eml package",
    "oneop_senses_animal_models": "1op Senses animal models",
    "machlib_evidence_reel": "MachLib Evidence Reel",
    "capcard_tevv_lab": "CapCard TEVV Lab",
    "electronics_curated_manifest_support": "Electronics curated manifest support",
    "mobius_pair_kernel_future_candidate": "Alpha-Beta Mobius Pair Kernel",
}

EXPECTED_BANDS = {
    "eml_puzzle_evidence_kernel": "STRONG_INTERNAL",
    "qwen_puzzle_curriculum_pack": "BLOCKED_REPAIR_REQUIRED",
    "zero_mathlib_checker_package": "STRONG_INTERNAL",
    "claim_boundary_package": "STRONG_INTERNAL",
    "eml_records_package": "READY_INTERNAL",
    "review_branch_packet_package": "READY_INTERNAL",
    "machlib_package_readiness": "BLOCKED_RETRY_OR_PENDING_PYPI",
    "machlib_workbench_package": "READY_INTERNAL_NOT_UPLOADED",
    "eml_harness_package": "READY_INTERNAL_NOT_UPLOADED",
    "hybrid_trace_eml_package": "READY_INTERNAL_NOT_UPLOADED",
    "oneop_senses_animal_models": "READY_INTERNAL_DEPLOY_REVIEW",
    "machlib_evidence_reel": "READY_INTERNAL",
    "capcard_tevv_lab": "READY_INTERNAL",
    "electronics_curated_manifest_support": "SUPPORT_ONLY_NO_HARDWARE",
    "mobius_pair_kernel_future_candidate": "READY_INTERNAL" ,
}


@dataclass(frozen=True)
class ValidationResult:
    status: str
    reasons: list[str]


def action_false_payload() -> dict[str, bool]:
    payload = {field: False for field in FALSE_ACTION_FIELDS}
    payload.update({field: False for field in OPTIONAL_FALSE_FIELDS})
    payload.setdefault("safe_to_display_internally", True)
    payload.setdefault("safe_to_publish_publicly", False)
    return payload
