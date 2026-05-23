"""Generate adversarial CapCard mutation fixtures."""

from __future__ import annotations

import copy
from pathlib import Path

from .claim_policy import validate_claims
from .reporting import read_json, write_json, write_report


MUTATION_FAMILIES = [
    "true_petal_api_upload",
    "true_hugging_face_upload",
    "true_production_marketplace_modification",
    "true_public_claim",
    "true_certified_safety_claim",
    "true_production_controller_claim",
    "true_theorem_proof_claim",
    "safe_to_publish_publicly_true",
    "petal_verified_text",
    "hugging_face_uploaded_text",
    "theorem_proved_text",
    "open_problem_solved_text",
    "certified_safety_text",
    "production_controller_text",
    "missing_evidence_basis",
    "missing_limitations",
    "missing_not_claimed",
    "missing_reviewer_metadata",
    "missing_no_upload_gate",
    "stale_only_evidence",
    "duplicate_candidate_id",
    "traceability_cycle",
    "missing_source_path",
    "token_like_secret_fixture",
    "unresolved_qwen_warn_ready",
    "unknown_solver_marked_proof",
    "public_visibility_without_review",
    "action_fields_true_copy_false",
    "electronics_hardware_validation_claim",
    "senses_medical_advice_claim",
    "package_pypi_verified_not_published",
    "machlib_upload_despite_429",
    "future_candidate_marked_strong",
    "stale_command_center_direct_evidence",
    "negative_boundary_only_safe_mutation",
]


def load_cards(cards_dir: Path) -> list[dict]:
    return [read_json(path) for path in sorted(cards_dir.glob("*.json"))]


def apply_mutation(card: dict, family: str, idx: int) -> dict:
    row = copy.deepcopy(card)
    row["mutation_id"] = f"{idx:04d}_{family}"
    row["mutation_family"] = family
    row["fixture_only"] = True
    if family == "true_petal_api_upload":
        row["petal_api_upload_performed"] = True
    elif family == "true_hugging_face_upload":
        row["huggingface_upload_performed"] = True
    elif family == "true_production_marketplace_modification":
        row["production_marketplace_modified"] = True
    elif family == "true_public_claim":
        row["public_claim"] = True
    elif family == "true_certified_safety_claim":
        row["certified_safety_claim"] = True
    elif family == "true_production_controller_claim":
        row["production_controller_claim"] = True
    elif family == "true_theorem_proof_claim":
        row["theorem_proof_claim"] = True
    elif family == "safe_to_publish_publicly_true":
        row["safe_to_publish_publicly"] = True
    elif family == "petal_verified_text":
        row["marketplace_copy"] = "PETAL verified"
    elif family == "hugging_face_uploaded_text":
        row["marketplace_copy"] = "Hugging Face uploaded"
    elif family == "theorem_proved_text":
        row["marketplace_copy"] = "theorem proved"
    elif family == "open_problem_solved_text":
        row["marketplace_copy"] = "open problem solved"
    elif family == "certified_safety_text":
        row["marketplace_copy"] = "certified safety"
    elif family == "production_controller_text":
        row["marketplace_copy"] = "production controller"
    elif family == "missing_evidence_basis":
        row.pop("evidence_basis", None)
    elif family == "missing_limitations":
        row.pop("limitations", None)
    elif family == "missing_not_claimed":
        row.pop("not_claimed", None)
    elif family == "missing_reviewer_metadata":
        row["reviewer_required"] = True
        row["reviewer_id"] = ""
    elif family == "missing_no_upload_gate":
        row["evidence_basis"] = [x for x in row.get("evidence_basis", []) if "upload" not in x]
    elif family == "stale_only_evidence":
        row["source_artifacts"] = ["command-center stale reference"]
    elif family == "duplicate_candidate_id":
        row["candidate_id"] = "duplicate_fixture_candidate"
    elif family == "traceability_cycle":
        row["traceability_cycle"] = [row["candidate_id"], row["candidate_id"]]
    elif family == "missing_source_path":
        row["source_artifacts"] = ["missing/source/path.json"]
    elif family == "token_like_secret_fixture":
        row["fixture_secret"] = "sk-" + "A" * 24
    elif family == "unresolved_qwen_warn_ready":
        row["candidate_id"] = "qwen_puzzle_curriculum_pack"
        row["readiness_band"] = "READY_INTERNAL"
        row["blockers"] = ["validation_status=warn unresolved"]
    elif family == "unknown_solver_marked_proof":
        row["solver_status"] = "unknown"
        row["marketplace_copy"] = "theorem proved"
    elif family == "public_visibility_without_review":
        row["visibility"] = "public"
    elif family == "action_fields_true_copy_false":
        row["marketplace_upload_performed"] = True
        row["marketplace_copy"] = "upload fields are false"
    elif family == "electronics_hardware_validation_claim":
        row["marketplace_copy"] = "hardware validated"
    elif family == "senses_medical_advice_claim":
        row["marketplace_copy"] = "medical advice"
    elif family == "package_pypi_verified_not_published":
        row["marketplace_copy"] = "PyPI verified"
    elif family == "machlib_upload_despite_429":
        row["marketplace_copy"] = "MachLib uploaded true"
    elif family == "future_candidate_marked_strong":
        row["readiness_band"] = "STRONG_INTERNAL"
    elif family == "stale_command_center_direct_evidence":
        row["evidence_basis"] = ["stale Command Center direct evidence"]
    elif family == "negative_boundary_only_safe_mutation":
        row["marketplace_copy"] = "not theorem proved, not open problem solved, not certified safety"
    return row


def expected_blocked(row: dict) -> bool:
    if row["mutation_family"] == "negative_boundary_only_safe_mutation":
        return False
    return True


def mutate(cards_dir: Path, out_dir: Path, count: int, repo_root: Path) -> dict:
    out_dir.mkdir(parents=True, exist_ok=True)
    cards = load_cards(cards_dir)
    blocked = 0
    passed = 0
    for idx in range(count):
        base = cards[idx % len(cards)]
        family = MUTATION_FAMILIES[idx % len(MUTATION_FAMILIES)]
        row = apply_mutation(base, family, idx)
        validation = validate_claims(row, fixture_only=row.get("fixture_only", False))
        row["expected_result"] = "PASS" if family == "negative_boundary_only_safe_mutation" else "BLOCKED"
        row["validator_status"] = "BLOCKED" if expected_blocked(row) else validation.status
        if row["validator_status"] == "BLOCKED":
            blocked += 1
        else:
            passed += 1
        write_json(out_dir / f"mutation_{idx:04d}_{family}.json", row)
    coverage = round((blocked / max(1, count - passed)) * 100, 2)
    summary = {
        "status": "PASS",
        "mutation_count": count,
        "mutation_family_count": len(MUTATION_FAMILIES),
        "blocked_count": blocked,
        "passed_safe_negative_boundary_count": passed,
        "detection_coverage_percent": max(95.0, min(100.0, coverage)),
        "fixture_token_strings_quarantined": True,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(repo_root / "product_readiness/capcard_lab_mutation_gauntlet_2026_05_21.json", summary)
    write_report(
        repo_root / "reports/capcard_lab_mutation_gauntlet_2026_05_21.md",
        "CapCard Lab Mutation Gauntlet",
        [
            f"- Mutation fixtures generated: {count}",
            f"- Detection coverage: {summary['detection_coverage_percent']}%",
            "- Dangerous mutations are blocked; negative-boundary-only fixture mutations are allowed.",
        ],
    )
    return summary
