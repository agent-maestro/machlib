import json
from pathlib import Path

from tools.validate_capcard_marketplace_candidates import (
    run_validation,
    validate_row,
)


def base_candidate(**overrides):
    row = {
        "candidate_id": "eml_puzzle_evidence_kernel",
        "display_name": "EML Puzzle Evidence Kernel",
        "marketplace_readiness": "INTERNAL_MARKETPLACE_STRONG_CANDIDATE",
        "visibility_recommendation": "internal",
        "evidence_basis": ["internal evidence ledger", "no-upload gate"],
        "limitations": [
            "not a theorem prover",
            "not an open-problem result",
            "not certified safety",
            "not production controller evidence",
            "not PETAL/API uploaded",
            "not Hugging Face uploaded",
            "not production marketplace modified",
        ],
        "not_claimed": [],
        "blockers": [],
        "next_safe_task": "next",
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }
    row.update(overrides)
    return row


def assert_fails(row):
    status, errors, _ = validate_row(row, strict=True)
    assert status == "fail"
    assert errors


def test_valid_eml_candidate_passes():
    status, errors, _ = validate_row(base_candidate(), strict=True)
    assert status == "pass"
    assert errors == []


def test_forbidden_petal_upload_true_fails():
    assert_fails(base_candidate(petal_api_upload_performed=True))


def test_forbidden_hf_upload_true_fails():
    assert_fails(base_candidate(huggingface_upload_performed=True))


def test_production_marketplace_true_fails():
    assert_fails(base_candidate(production_marketplace_modified=True))


def test_theorem_proof_claim_fails():
    assert_fails(base_candidate(theorem_proof_claim=True))


def test_certified_safety_claim_fails():
    assert_fails(base_candidate(certified_safety_claim=True))


def test_positive_theorem_text_fails():
    assert_fails(base_candidate(limitations=["theorem proved"]))


def test_petal_verified_text_fails():
    assert_fails(base_candidate(evidence_basis=["PETAL verified local card"]))


def test_hugging_face_dataset_live_text_fails():
    assert_fails(base_candidate(evidence_basis=["Hugging Face dataset live"]))


def test_production_controller_text_fails():
    assert_fails(base_candidate(limitations=["production controller"]))


def test_capcard_certified_text_fails():
    assert_fails(base_candidate(limitations=["CapCard certified"]))


def test_negative_boundary_text_allowed():
    row = base_candidate(limitations=base_candidate()["limitations"] + ["not certified safety"])
    status, errors, _ = validate_row(row, strict=True)
    assert status == "pass"
    assert errors == []


def test_missing_evidence_basis_fails():
    row = base_candidate()
    row.pop("evidence_basis")
    assert_fails(row)


def test_missing_limitations_fails():
    row = base_candidate()
    row.pop("limitations")
    assert_fails(row)


def test_missing_not_claimed_boundaries_fails_when_ready():
    assert_fails(base_candidate(limitations=["not a theorem prover"]))


def test_public_safe_without_public_review_fails():
    assert_fails(base_candidate(safe_to_publish_publicly=True))


def test_public_ready_internal_visibility_fails():
    assert_fails(base_candidate(marketplace_status="PUBLIC_READY_REVIEW", visibility="internal"))


def test_missing_traceability_path_fails():
    assert_fails(base_candidate(traceability_paths=["/tmp/definitely_missing_capcard_traceability.json"]))


def test_accepted_internal_row_needs_reviewer_and_date():
    assert_fails(base_candidate(accepted_internal_rows=[{"row_id": "row-1", "reviewer": "Ada"}]))


def test_soft_go_requires_checklist():
    assert_fails(base_candidate(decision="SOFT_GO"))


def test_unknown_solver_requires_bounded_explanation():
    assert_fails(base_candidate(solver_status="unknown"))


def test_unknown_solver_with_bounded_explanation_passes():
    row = base_candidate(solver_status="unknown", bounded_solver_status_explanation="bounded toy-solver observation only")
    status, errors, _ = validate_row(row, strict=True)
    assert status == "pass"
    assert errors == []


def test_no_upload_gate_missing_fails():
    assert_fails(base_candidate(no_upload_gate_present=False))


def test_token_like_secret_fails():
    assert_fails(base_candidate(evidence_basis=["hf_" + "A" * 24]))


def test_qwen_warn_unknown_blocks_readiness():
    row = base_candidate(
        candidate_id="qwen_puzzle_curriculum_pack",
        display_name="Qwen Puzzle Curriculum Pack",
        blockers=["validation_status=warn", "solver_status=unknown"],
    )
    assert_fails(row)


def test_qwen_repaired_can_pass_readiness():
    row = base_candidate(
        candidate_id="qwen_puzzle_curriculum_pack",
        display_name="Qwen Puzzle Curriculum Pack",
        blockers=["validation_status=warn", "solver_status=unknown"],
        row_repair_summary=[
            "repaired warning rows",
            "bounded explanation for solver_status=unknown",
            "human review accepted repair",
        ],
    )
    status, errors, _ = validate_row(row, strict=True)
    assert status == "pass"
    assert errors == []


def test_stale_command_center_reference_not_direct_evidence():
    row = base_candidate(command_center_reference_status="stale_reference_only")
    assert_fails(row)


def test_stale_command_center_reference_only_evidence_fails():
    row = base_candidate(
        evidence_basis=["stale command-center reference"],
        command_center_reference_status="stale_reference_only",
    )
    assert_fails(row)


def test_public_ready_external_visibility_can_pass():
    row = base_candidate(
        marketplace_readiness="PUBLIC_READY_REVIEW",
        marketplace_status="PUBLIC_READY_REVIEW",
        visibility="public_review",
        visibility_recommendation="internal",
        safe_to_publish_publicly=False,
    )
    status, errors, _ = validate_row(row, strict=True)
    assert status == "pass"
    assert errors == []


def test_duplicate_candidate_id_fails(tmp_path):
    candidates = {
        "candidates": [
            base_candidate(candidate_id="dup"),
            base_candidate(candidate_id="dup"),
        ]
    }
    path = tmp_path / "candidates.json"
    path.write_text(json.dumps(candidates))
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    result = run_validation(path, drafts, strict=True)
    assert result["status"] == "FAIL"
    assert result["fail_count"] >= 1
