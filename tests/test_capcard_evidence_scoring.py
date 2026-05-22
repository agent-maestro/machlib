import json

from tools.score_capcard_evidence import score_card


def inventory():
    return {"sources": [
        {"candidate_link": "eml_puzzle_evidence_kernel", "marketplace_use": "direct_evidence"},
        {"candidate_link": "qwen_puzzle_curriculum_pack", "marketplace_use": "stale_reference_only"},
    ]}


def card(**overrides):
    row = {
        "candidate_id": "eml_puzzle_evidence_kernel",
        "evidence_basis": ["internal evidence ledger", "no-upload gate"],
        "source_artifacts": ["a.json", "a.json", "b.json"],
        "limitations": ["not certified safety", "not production controller evidence"],
        "requires_human_approval_for_production": True,
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


def test_eml_strong_card_scores_high():
    result = score_card(card(reviewer_id="r", review_date="2026-05-21"), inventory())
    assert result["score"] >= 85


def test_qwen_blocked_scores_lower():
    row = card(candidate_id="qwen_puzzle_curriculum_pack", blockers=["validation_status=warn", "solver_status=unknown"])
    assert score_card(row, inventory())["score"] < 85


def test_stale_only_scores_low():
    row = card(candidate_id="qwen_puzzle_curriculum_pack", source_artifacts=[])
    assert score_card(row, inventory())["stale_reference_count"] == 1


def test_petal_upload_true_caps_score():
    assert score_card(card(petal_api_upload_performed=True), inventory())["score"] <= 30


def test_hf_live_claim_caps_score():
    assert score_card(card(evidence_basis=["Hugging Face dataset live"]), inventory())["score"] <= 30


def test_certified_safety_caps_score():
    assert score_card(card(evidence_basis=["certified safety"]), inventory())["score"] <= 30


def test_missing_no_upload_gate_loses_points():
    lower = score_card(card(evidence_basis=["internal evidence ledger"]), inventory())["score"]
    higher = score_card(card(), inventory())["score"]
    assert lower < higher


def test_negative_boundary_language_safe():
    assert score_card(card(limitations=["not certified safety"]), inventory())["score"] > 30


def test_reviewer_identity_gains_points():
    plain = score_card(card(), inventory())["score"]
    reviewed = score_card(card(reviewer_id="r", review_date="2026-05-21"), inventory())["score"]
    assert reviewed > plain


def test_duplicate_sources_are_deduped():
    assert score_card(card(), inventory())["source_count"] == 2


def test_missing_source_paths_penalized_by_absence():
    assert score_card(card(source_artifacts=[]), inventory())["source_count"] == 2


def test_command_center_stale_not_direct_evidence():
    result = score_card(card(candidate_id="qwen_puzzle_curriculum_pack"), inventory())
    assert result["direct_source_count"] == 0


def test_token_like_secret_caps_score():
    assert score_card(card(evidence_basis=["hf_" + "A" * 24]), inventory())["score"] <= 30


def test_false_action_fields_score_full():
    assert score_card(card(), inventory())["forbidden_action_false_score"] == 100


def test_unknown_solver_penalty_counted():
    result = score_card(card(blockers=["solver_status=unknown"]), inventory())
    assert result["unknown_solver_penalty_count"] == 1
