import json

from tools.simulate_capcard_marketplace import simulate


def write_card(path, **overrides):
    row = {
        "candidate_id": "eml_puzzle_evidence_kernel",
        "display_name": "EML Puzzle Evidence Kernel",
        "marketplace_status": "INTERNAL_MARKETPLACE_STRONG_CANDIDATE",
        "visibility": "internal",
        "tier": "OBSERVATION",
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
        "blockers": [],
        "next_safe_task": "human_review",
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
    path.write_text(json.dumps(row))


def test_eml_candidate_lands_in_promotion_queue(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    write_card(drafts / "eml.json")
    result = simulate(drafts, strict=True)
    assert result["ready_count"] == 1
    assert result["promotion_queue"][0]["candidate_id"] == "eml_puzzle_evidence_kernel"
    assert result["production_marketplace_modified"] is False


def test_qwen_lands_in_blocked_queue(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    review = tmp_path / "product_readiness"
    review.mkdir()
    (review / "qwen_puzzle_curriculum_repair_review_2026_05_21.json").write_text(json.dumps({
        "candidate_id": "qwen_puzzle_curriculum_pack",
        "marketplace_readiness": "BLOCKED_WITH_EXACT_FIX_LIST",
        "blockers": ["validation_status=warn", "solver_status=unknown"],
        "next_safe_task": "repair",
    }))
    result = simulate(drafts, strict=True)
    assert result["blocked_count"] == 1
    assert result["blocked_queue"][0]["candidate_id"] == "qwen_puzzle_curriculum_pack"


def test_no_uploads_or_public_claims_in_simulation(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    write_card(drafts / "eml.json")
    result = simulate(drafts, strict=True)
    assert result["petal_api_upload_performed"] is False
    assert result["huggingface_upload_performed"] is False
    assert result["public_claim"] is False


def test_stale_only_candidate_blocked(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    write_card(drafts / "stale.json", candidate_id="stale_only", command_center_reference_status="stale_reference_only")
    result = simulate(drafts, strict=True)
    assert result["ready_count"] == 0
    assert result["blocked_count"] == 1


def test_forbidden_claim_candidate_blocked(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    write_card(drafts / "bad.json", limitations=["theorem proved"])
    result = simulate(drafts, strict=True)
    assert result["ready_count"] == 0
    assert result["blocked_count"] == 1
