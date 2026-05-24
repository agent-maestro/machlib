import json
from pathlib import Path

from tools.qwen_capcard_lab.evidence_miner import (
    artifact_type,
    build_inventory,
    classify_evidence,
    matched_terms,
    row_relevance,
)


def test_matched_terms_finds_qwen_and_solver_status():
    terms = matched_terms("Qwen_Puzzle_Curriculum row 2 solver_status unknown")
    assert "Qwen_Puzzle_Curriculum" in terms
    assert "solver_status" in terms
    assert "unknown" in terms


def test_artifact_type_jsonl():
    assert artifact_type(Path("accepted_internal_capcard_pack_rows.jsonl")) == "jsonl"


def test_row2_relevance_from_text():
    assert row_relevance(Path("x.md"), "accepted row 2 has validation_status warn", 2)


def test_row3_relevance_from_json_source_row():
    assert row_relevance(Path("x.json"), '{"source_row": 3, "solver_status": "unknown"}', 3)


def test_direct_evidence_candidate_requires_row_and_marker():
    row = classify_evidence(
        Path("product_readiness/direct.json"),
        "row 2 human review accepted repair",
        ["row 2", "accepted repair"],
    )
    assert row.direct_evidence_candidate is True
    assert row.evidence_strength == "DIRECT"


def test_blocked_marker_prevents_direct():
    row = classify_evidence(
        Path("product_readiness/blocked.json"),
        "row 2 accepted repair evidence missing; no accepted repair evidence",
        ["row 2", "accepted repair"],
    )
    assert row.direct_evidence_candidate is False
    assert row.evidence_strength == "SUPPORTING"


def test_stale_reference_classification():
    row = classify_evidence(
        Path("command_center_feeds/qwen.json"),
        "row 3 command-center pasted row cannot count as direct evidence",
        ["row 3"],
    )
    assert row.stale_reference_only is True
    assert row.evidence_strength == "STALE_REFERENCE_ONLY"


def test_supporting_context_when_no_direct_marker():
    row = classify_evidence(Path("reports/qwen.md"), "row 2 solver_status unknown", ["row 2"])
    assert row.evidence_strength == "SUPPORTING"


def test_irrelevant_when_no_terms():
    row = classify_evidence(Path("reports/other.md"), "unrelated text", [])
    assert row.evidence_strength == "IRRELEVANT"


def test_build_inventory_counts_direct_candidate(tmp_path):
    root = tmp_path
    base = root / "product_readiness"
    base.mkdir()
    (base / "qwen.json").write_text("row 2 human review accepted repair")
    inventory = build_inventory(root, roots=["product_readiness"])
    assert inventory["files_scanned"] == 1
    assert inventory["direct_evidence_candidate_count"] == 1
    assert inventory["direct_repair_evidence_found"] is True


def test_build_inventory_counts_stale_only(tmp_path):
    root = tmp_path
    base = root / "command_center_feeds"
    base.mkdir()
    (base / "qwen.json").write_text("row 3 stale reference only")
    inventory = build_inventory(root, roots=["command_center_feeds"])
    assert inventory["stale_reference_only_count"] == 1
    assert inventory["direct_repair_evidence_found"] is False


def test_inventory_guardrail_fields_false(tmp_path):
    root = tmp_path
    base = root / "reports"
    base.mkdir()
    (base / "qwen.md").write_text("Qwen Puzzle row 2 warn unknown")
    inventory = build_inventory(root, roots=["reports"])
    for key in [
        "public_ready",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "production_marketplace_modified",
        "fine_tune_performed",
        "cloud_model_used",
        "public_claim",
        "certified_safety_claim",
        "production_controller_claim",
        "theorem_proof_claim",
    ]:
        assert inventory[key] is False


def test_inventory_json_serializable(tmp_path):
    root = tmp_path
    base = root / "reports"
    base.mkdir()
    (base / "qwen.md").write_text("qwen_puzzle_curriculum_pack row 3")
    json.dumps(build_inventory(root, roots=["reports"]))
