import json
from pathlib import Path

from tools.validate_capcard_marketplace_card import render_preview, validate_card


def card():
    return {
        "card_id": "eml_puzzle_evidence_kernel_DRAFT_2026_05_21",
        "candidate_id": "eml_puzzle_evidence_kernel",
        "display_name": "EML Puzzle Evidence Kernel",
        "marketplace_status": "INTERNAL_DRAFT_MARKETPLACE_READY",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "evidence_basis": ["bounded internal puzzle evidence", "no-upload gate"],
        "limitations": [
            "not a theorem prover",
            "not an open-problem result",
            "not certified safety",
            "not production controller evidence",
            "not PETAL/API uploaded",
            "not Hugging Face uploaded",
            "not production marketplace modified",
        ],
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
    }


def guardrails():
    row = {key: False for key in [
        "marketplace_upload_performed",
        "production_marketplace_modified",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "public_claim",
        "certified_safety_claim",
        "production_controller_claim",
        "theorem_proof_claim",
    ]}
    row.update({"candidate_id": "eml_puzzle_evidence_kernel", "visibility": "internal"})
    return row


def test_valid_card_passes():
    errors = validate_card(card(), guardrails(), "Not a theorem prover. Not production controller evidence.")
    assert errors == []


def test_action_true_fails():
    row = card()
    row["petal_api_upload_performed"] = True
    errors = validate_card(row, guardrails(), "")
    assert any("petal_api_upload_performed" in error for error in errors)


def test_public_visibility_fails():
    row = card()
    row["visibility"] = "public"
    assert validate_card(row, guardrails(), "")


def test_missing_boundary_fails():
    row = card()
    row["limitations"] = ["not a theorem prover"]
    errors = validate_card(row, guardrails(), "")
    assert any("missing boundary" in error for error in errors)


def test_positive_claim_fails():
    row = card()
    row["limitations"] = row["limitations"] + ["theorem proved"]
    errors = validate_card(row, guardrails(), "")
    assert any("forbidden positive claim" in error for error in errors)


def test_render_preview_outputs_files(tmp_path):
    render_preview(card(), tmp_path)
    assert (tmp_path / "index.html").exists()
    assert (tmp_path / "card_preview.json").exists()
    assert (tmp_path / "card_preview.md").exists()
    preview = json.loads((tmp_path / "card_preview.json").read_text())
    assert preview["not_public_marketplace"] is True
    assert "Not public marketplace" in (tmp_path / "index.html").read_text()
