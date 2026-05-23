"""Reviewer workflow helpers for CapCard Lab."""

from __future__ import annotations

from pathlib import Path

from .reporting import write_json
from .schema import REQUIRED_CANDIDATES

ALLOWED_DECISIONS = {"approve_internal_display", "request_revision", "keep_blocked", "retire_candidate"}
FORBIDDEN_DECISIONS = {"approve_public_marketplace", "approve_petal_upload", "approve_hf_upload", "approve_certified_safety", "approve_production_controller", "approve_production_marketplace"}


def validate_decision(decision: dict) -> tuple[bool, list[str]]:
    errors = []
    for field in ["reviewer_id", "reviewer_role", "review_date", "decision"]:
        if not decision.get(field):
            errors.append(f"missing {field}")
    if decision.get("decision") not in ALLOWED_DECISIONS:
        errors.append("forbidden or unknown decision")
    for field in ["public_claim", "petal_api_upload_performed", "huggingface_upload_performed", "certified_safety_claim", "production_controller_claim", "production_marketplace_modified"]:
        if decision.get(field) is not False:
            errors.append(f"{field} must be false")
    return not errors, errors


def write_workflow(repo_root: Path) -> dict:
    base = repo_root / "capcard_marketplace_drafts/reviewer_workflow_v2"
    sample = base / "sample_decisions"
    sample.mkdir(parents=True, exist_ok=True)
    queue = {"status": "PASS", "reviewer_queue": [{"candidate_id": cid, "action": "review_or_repair"} for cid in REQUIRED_CANDIDATES[:6]]}
    schema = {"allowed_decisions": sorted(ALLOWED_DECISIONS), "forbidden_decisions": sorted(FORBIDDEN_DECISIONS), "required_fields": ["reviewer_id", "reviewer_role", "review_date", "decision"]}
    write_json(base / "reviewer_queue_2026_05_21.json", queue)
    write_json(base / "reviewer_decision_schema_2026_05_21.json", schema)
    for cid in ["eml_puzzle", "qwen_puzzle", "1op_senses"]:
        (base / f"reviewer_packet_{cid}_2026_05_21.md").write_text(f"# Reviewer Packet: {cid}\n\nInternal review only. No public, PETAL/API, HF, production marketplace, safety, or controller approval.\n")
    decisions = {
        "valid_approve_internal_eml.json": {"reviewer_id": "internal-reviewer", "reviewer_role": "human_reviewer", "review_date": "2026-05-21", "decision": "approve_internal_display"},
        "valid_request_revision_qwen.json": {"reviewer_id": "internal-reviewer", "reviewer_role": "human_reviewer", "review_date": "2026-05-21", "decision": "request_revision"},
        "invalid_approve_public.json": {"reviewer_id": "internal-reviewer", "reviewer_role": "human_reviewer", "review_date": "2026-05-21", "decision": "approve_public_marketplace"},
        "invalid_petal_upload.json": {"reviewer_id": "internal-reviewer", "reviewer_role": "human_reviewer", "review_date": "2026-05-21", "decision": "approve_petal_upload"},
        "invalid_certified_safety.json": {"reviewer_id": "internal-reviewer", "reviewer_role": "human_reviewer", "review_date": "2026-05-21", "decision": "approve_certified_safety"},
    }
    false_fields = {
        "public_claim": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "production_marketplace_modified": False,
    }
    for name, row in decisions.items():
        row.update(false_fields)
        write_json(sample / name, row)
    return queue
