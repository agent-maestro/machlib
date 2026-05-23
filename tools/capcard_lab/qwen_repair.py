"""Qwen repair workbench generation."""

from __future__ import annotations

from pathlib import Path

from .reporting import write_json, write_report


def build_qwen_repair(repo_root: Path) -> dict:
    rows = [
        {
            "row": 2,
            "source_path": "product_readiness/qwen_capcard_marketplace_candidates_2026_05_21.json",
            "validation_status": "warn",
            "solver_status": "unknown",
            "accepted_repair_evidence": False,
            "bounded_explanation_present": False,
            "reviewer_metadata_required": ["reviewer_id", "reviewer_role", "review_date", "repair_decision"],
            "decision": "still_blocked",
        },
        {
            "row": 3,
            "source_path": "product_readiness/qwen_capcard_marketplace_candidates_2026_05_21.json",
            "validation_status": "warn",
            "solver_status": "unknown",
            "accepted_repair_evidence": False,
            "bounded_explanation_present": False,
            "reviewer_metadata_required": ["reviewer_id", "reviewer_role", "review_date", "repair_decision"],
            "decision": "still_blocked",
        },
    ]
    data = {
        "status": "QWEN_KEEP_BLOCKED",
        "rows": rows,
        "exact_next_actions": [
            "locate accepted row 2 source and rerun local import/dryrun validation",
            "locate accepted row 3 source and rerun local import/dryrun validation",
            "write bounded solver_status explanation or repair evidence",
            "capture human reviewer identity/date before marketplace promotion",
        ],
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(repo_root / "product_readiness/qwen_repair_workbench_2026_05_21.json", data)
    write_report(
        repo_root / "reports/qwen_repair_workbench_2026_05_21.md",
        "Qwen Repair Workbench",
        [
            "- Decision: QWEN_KEEP_BLOCKED",
            "- Rows 2 and 3 still have warn/unknown blockers without accepted repair evidence.",
            "- Stale Command Center references cannot count as direct evidence.",
        ],
    )
    write_report(
        repo_root / "reports/qwen_repair_exact_next_actions_2026_05_21.md",
        "Qwen Repair Exact Next Actions",
        [f"- {action}" for action in data["exact_next_actions"]],
    )
    return data
