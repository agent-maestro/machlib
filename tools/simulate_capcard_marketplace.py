#!/usr/bin/env python3
"""Simulate an internal CapCard marketplace queue from local draft cards."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.validate_capcard_marketplace_candidates import validate_row


FALSE_RESULT = {
    "production_marketplace_modified": False,
    "petal_api_upload_performed": False,
    "huggingface_upload_performed": False,
    "public_claim": False,
}


def load_draft_cards(drafts: Path) -> list[dict[str, Any]]:
    cards: dict[str, dict[str, Any]] = {}
    for path in sorted(drafts.glob("*.json")):
        data = json.loads(path.read_text())
        cid = data.get("candidate_id")
        if not cid:
            continue
        cards.setdefault(cid, {"candidate_id": cid})
        cards[cid].update({k: v for k, v in data.items() if not k.startswith("_")})
        cards[cid].setdefault("source_paths", []).append(str(path))
    qwen_review = Path("product_readiness/qwen_puzzle_curriculum_repair_review_2026_05_21.json")
    if qwen_review.exists():
        data = json.loads(qwen_review.read_text())
        cid = data.get("candidate_id")
        cards.setdefault(cid, {"candidate_id": cid})
        cards[cid].update({
            "display_name": "Qwen Puzzle Curriculum Pack",
            "marketplace_readiness": data.get("marketplace_readiness"),
            "visibility_recommendation": "internal_marketplace",
            "evidence_basis": ["Qwen puzzle curriculum evidence ledger"],
            "limitations": [
                "not a theorem prover",
                "not an open-problem result",
                "not certified safety",
                "not production controller evidence",
                "not PETAL/API uploaded",
                "not Hugging Face uploaded",
                "not production marketplace modified",
            ],
            "blockers": data.get("blockers", []),
            "next_safe_task": data.get("next_safe_task"),
            "marketplace_upload_performed": False,
            "production_marketplace_modified": False,
            "petal_api_upload_performed": False,
            "huggingface_upload_performed": False,
            "public_claim": False,
            "certified_safety_claim": False,
            "production_controller_claim": False,
            "theorem_proof_claim": False,
        })
    return list(cards.values())


def lifecycle_state(card: dict[str, Any], status: str) -> str:
    if status != "pass":
        return "PUBLIC_REVIEW_BLOCKED"
    readiness = card.get("marketplace_readiness") or card.get("marketplace_status")
    if readiness == "INTERNAL_MARKETPLACE_STRONG_CANDIDATE":
        return "INTERNAL_MARKETPLACE_STRONG_CANDIDATE"
    if readiness == "INTERNAL_DRAFT_MARKETPLACE_READY":
        return "VALIDATED_CARD"
    if readiness == "BLOCKED_WITH_EXACT_FIX_LIST":
        return "PUBLIC_REVIEW_BLOCKED"
    return "REVIEWED_INTERNAL"


def simulate(drafts: Path, strict: bool) -> dict[str, Any]:
    cards = load_draft_cards(drafts)
    reviewer_queue = []
    promotion_queue = []
    blocked_queue = []
    for card in cards:
        normalized = dict(card)
        if "marketplace_readiness" not in normalized and "marketplace_status" in normalized:
            normalized["marketplace_readiness"] = normalized["marketplace_status"]
        if "visibility_recommendation" not in normalized and "visibility" in normalized:
            normalized["visibility_recommendation"] = normalized["visibility"]
        normalized.setdefault("blockers", [])
        normalized.setdefault("next_safe_task", "human_review")
        status, errors, warnings = validate_row(normalized, strict=strict)
        entry = {
            "candidate_id": normalized["candidate_id"],
            "display_name": normalized.get("display_name"),
            "validation_status": status,
            "lifecycle_state": lifecycle_state(normalized, status),
            "errors": errors,
            "warnings": warnings,
        }
        reviewer_queue.append(entry)
        if status == "pass" and normalized.get("candidate_id") == "eml_puzzle_evidence_kernel":
            promotion_queue.append(entry)
        else:
            blocked_queue.append(entry)
    return {
        "candidate_count": len(cards),
        "ready_count": len(promotion_queue),
        "blocked_count": len(blocked_queue),
        "reviewer_queue": reviewer_queue,
        "promotion_queue": promotion_queue,
        "blocked_queue": blocked_queue,
        **FALSE_RESULT,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--drafts", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    result = simulate(args.drafts, args.strict)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    status = "PASS" if result["ready_count"] >= 1 else "FAIL"
    print(
        "CAPCARD_MARKETPLACE_SIMULATION",
        result["candidate_count"],
        result["ready_count"],
        result["blocked_count"],
        status,
    )
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
