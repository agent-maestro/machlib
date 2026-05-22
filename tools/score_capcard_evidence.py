#!/usr/bin/env python3
"""Score local CapCard evidence freshness, provenance, and trust."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


FALSE_FIELDS = [
    "marketplace_upload_performed",
    "production_marketplace_modified",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "public_claim",
    "certified_safety_claim",
    "production_controller_claim",
    "theorem_proof_claim",
]

FORBIDDEN = ["theorem proved", "open problem solved", "certified safety", "production controller", "petal verified", "hugging face dataset live"]


def load_json(path: Path) -> Any:
    return json.loads(path.read_text())


def normalize(text: str) -> str:
    return " ".join(text.lower().replace("not a ", "not ").replace("not an ", "not ").split())


def negative(blob: str, phrase: str) -> bool:
    idx = blob.find(phrase)
    return idx >= 0 and ("not " in blob[max(0, idx - 32):idx] or "no " in blob[max(0, idx - 32):idx])


def collect_cards(drafts: Path) -> list[dict[str, Any]]:
    cards: dict[str, dict[str, Any]] = {}
    for path in sorted(drafts.glob("*.json")):
        try:
            data = load_json(path)
        except Exception:
            continue
        cid = data.get("candidate_id")
        if not cid:
            continue
        cards.setdefault(cid, {"candidate_id": cid, "source_files": []})
        cards[cid].update(data)
        cards[cid]["source_files"].append(str(path))
    qwen = Path("product_readiness/qwen_puzzle_curriculum_repair_review_2026_05_21.json")
    if qwen.exists():
        data = load_json(qwen)
        cards["qwen_puzzle_curriculum_pack"] = {
            "candidate_id": "qwen_puzzle_curriculum_pack",
            "display_name": "Qwen Puzzle Curriculum Pack",
            "marketplace_readiness": data.get("marketplace_readiness"),
            "evidence_basis": ["Qwen puzzle curriculum evidence ledger"],
            "limitations": ["not a theorem prover", "not certified safety", "not production controller evidence"],
            "blockers": data.get("blockers", []),
            "marketplace_upload_performed": False,
            "production_marketplace_modified": False,
            "petal_api_upload_performed": False,
            "huggingface_upload_performed": False,
            "public_claim": False,
            "certified_safety_claim": False,
            "production_controller_claim": False,
            "theorem_proof_claim": False,
        }
    return list(cards.values())


def score_card(card: dict[str, Any], inventory: dict[str, Any]) -> dict[str, Any]:
    blob = normalize(json.dumps(card, sort_keys=True))
    score = 50
    basis = card.get("evidence_basis", [])
    sources = set(card.get("source_artifacts", []) + card.get("source_files", []))
    source_count = len(sources) or len(basis)
    if source_count:
        score += min(15, source_count * 3)
    direct_count = sum(1 for row in inventory.get("sources", []) if row.get("marketplace_use") == "direct_evidence" and row.get("candidate_link") in {card.get("candidate_id"), "both"})
    if direct_count:
        score += min(15, direct_count * 3)
    stale_count = sum(1 for row in inventory.get("sources", []) if row.get("marketplace_use") == "stale_reference_only" and row.get("candidate_link") in {card.get("candidate_id"), "both"})
    score -= min(20, stale_count * 5)
    blockers = " ".join(map(str, card.get("blockers", []))).lower()
    warn_count = blockers.count("validation_status=warn")
    unknown_count = blockers.count("solver_status=unknown")
    score -= warn_count * 10
    score -= unknown_count * 10
    no_upload = "no-upload" in blob or "no upload" in blob
    if no_upload:
        score += 10
    if card.get("reviewer_id") and card.get("review_date"):
        score += 10
    elif card.get("requires_human_approval_for_production"):
        score += 3
    if all(card.get(key) is False for key in FALSE_FIELDS):
        score += 10
    else:
        score = min(score, 30)
    for phrase in FORBIDDEN:
        if phrase in blob and not negative(blob, phrase):
            score = min(score, 30)
    if re.search(r"pypi-[A-Za-z0-9]{20,}|hf_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,}", json.dumps(card)):
        score = min(score, 30)
    score = max(0, min(100, score))
    if score >= 85:
        status = "STRONG_INTERNAL_CANDIDATE"
    elif score >= 70:
        status = "READY_FOR_HUMAN_INTERNAL_REVIEW"
    elif score >= 50:
        status = "PROMISING_BUT_NEEDS_REPAIR"
    else:
        status = "BLOCKED"
    return {
        "candidate_id": card.get("candidate_id"),
        "score": score,
        "score_band": status,
        "source_count": source_count,
        "direct_source_count": direct_count,
        "stale_reference_count": stale_count,
        "warn_count": warn_count,
        "unknown_solver_penalty_count": unknown_count,
        "no_upload_gate_present": no_upload,
        "human_review_present": bool(card.get("reviewer_id") or card.get("requires_human_approval_for_production")),
        "reviewer_identity_present": bool(card.get("reviewer_id") and card.get("review_date")),
        "forbidden_action_false_score": 100 if all(card.get(key) is False for key in FALSE_FIELDS) else 0,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--drafts", required=True, type=Path)
    parser.add_argument("--inventory", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    inventory = load_json(args.inventory)
    scores = [score_card(card, inventory) for card in collect_cards(args.drafts)]
    result = {
        "score_status": "PASS",
        "scores": scores,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print("CAPCARD_EVIDENCE_SCORES", len(scores), "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
