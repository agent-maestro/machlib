"""Rank CapCard candidates by internal marketplace utility."""

from __future__ import annotations

from pathlib import Path

from .reporting import read_json, write_json, write_report


SEGMENTS = [
    "AI eval teams",
    "formal/artifact review teams",
    "model-curriculum teams",
    "safety/governance teams",
    "robotics/simulation review teams",
    "internal platform teams",
    "evidence audit consultants",
    "education/curriculum teams",
]


def rank(scores_path: Path, out: Path, repo_root: Path) -> dict:
    scores = read_json(scores_path)
    ranked = sorted(scores.get("candidates", []), key=lambda row: (-row["overall_trust_score_0_to_100"], row["candidate_id"]))
    data = {
        "status": "PASS",
        "ranked_candidates": ranked,
        "top_candidate": ranked[0]["candidate_id"] if ranked else None,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(out, data)
    buyer = {
        "status": "PASS",
        "segments": [
            {
                "segment": segment,
                "why_capcard_helps": "Turns local evidence into reviewable cards with explicit no-go boundaries.",
                "strongest_candidate_type": "strong internal evidence card" if "eval" in segment.lower() else "readiness dashboard card",
                "risks": ["overclaiming", "stale evidence", "missing reviewer metadata"],
                "product_surface": "static internal workbench",
                "revenue_path": "private evidence review workbench",
            }
            for segment in SEGMENTS
        ],
    }
    write_json(repo_root / "product_readiness/capcard_lab_buyer_utility_2026_05_21.json", buyer)
    write_report(
        repo_root / "reports/capcard_lab_marketplace_ranking_2026_05_21.md",
        "CapCard Lab Marketplace Ranking",
        [f"- Ranked candidates: {len(ranked)}", f"- Top candidate: {data['top_candidate']}", "- Ranking uses trust, usefulness, freshness, actionability, and risk."],
    )
    write_report(
        repo_root / "reports/capcard_lab_buyer_utility_2026_05_21.md",
        "CapCard Lab Buyer Utility",
        ["- Buyer utility is strongest for internal eval, artifact review, governance, and evidence audit teams.", "- Revenue path remains internal/private workbench first."],
    )
    return data
