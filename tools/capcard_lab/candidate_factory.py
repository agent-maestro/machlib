"""Generate internal CapCard Lab candidate cards."""

from __future__ import annotations

from pathlib import Path

from .reporting import write_json, write_report
from .schema import DISPLAY_NAMES, EXPECTED_BANDS, NOT_CLAIMED, REQUIRED_CANDIDATES, action_false_payload


def _category(cid: str) -> str:
    if "package" in cid or cid in {"claim_boundary_package", "eml_records_package"}:
        return "package_evidence"
    if "senses" in cid:
        return "senses_product"
    if "electronics" in cid:
        return "support_only"
    if "qwen" in cid:
        return "curriculum"
    if "mobius" in cid:
        return "toy_kernel"
    return "evidence_marketplace"


def make_card(cid: str, graph: dict | None = None) -> dict:
    band = EXPECTED_BANDS[cid]
    blockers = []
    if band.startswith("BLOCKED"):
        blockers = ["PyPI 429 or pending upload" if "machlib_package" in cid else "warn rows unresolved", "human repair evidence required"]
    if cid == "electronics_curated_manifest_support":
        blockers = ["support-only, no hardware validation"]
    if cid == "mobius_pair_kernel_future_candidate":
        blockers = [] if Path("corpus/mobius_pair_kernel_2026_05_21").exists() else ["future candidate until M088 artifacts exist"]
    source_artifacts = [
        "product_readiness/qwen_capcard_marketplace_candidates_2026_05_21.json",
        "capcard_marketplace_drafts/eml_puzzle_evidence_kernel_strengthened_DRAFT_2026_05_21.json",
        "product_readiness/capcard_deep_utility_assessment_2026_05_21.json",
    ]
    if "senses" in cid:
        source_artifacts.append("reports/oneop_senses_push_deploy_review_2026_05_21.md")
    if "mobius" in cid:
        source_artifacts.append("product_readiness/mobius_pair_capcard_candidate_2026_05_21.json")
    card = {
        "card_id": f"{cid}_LAB_DRAFT_2026_05_21",
        "candidate_id": cid,
        "display_name": DISPLAY_NAMES[cid],
        "category": _category(cid),
        "lifecycle_state": "INTERNAL_MARKETPLACE_STRONG_CANDIDATE" if band == "STRONG_INTERNAL" else "CANDIDATE_PROFILE",
        "marketplace_readiness": "READY_FOR_HUMAN_INTERNAL_MARKETPLACE_APPROVAL" if band in {"STRONG_INTERNAL", "READY_INTERNAL"} else "BLOCKED_WITH_EXACT_FIX_LIST" if "BLOCKED" in band else "INTERNAL_DRAFT_CANDIDATE",
        "readiness_band": band,
        "visibility": "internal",
        "visibility_recommendation": "internal_marketplace",
        "evidence_basis": ["local evidence ledger", "no-upload gate", "bounded internal review packet"],
        "source_artifacts": source_artifacts,
        "blockers": blockers,
        "limitations": ["internal observation tier", "not public marketplace", "bounded evidence only"] + NOT_CLAIMED,
        "not_claimed": NOT_CLAIMED,
        "reviewer_required": True,
        "score_placeholders": {
            "trust": 0,
            "readiness": 0,
            "buyer_utility": 0,
        },
    }
    card.update(action_false_payload())
    return card


def generate_candidates(repo_root: Path, out_dir: Path) -> dict:
    out_dir.mkdir(parents=True, exist_ok=True)
    cards = []
    for cid in REQUIRED_CANDIDATES:
        card = make_card(cid)
        write_json(out_dir / f"{cid}.json", card)
        cards.append(card)
    summary = {
        "status": "PASS",
        "candidate_count": len(cards),
        "candidates": cards,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(repo_root / "product_readiness/capcard_lab_generated_candidates_2026_05_21.json", summary)
    write_report(
        repo_root / "reports/capcard_lab_generated_candidates_2026_05_21.md",
        "CapCard Lab Generated Candidates",
        [
            f"- Generated candidates: {len(cards)}",
            "- EML Puzzle Evidence Kernel is strong internal.",
            "- Qwen Puzzle Curriculum Pack remains blocked with exact repair requirements.",
            "- Electronics remains support-only and makes no hardware-validation claim.",
        ],
    )
    return summary
