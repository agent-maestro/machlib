"""Discover local evidence sources for the CapCard Lab."""

from __future__ import annotations

from pathlib import Path

from .reporting import write_json, write_report
from .schema import SOURCE_FAMILIES


KEYWORDS = {
    "capcard_draft": ["capcard_marketplace_drafts"],
    "capcard_spec": ["capcard_specs"],
    "capcard_validator": ["validate_capcard", "score_capcard", "simulate_capcard", "capcard_workbench", "capcard_lab"],
    "qwen_evidence": ["qwen"],
    "puzzle_kernel_evidence": ["puzzle"],
    "petal_style_record": ["petal"],
    "capcard_style_record": ["capcard"],
    "package_publish_record": ["published", "package-candidates", "package_candidates"],
    "pypi_upload_record": ["pypi"],
    "oneop_senses_record": ["senses", "oneop"],
    "machlib_package_record": ["machlib_package", "machlib-workbench", "eml-harness"],
    "evidence_reel_record": ["evidence_reel", "evidence_reels"],
    "electronics_curated_summary": ["electronics"],
    "command_center_feed": ["command_center_feeds"],
    "stale_command_center_reference": ["command-center", "proof-registry"],
    "reviewer_workflow": ["reviewer_workflow"],
    "adversarial_fixture": ["adversarial", "mutation"],
}


def classify(path: Path) -> str:
    text = path.as_posix().lower()
    for family, needles in KEYWORDS.items():
        if any(needle in text for needle in needles):
            return family
    return "unknown"


def discover_sources(repo_root: Path) -> dict:
    roots = [
        "capcard_marketplace_drafts",
        "capcard_specs",
        "product_readiness",
        "reports",
        "command_center_feeds",
        "tools",
        "tests",
        "corpus",
        "senses",
        "package_candidates",
    ]
    sources = []
    for root in roots:
        base = repo_root / root
        if not base.exists():
            continue
        for path in sorted(base.rglob("*")):
            if not path.is_file() or "__pycache__" in path.parts:
                continue
            if path.suffix not in {".json", ".md", ".py", ".html", ".css", ".js", ".tsx", ".ts"}:
                continue
            family = classify(path.relative_to(repo_root))
            sources.append({
                "source_path": path.relative_to(repo_root).as_posix(),
                "artifact_id": path.stem,
                "artifact_family": family if family in SOURCE_FAMILIES else "unknown",
                "status": "FOUND",
                "freshness": "stale_reference_only" if family == "stale_command_center_reference" else "current",
                "marketplace_use": "stale_reference_only" if family == "stale_command_center_reference" else "supporting_evidence",
            })
    return {
        "status": "PASS" if len(sources) >= 40 else "BLOCKED_FEWER_THAN_40_SOURCES",
        "source_count": len(sources),
        "sources": sources,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }


def write_discovery(repo_root: Path, out: Path) -> dict:
    data = discover_sources(repo_root)
    write_json(out, data)
    write_report(
        repo_root / "reports/capcard_lab_source_discovery_2026_05_21.md",
        "CapCard Lab Source Discovery",
        [
            f"- Source artifacts discovered: {data['source_count']}",
            f"- Status: {data['status']}",
            "- Stale references are classified separately from direct evidence.",
            "- No production marketplace, PETAL/API, Hugging Face, deploy, or public claim action was performed.",
        ],
    )
    return data
