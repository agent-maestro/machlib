"""Local evidence miner for Qwen Puzzle row 2/3 repair artifacts."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path


SEARCH_ROOTS = [
    "product_readiness",
    "reports",
    "capcard_marketplace_drafts",
    "command_center_feeds",
    "corpus",
    "curricula",
    "evidence_reels",
    "hardware_readiness",
    "tools",
    "tests",
]

SEARCH_TERMS = [
    "Qwen_Puzzle_Curriculum",
    "qwen_puzzle_curriculum_pack",
    "puzzle_curriculum",
    "row 2",
    "row_2",
    "accepted row 2",
    "row 3",
    "row_3",
    "accepted row 3",
    "validation_status",
    "solver_status",
    "unknown",
    "warn",
    "accepted repair",
    "repair evidence",
    "lesson_id",
    "curriculum_lane",
    "puzzle_evidence",
    "PETAL",
    "CapCard",
]

DIRECT_MARKERS = [
    "human review accepted repair",
    "repaired_by_existing_evidence",
    "accepted_repair_evidence_present\": true",
    "accepted_repair_evidence_present: true",
    "decision\": \"repaired_or_accepted\"",
    "decision: repaired_or_accepted",
]

BLOCKED_MARKERS = [
    "still_blocked",
    "blocked_with_exact_fix_list",
    "no accepted repair evidence",
    "direct accepted repair evidence is still missing",
    "accepted_repair_evidence_present\": false",
    "accepted_repair_evidence_present: false",
]

STALE_MARKERS = [
    "stale reference",
    "stale_reference_only",
    "command-center pasted",
    "cannot count as direct evidence",
]


@dataclass
class ArtifactInventoryRow:
    path: str
    match_terms: list[str]
    artifact_type: str
    direct_evidence_candidate: bool
    stale_reference_only: bool
    row2_relevant: bool
    row3_relevant: bool
    evidence_strength: str
    reason: str


def safe_read_text(path: Path, *, max_bytes: int = 750_000) -> str:
    try:
        data = path.read_bytes()[:max_bytes]
    except OSError:
        return ""
    return data.decode("utf-8", errors="ignore")


def artifact_type(path: Path) -> str:
    suffix = path.suffix.lower()
    if suffix == ".json":
        return "json"
    if suffix == ".jsonl":
        return "jsonl"
    if suffix == ".md":
        return "markdown"
    if suffix == ".py":
        return "python"
    if suffix in {".txt", ".log"}:
        return "text"
    return suffix.lstrip(".") or "unknown"


def matched_terms(text: str, terms: list[str] | None = None) -> list[str]:
    terms = terms or SEARCH_TERMS
    lower = text.lower()
    return [term for term in terms if term.lower() in lower]


def row_relevance(path: Path, text: str, row: int) -> bool:
    lower = f"{path}\n{text}".lower()
    needles = [
        f"row {row}",
        f"row_{row}",
        f"source_row\": {row}",
        f"source_row: {row}",
        f"qwen_puzzle_row_{row}",
        f"accepted row {row}",
    ]
    return any(needle in lower for needle in needles)


def classify_evidence(path: Path, text: str, terms: list[str]) -> ArtifactInventoryRow:
    lower = text.lower()
    lower_path = str(path).lower()
    row2 = row_relevance(path, text, 2)
    row3 = row_relevance(path, text, 3)
    stale = "command_center_feeds" in lower_path or any(marker in lower for marker in STALE_MARKERS)
    direct_marker = any(marker in lower for marker in DIRECT_MARKERS)
    blocked_marker = any(marker in lower for marker in BLOCKED_MARKERS)
    direct = (row2 or row3) and direct_marker and not stale and not blocked_marker

    if direct:
        strength = "DIRECT"
        reason = "row-specific artifact contains direct accepted repair markers without stale/blocking markers"
    elif stale:
        strength = "STALE_REFERENCE_ONLY"
        reason = "artifact is stale, command-center-derived, or explicitly says it cannot count as direct evidence"
    elif row2 or row3 or terms:
        strength = "SUPPORTING"
        reason = "artifact is relevant or contextual but does not prove accepted repair evidence for row 2/3"
    else:
        strength = "IRRELEVANT"
        reason = "no relevant Qwen row 2/3 evidence terms found"

    return ArtifactInventoryRow(
        path=str(path),
        match_terms=terms,
        artifact_type=artifact_type(path),
        direct_evidence_candidate=direct,
        stale_reference_only=stale,
        row2_relevant=row2,
        row3_relevant=row3,
        evidence_strength=strength,
        reason=reason,
    )


def iter_candidate_files(repo_root: Path, roots: list[str] | None = None) -> list[Path]:
    roots = roots or SEARCH_ROOTS
    files: list[Path] = []
    for root in roots:
        base = repo_root / root
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if not path.is_file():
                continue
            if any(part.startswith(".") for part in path.relative_to(base).parts):
                continue
            files.append(path)
    return sorted(files)


def build_inventory(repo_root: Path, *, roots: list[str] | None = None) -> dict:
    rows: list[ArtifactInventoryRow] = []
    scanned = 0
    for path in iter_candidate_files(repo_root, roots):
        scanned += 1
        text = safe_read_text(path)
        terms = matched_terms(text + "\n" + str(path))
        if not terms:
            continue
        rows.append(classify_evidence(path.relative_to(repo_root), text, terms))

    direct_count = sum(1 for row in rows if row.evidence_strength == "DIRECT")
    stale_count = sum(1 for row in rows if row.evidence_strength == "STALE_REFERENCE_ONLY")
    row2_count = sum(1 for row in rows if row.row2_relevant)
    row3_count = sum(1 for row in rows if row.row3_relevant)
    return {
        "inventory_id": "qwen_row23_source_artifact_inventory_2026_05_23",
        "status": "PASS",
        "search_roots": roots or SEARCH_ROOTS,
        "search_terms": SEARCH_TERMS,
        "files_scanned": scanned,
        "artifact_count": len(rows),
        "direct_evidence_candidate_count": direct_count,
        "stale_reference_only_count": stale_count,
        "row2_relevant_count": row2_count,
        "row3_relevant_count": row3_count,
        "direct_repair_evidence_found": direct_count > 0,
        "rows": [asdict(row) for row in rows],
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "fine_tune_performed": False,
        "cloud_model_used": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }


def render_inventory_report(inventory: dict) -> str:
    lines = [
        "# Qwen Row 2/3 Source Artifact Inventory",
        "",
        f"Files scanned: {inventory['files_scanned']}.",
        f"Matching artifacts: {inventory['artifact_count']}.",
        f"Direct evidence candidates: {inventory['direct_evidence_candidate_count']}.",
        f"Stale-reference-only artifacts: {inventory['stale_reference_only_count']}.",
        f"Row 2 relevant artifacts: {inventory['row2_relevant_count']}.",
        f"Row 3 relevant artifacts: {inventory['row3_relevant_count']}.",
        "",
        "Decision: direct accepted repair evidence is present only if a row-specific artifact is classified DIRECT.",
        "",
        "| path | strength | row 2 | row 3 | reason |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in inventory["rows"][:120]:
        lines.append(
            f"| `{row['path']}` | {row['evidence_strength']} | {row['row2_relevant']} | "
            f"{row['row3_relevant']} | {row['reason']} |"
        )
    if len(inventory["rows"]) > 120:
        lines.append(f"| ... | ... | ... | ... | {len(inventory['rows']) - 120} additional rows omitted from report preview |")
    lines.append("")
    lines.append("No upload, marketplace modification, fine-tune, cloud model, deployment, hardware action, public proof claim, certified safety claim, or production controller claim was performed.")
    return "\n".join(lines) + "\n"


def write_json(path: Path, data: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", default=".")
    parser.add_argument("--out", required=True)
    parser.add_argument("--report-out", required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    inventory = build_inventory(Path(args.repo_root).resolve())
    write_json(Path(args.out), inventory)
    Path(args.report_out).parent.mkdir(parents=True, exist_ok=True)
    Path(args.report_out).write_text(render_inventory_report(inventory))
    print("QWEN_ROW23_SOURCE_ARTIFACT_INVENTORY_OK", inventory["artifact_count"], inventory["direct_evidence_candidate_count"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
