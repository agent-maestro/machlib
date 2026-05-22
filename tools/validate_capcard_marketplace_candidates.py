#!/usr/bin/env python3
"""Validate internal CapCard marketplace candidate packets."""

from __future__ import annotations

import argparse
import copy
import json
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

BOUNDARY_PHRASES = [
    "not theorem prover",
    "not open-problem result",
    "not certified safety",
    "not production controller evidence",
    "not petal/api uploaded",
    "not hugging face uploaded",
    "not production marketplace modified",
]

FORBIDDEN_POSITIVE = [
    "theorem proved",
    "open problem solved",
    "certified safety",
    "production controller",
    "petal verified",
    "hugging face uploaded",
    "capcard certified",
]

READY_STATES = {
    "READY_FOR_HUMAN_MARKETPLACE_APPROVAL",
    "READY_FOR_HUMAN_INTERNAL_MARKETPLACE_APPROVAL",
    "INTERNAL_MARKETPLACE_STRONG_CANDIDATE",
    "INTERNAL_DRAFT_MARKETPLACE_READY",
}


def load_json(path: Path) -> Any:
    return json.loads(path.read_text())


def text_blob(value: Any) -> str:
    if isinstance(value, str):
        return value
    return json.dumps(value, sort_keys=True)


def normalize_boundary_text(value: str) -> str:
    return " ".join(value.lower().replace("not a ", "not ").replace("not an ", "not ").split())


def is_negative_boundary_hit(blob: str, phrase: str) -> bool:
    idx = blob.find(phrase)
    if idx < 0:
        return False
    prefix = blob[max(0, idx - 24):idx]
    return "not " in prefix or "no " in prefix or "false" in blob[idx:idx + 80]


def collect_drafts(path: Path) -> list[dict[str, Any]]:
    drafts: list[dict[str, Any]] = []
    if not path.exists():
        return drafts
    for item in sorted(path.glob("*.json")):
        data = load_json(item)
        if isinstance(data, dict) and data.get("candidate_id"):
            data = copy.deepcopy(data)
            data["_source_path"] = str(item)
            drafts.append(data)
    return drafts


def merge_by_candidate(candidates: list[dict[str, Any]], drafts: list[dict[str, Any]]) -> dict[str, dict[str, Any]]:
    merged: dict[str, dict[str, Any]] = {}
    for row in candidates:
        cid = row.get("candidate_id")
        if not cid:
            continue
        merged[cid] = copy.deepcopy(row)
    for draft in drafts:
        cid = draft["candidate_id"]
        merged.setdefault(cid, {"candidate_id": cid})
        for key, value in draft.items():
            if key.startswith("_"):
                continue
            if key not in merged[cid] or merged[cid].get(key) in (None, [], ""):
                merged[cid][key] = value
        merged[cid].setdefault("_draft_sources", []).append(draft.get("_source_path"))
    return merged


def normalize_row(row: dict[str, Any]) -> dict[str, Any]:
    row = copy.deepcopy(row)
    if "marketplace_readiness" not in row and "marketplace_status" in row:
        row["marketplace_readiness"] = row["marketplace_status"]
    if "visibility_recommendation" not in row and "visibility" in row:
        row["visibility_recommendation"] = row["visibility"]
    if "evidence_basis" not in row and "source_artifacts" in row:
        row["evidence_basis"] = row["source_artifacts"]
    if "limitations" not in row and row.get("marketplace_readiness") == "BLOCKED_WITH_EXACT_FIX_LIST":
        row["limitations"] = row.get("blockers", [])
    row.setdefault("blockers", [])
    return row


def validate_row(row: dict[str, Any], *, strict: bool) -> tuple[str, list[str], list[str]]:
    errors: list[str] = []
    warnings: list[str] = []
    row = normalize_row(row)
    cid = row.get("candidate_id", "<missing>")
    for key in [
        "candidate_id",
        "display_name",
        "marketplace_readiness",
        "visibility_recommendation",
        "evidence_basis",
        "limitations",
        "blockers",
        "next_safe_task",
    ]:
        if key not in row:
            errors.append(f"{cid}: missing {key}")
    for key in FALSE_FIELDS:
        if row.get(key) is not False:
            errors.append(f"{cid}: {key} must be false")
    blob = text_blob(row).lower()
    for phrase in FORBIDDEN_POSITIVE:
        if phrase in blob and not is_negative_boundary_hit(blob, phrase):
            errors.append(f"{cid}: forbidden positive claim '{phrase}'")
    ready = row.get("marketplace_readiness") in READY_STATES
    if ready:
        boundary_text = normalize_boundary_text(" ".join(
            str(x).lower()
            for x in row.get("limitations", []) + row.get("not_claimed", [])
        ))
        for phrase in BOUNDARY_PHRASES:
            if phrase not in boundary_text:
                errors.append(f"{cid}: missing boundary '{phrase}'")
    if cid == "eml_puzzle_evidence_kernel":
        if ready and row.get("visibility_recommendation") not in {"internal", "internal_marketplace"}:
            errors.append(f"{cid}: must be internal visibility only")
        if ready:
            basis = " ".join(map(str, row.get("evidence_basis", []))).lower()
            if "ledger" not in basis:
                errors.append(f"{cid}: evidence ledger not represented")
            if "no-upload" not in basis and "no upload" not in basis:
                errors.append(f"{cid}: no-upload gate not represented")
    if cid == "qwen_puzzle_curriculum_pack":
        if ready:
            blockers = " ".join(map(str, row.get("blockers", []))).lower()
            repair = " ".join(map(str, row.get("row_repair_summary", []))).lower()
            if "validation_status=warn" in blockers and "repaired" not in repair:
                errors.append(f"{cid}: warn rows block readiness without repair")
            if "solver_status=unknown" in blockers and "bounded explanation" not in repair:
                errors.append(f"{cid}: unknown solver rows block readiness without bounded explanation")
            if "human review" not in repair:
                errors.append(f"{cid}: missing human review note for readiness")
    if row.get("command_center_reference_status") == "stale_reference_only" and ready:
        errors.append(f"{cid}: stale command-center reference cannot count as direct evidence")
    if errors:
        return "fail", errors, warnings
    if warnings:
        return "warn", errors, warnings
    return "pass", errors, warnings


def run_validation(candidates_path: Path, drafts_path: Path, strict: bool) -> dict[str, Any]:
    raw = load_json(candidates_path)
    candidates = raw.get("candidates", raw if isinstance(raw, list) else [])
    drafts = collect_drafts(drafts_path)
    ids = [row.get("candidate_id") for row in candidates if row.get("candidate_id")]
    duplicate_ids = sorted({cid for cid in ids if ids.count(cid) > 1})
    merged = merge_by_candidate(candidates, drafts)
    results = []
    fail_count = warn_count = pass_count = 0
    for cid, row in sorted(merged.items()):
        status, errors, warnings = validate_row(row, strict=strict)
        if status == "pass":
            pass_count += 1
        elif status == "warn":
            warn_count += 1
        else:
            fail_count += 1
        results.append({"candidate_id": cid, "status": status, "errors": errors, "warnings": warnings})
    for cid in duplicate_ids:
        fail_count += 1
        results.append({"candidate_id": cid, "status": "fail", "errors": ["duplicate candidate_id"], "warnings": []})
    overall = "PASS" if fail_count == 0 else "FAIL"
    return {
        "candidate_count": len(merged),
        "pass_count": pass_count,
        "warn_count": warn_count,
        "fail_count": fail_count,
        "status": overall,
        "results": results,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--candidates", required=True, type=Path)
    parser.add_argument("--drafts", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    result = run_validation(args.candidates, args.drafts, args.strict)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(
        "CAPCARD_MARKETPLACE_VALIDATION",
        result["candidate_count"],
        result["pass_count"],
        result["warn_count"],
        result["fail_count"],
        result["status"],
    )
    return 0 if result["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
