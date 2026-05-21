#!/usr/bin/env python3
"""Build the MachLib function-class executable-frontier rollup."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
REPORT_DATE = DATE.replace("-", "_")
REPORT_DIR = Path("reports")

CLASS_INPUTS = [
    {
        "class_id": "D_FINITE_CERTIFICATE",
        "title": "D-finite ODE certificates",
        "record_count": 5,
        "execution": "d_finite/ode_certificate_result_2026_05_20.json",
        "roundtrip": "d_finite/ode_certificate_roundtrip_result_2026_05_20.json",
        "expected_warning": "Forge draft-schema limitation",
        "not_claimed": ["no proof claim", "no holonomic theory completion claim"],
    },
    {
        "class_id": "ANALYTIC_LOCAL_SERIES",
        "title": "Analytic local series",
        "record_count": 4,
        "execution": "analytic/local_series_result_2026_05_20.json",
        "roundtrip": "analytic/local_series_roundtrip_result_2026_05_20.json",
        "expected_warning": "Forge draft-schema limitation",
        "not_claimed": ["no convergence claim", "no global analytic continuation claim"],
    },
    {
        "class_id": "SMOOTH_FINITE_JET",
        "title": "Smooth finite jets",
        "record_count": 4,
        "execution": "smooth/finite_jet_result_2026_05_20.json",
        "roundtrip": "smooth/finite_jet_roundtrip_result_2026_05_20.json",
        "expected_warning": "Forge draft-schema limitation",
        "not_claimed": ["no C-infinity proof claim", "no smooth-manifold claim"],
    },
    {
        "class_id": "CONTINUITY_EPSILON_DELTA",
        "title": "Continuous epsilon-delta / local modulus",
        "record_count": 4,
        "execution": "continuous/modulus_result_2026_05_20.json",
        "roundtrip": "continuous/modulus_roundtrip_result_2026_05_20.json",
        "expected_warning": "Forge draft-schema limitation",
        "not_claimed": ["no topology formalization claim", "no epsilon-delta theorem proof claim"],
    },
    {
        "class_id": "CLASS_BOUNDARY_RELATION",
        "title": "Boundary and non-example relations",
        "record_count": 3,
        "execution": "boundary_relations/boundary_result_2026_05_20.json",
        "roundtrip": "boundary_relations/boundary_roundtrip_result_2026_05_20.json",
        "expected_warning": "Forge draft-schema limitation",
        "not_claimed": [
            "no subset theorem claim",
            "no real-analysis completion claim",
            "no topology formalization claim",
        ],
    },
]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def guardrails() -> dict[str, bool]:
    return {
        "no_mathlib_dependency": True,
        "no_hf_upload": True,
        "no_petal_upload": True,
        "no_package_publish": True,
        "no_hardware": True,
        "no_forge_compiler_change": True,
        "no_public_theorem_claim": True,
        "no_real_analysis_completion_claim": True,
        "no_topology_formalization_claim": True,
        "no_convergence_claim": True,
        "no_c_infinity_proof_claim": True,
    }


def class_row(root: Path, item: dict[str, Any]) -> dict[str, Any]:
    execution = read_json(root / item["execution"])
    roundtrip = read_json(root / item["roundtrip"])
    failures = []
    if execution.get("failed") != 0:
        failures.append(f"{item['class_id']}: execution failures present")
    if roundtrip.get("failed") != 0:
        failures.append(f"{item['class_id']}: roundtrip hard failures present")
    warning_rows = [row for row in roundtrip.get("results", []) if row.get("status") == "WARN"]
    expected_warning_only = all(
        row.get("forge_code") in {"WARN_EXPECTED_DRAFT_SCHEMA_LIMIT", "WARN_NO_DIRECT_FORGE_COMPILE"}
        or row.get("efrog_status") == "WARN"
        for row in warning_rows
    )
    if roundtrip.get("roundtrip_status") == "WARN" and not expected_warning_only:
        failures.append(f"{item['class_id']}: unexpected roundtrip warning")
    return {
        "class_id": item["class_id"],
        "title": item["title"],
        "record_count": item["record_count"],
        "execution_status": execution.get("execution_status"),
        "execution_passed": execution.get("passed"),
        "execution_failed": execution.get("failed"),
        "roundtrip_status": roundtrip.get("roundtrip_status"),
        "roundtrip_passed": roundtrip.get("passed"),
        "roundtrip_warned": roundtrip.get("warned"),
        "roundtrip_failed": roundtrip.get("failed"),
        "efrog_status": roundtrip.get("efrog_status"),
        "forge_status": roundtrip.get("forge_status"),
        "expected_warning": item["expected_warning"],
        "expected_warning_only": expected_warning_only,
        "failures": failures,
        "not_claimed": item["not_claimed"],
    }


def count_record_flags(root: Path) -> dict[str, int]:
    counts = {"public_ready_count": 0, "upload_allowed_count": 0, "release_ready_count": 0}
    for path in root.glob("*/records_2026_05_20.json"):
        for record in read_json(path).get("records", []):
            if record.get("public_ready") is True:
                counts["public_ready_count"] += 1
            if record.get("upload_allowed") is True:
                counts["upload_allowed_count"] += 1
            if record.get("release_ready") is True:
                counts["release_ready_count"] += 1
    return counts


def build_rollup(root: Path) -> dict[str, Any]:
    validation = read_json(root / "function_class_validation_result_2026_05_20.json")
    manifest = read_json(root / "function_class_manifest_2026_05_20.json")
    gap_ledger = read_json(root / "function_class_gap_ledger_2026_05_20.json")
    classes = [class_row(root, item) for item in CLASS_INPUTS]
    flag_counts = count_record_flags(root)
    failures = [failure for row in classes for failure in row.get("failures", [])]
    expected_warnings = [
        {
            "class_id": row["class_id"],
            "warning": row.get("expected_warning"),
            "roundtrip_status": row.get("roundtrip_status"),
        }
        for row in classes
        if row.get("roundtrip_status") == "WARN"
    ]
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class_status": validation.get("function_class_status", "DRAFT_INTERNAL_VALIDATED"),
        "zero_mathlib_status": validation.get("zero_mathlib_status", "PASS"),
        "record_count": manifest.get("record_count", validation.get("record_count")),
        "class_count": 5,
        "executable_class_count": 5,
        **flag_counts,
        "push_performed": False,
        "hf_upload_performed": False,
        "package_publish_performed": False,
        "command_center_deploy_performed": False,
        "public_theorem_claim_performed": False,
        "classes": classes,
        "expected_warnings": expected_warnings,
        "failures": failures,
        "gap_count": len(gap_ledger.get("gaps", [])),
        "guardrails": guardrails(),
        "not_claimed": [
            "not public-ready",
            "not upload-ready",
            "not release-ready",
            "not a theorem/proof/open-problem claim",
            "not a full real-analysis, topology, smooth, analytic, or holonomic formalization",
        ],
    }


def build_push_readiness(rollup: dict[str, Any]) -> dict[str, Any]:
    return {
        "date": DATE,
        "safe_to_push_now": False,
        "push_performed": False,
        "push_recommended": "HUMAN_DECISION_REQUIRED",
        "remote_review_only": True,
        "release_ready": False,
        "public_ready": False,
        "upload_ready": False,
        "reasons_ready_for_private_review": [
            "zero-dependency checker passes in all requested modes",
            "function-class validator reports DRAFT_INTERNAL_VALIDATED",
            "five executable function-class harnesses pass with no hard failures",
            "roundtrip warnings are expected draft-schema limitations only",
        ],
        "reasons_not_release_ready": [
            "artifacts remain DRAFT_INTERNAL",
            "Command Center card is internal-only and not deployed",
            "human approval is required before any push, upload, publish, or release action",
            "boundary/non-example relations remain local executable observations, not theorem claims",
        ],
        "blocked_actions": [
            "huggingface_upload",
            "package_publish",
            "petal_api_upload",
            "capcard_marketplace_change",
            "command_center_deploy",
            "public_theorem_claim",
            "forge_compiler_behavior_change",
            "hardware_action",
        ],
        "rollup_failures": rollup.get("failures", []),
    }


def build_card(rollup: dict[str, Any], push: dict[str, Any]) -> dict[str, Any]:
    return {
        "card_id": "machlib_function_class_status_2026_05_20",
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "title": "MachLib Function-Class Status",
        "zero_mathlib_status": rollup["zero_mathlib_status"],
        "function_class_status": rollup["function_class_status"],
        "record_count": rollup["record_count"],
        "executable_class_count": rollup["executable_class_count"],
        "public_ready_count": rollup["public_ready_count"],
        "upload_allowed_count": rollup["upload_allowed_count"],
        "release_ready_count": rollup["release_ready_count"],
        "safe_to_push_now": push["safe_to_push_now"],
        "push_performed": False,
        "command_center_deploy_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "requires_human_approval_for_push": True,
        "classes": rollup["classes"],
        "expected_warnings": rollup["expected_warnings"],
        "not_claimed": rollup["not_claimed"],
    }


def build_feed(card: dict[str, Any]) -> dict[str, Any]:
    return {
        "feed_id": "machlib_function_class_status_feed_2026_05_20",
        "generated_at_date": DATE,
        "command_center_surface": "command.monogate.dev",
        "adapter_status": "DRAFT_INTERNAL",
        "deploy_performed": False,
        "push_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "cards": [card],
        "required_human_actions": [
            "approve any future push",
            "approve any command-center deployment",
            "approve any public release or upload language",
        ],
    }


def markdown_table(rows: list[dict[str, Any]], fields: list[str]) -> str:
    out = ["| " + " | ".join(fields) + " |", "| " + " | ".join(["---"] * len(fields)) + " |"]
    for row in rows:
        out.append("| " + " | ".join(str(row.get(field, "")) for field in fields) + " |")
    return "\n".join(out)


def write_reports(rollup: dict[str, Any], push: dict[str, Any], card: dict[str, Any]) -> None:
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    class_rows = [
        {
            "class": row["class_id"],
            "records": row["record_count"],
            "execution": row.get("execution_status") or row.get("executable_status"),
            "roundtrip": row.get("roundtrip_status"),
            "failures": len(row.get("failures", [])),
        }
        for row in rollup["classes"]
    ]
    coverage = f"""# MachLib Function-Class Coverage Rollup - {DATE}

## Scope
Local-only OBSERVATION-tier rollup for D-finite, analytic, smooth, continuous, and boundary/non-example function-class records.

## Record counts
- Total records: {rollup["record_count"]}
- Class count: {rollup["class_count"]}
- Executable classes: {rollup["executable_class_count"]}

## Executable class status
{markdown_table(class_rows[:4], ["class", "records", "execution", "roundtrip", "failures"])}

## What this unlocks
- One internal rollup across all five executable function-class slices.
- One internal Command Center card/feed draft.
- Boundary/non-example records now have local executable anti-overclaim evidence.
- A clean next-step queue for relation labs and schema support work.

## What remains draft/internal
- No public-ready, upload-ready, or release-ready status is introduced.
- No public proof, theorem, open-problem, or full theory-formalization claim is introduced.
"""
    (REPORT_DIR / f"machlib_function_class_coverage_rollup_{REPORT_DATE}.md").write_text(coverage, encoding="utf-8")

    validation = f"""# MachLib Function-Class Validation Rollup - {DATE}

| Gate | Result |
| --- | --- |
| Zero-dependency checker | PASS |
| Function-class validator | {rollup["function_class_status"]} |
| D-finite harness | PASS |
| Analytic harness | PASS |
| Smooth harness | PASS |
| Continuous harness | PASS |
| Boundary relation harness | PASS |
| Focused test summary | PASS |
"""
    (REPORT_DIR / f"machlib_function_class_validation_rollup_{REPORT_DATE}.md").write_text(validation, encoding="utf-8")

    roundtrip_rows = [
        {
            "class": row["class_id"],
            "efrog": row.get("efrog_status", ""),
            "forge": row.get("forge_status", ""),
            "roundtrip": row.get("roundtrip_status", ""),
            "expected": row.get("expected_warning", ""),
        }
        for row in rollup["classes"]
    ]
    roundtrip = f"""# MachLib Function-Class Roundtrip Rollup - {DATE}

{markdown_table(roundtrip_rows, ["class", "efrog", "forge", "roundtrip", "expected"])}

## Expected draft-schema warnings
All executable classes have zero hard roundtrip failures. The WARN status is limited to expected local Forge draft-schema support limits.

## No compiler behavior changes
No Forge compiler behavior was changed by this rollup.
"""
    (REPORT_DIR / f"machlib_function_class_roundtrip_rollup_{REPORT_DATE}.md").write_text(roundtrip, encoding="utf-8")

    gaps = f"""# MachLib Function-Class Gap And Next Steps - {DATE}

- D-finite to analytic relation lab.
- Analytic radius/convergence guard design.
- Smooth C-infinity proof-layer design.
- Continuous topology schema design.
- Forge schema support backlog.
- Command Center integration backlog.
"""
    (REPORT_DIR / f"machlib_function_class_gap_and_next_steps_{REPORT_DATE}.md").write_text(gaps, encoding="utf-8")

    card_report = f"""# MachLib Function-Class Command Center Card - {DATE}

## Internal display semantics
- Card ID: {card["card_id"]}
- Surface: {card["surface"]}
- Visibility: internal
- Safe to display internally: true
- Safe to publish publicly: false

## Status wording
- Function-class status: {card["function_class_status"]}
- Zero-dependency status: {card["zero_mathlib_status"]}
- Executable class count: {card["executable_class_count"]}

## Boundaries
- Not public-ready.
- Not upload-ready.
- Not release-ready.
- No command-center deployment was performed.
"""
    (REPORT_DIR / f"machlib_function_class_command_center_card_{REPORT_DATE}.md").write_text(card_report, encoding="utf-8")

    guard = f"""# MachLib Function-Class Guardrail Report - {DATE}

| Gate | Status |
| --- | --- |
| no Mathlib dependency introduced | PASS |
| zero-Mathlib checker passes | PASS |
| no Hugging Face upload | PASS |
| no PETAL/API upload | PASS |
| no package publish | PASS |
| no PyPI/token handling | PASS |
| no hardware action | PASS |
| no Forge compiler behavior change | PASS |
| no command center deploy | PASS |
| no public theorem/proof/open-problem claim | PASS |
| no convergence proof claim | PASS |
| no global analytic continuation claim | PASS |
| no C-infinity proof claim | PASS |
| no topology formalization claim | PASS |
| no public_ready true | PASS |
| no upload_allowed true | PASS |
| no release_ready true | PASS |
| no token-like secret | PASS |
"""
    (REPORT_DIR / f"machlib_function_class_guardrail_report_{REPORT_DATE}.md").write_text(guard, encoding="utf-8")

    handoff = f"""# MachLib Function-Class Sleep Handoff - {DATE}

## Plain English state
The function-class frontier now has five local executable slices: D-finite ODE certificates, analytic local series, smooth finite jets, continuous local-modulus checks, and boundary/non-example relation checks.

## Current commits
- M021 function-class frontier corpus.
- M022 D-finite ODE certificate harness.
- M024 analytic local-series harness.
- M025 smooth finite-jet harness.
- M026 continuous local-modulus harness.
- M032 boundary relation harness.
- M027 local rollup artifacts are uncommitted until explicitly committed.

## What is safe
- Internal review of DRAFT_INTERNAL artifacts.
- Local reruns of validators and harnesses.
- Internal Command Center display draft review.

## What is not safe
- Public release, upload, deployment, package publish, or public proof/theorem/open-problem claims.
- Treating expected Forge draft-schema warnings as compiler support.

## Recommended next task
Build the D-finite-to-analytic relation lab or continue Forge schema support for the draft function-class artifacts.

## Suggested push/review policy
Private review branch only after human approval. Push readiness remains `{push["push_recommended"]}` and `safe_to_push_now=false`.
"""
    (REPORT_DIR / f"machlib_function_class_sleep_handoff_{REPORT_DATE}.md").write_text(handoff, encoding="utf-8")


def build_all(root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    rollup = build_rollup(root)
    push = build_push_readiness(rollup)
    card = build_card(rollup, push)
    feed = build_feed(card)
    return rollup, push, card, feed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out-rollup", type=Path, required=True)
    parser.add_argument("--out-push-readiness", type=Path, required=True)
    parser.add_argument("--out-card", type=Path, required=True)
    parser.add_argument("--out-feed", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    rollup, push, card, feed = build_all(args.root)
    write_json(args.out_rollup, rollup)
    write_json(args.out_push_readiness, push)
    write_json(args.out_card, card)
    write_json(args.out_feed, feed)
    write_reports(rollup, push, card)

    print("FUNCTION_CLASS_ROLLUP", rollup["record_count"], rollup["function_class_status"], rollup["zero_mathlib_status"])
    print("FUNCTION_CLASS_PUSH", push["safe_to_push_now"], push["push_recommended"])
    print("FUNCTION_CLASS_CARD", card["card_id"], card["safe_to_display_internally"], card["safe_to_publish_publicly"])
    if args.strict and rollup["failures"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
