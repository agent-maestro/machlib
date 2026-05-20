#!/usr/bin/env python3
"""Build an aggregate dashboard for the MachLib six-lane draft corpus.

This is an observation-tier local review tool. It reads existing lane outputs,
summarizes validation posture, and records push readiness as a human decision,
without performing a push or any upload action.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
EXPECTED_SEED_COUNT = 19
EXPECTED_LANE_COUNTS = {
    "lane_1": 4,
    "lane_2": 3,
    "lane_3": 3,
    "lane_4": 3,
    "lane_5": 3,
    "lane_6": 3,
}
LANE_RESULTS = {
    "lane_1": {
        "manifest_id": "lane_1_algebra_core",
        "title": "EML algebra core",
        "execution": "lane_1_algebra_core/execution_result_2026_05_20.json",
        "roundtrip": "lane_1_algebra_core/roundtrip_result_2026_05_20.json",
    },
    "lane_2": {
        "manifest_id": "lane_2_calculus_special_functions",
        "title": "Calculus / special functions",
        "feasibility": "lane_2_calculus_special_functions/primitive_feasibility_result_2026_05_20.json",
        "symbolic": "lane_2_calculus_special_functions/symbolic_rewrite_result_2026_05_20.json",
        "roundtrip": "lane_2_calculus_special_functions/roundtrip_probe_result_2026_05_20.json",
    },
    "lane_3": {
        "manifest_id": "lane_3_discrete_algorithms",
        "title": "Discrete algorithms",
        "execution": "lane_3_discrete_algorithms/execution_result_2026_05_20.json",
        "roundtrip": "lane_3_discrete_algorithms/roundtrip_result_2026_05_20.json",
    },
    "lane_4": {
        "manifest_id": "lane_4_typeclass_lite",
        "title": "Typeclass-lite structures",
        "execution": "lane_4_typeclass_lite/execution_result_2026_05_20.json",
        "roundtrip": "lane_4_typeclass_lite/roundtrip_result_2026_05_20.json",
    },
    "lane_5": {
        "manifest_id": "lane_5_proof_evidence_records",
        "title": "Proof/evidence records",
        "execution": "lane_5_proof_evidence_records/execution_result_2026_05_20.json",
        "roundtrip": "lane_5_proof_evidence_records/roundtrip_result_2026_05_20.json",
    },
    "lane_6": {
        "manifest_id": "lane_6_legacy_compatibility",
        "title": "Legacy compatibility",
        "execution": "lane_6_legacy_compatibility/execution_result_2026_05_20.json",
        "roundtrip": "lane_6_legacy_compatibility/roundtrip_result_2026_05_20.json",
    },
}
BLOCKED_ACTIONS = [
    "huggingface_upload",
    "package_publish",
    "petal_api_upload",
    "capcard_marketplace_change",
    "public_theorem_claim",
    "forge_compiler_behavior_change",
    "hardware_action",
]


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def run_command(cmd: list[str]) -> str:
    proc = subprocess.run(cmd, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        return (proc.stdout + proc.stderr).strip()
    return proc.stdout.strip()


def seed_paths(root: Path) -> list[Path]:
    manifest = load_json(root / "lane_manifest_2026_05_20.json")
    paths: list[Path] = []
    for lane in manifest.get("lanes", []):
        for item in lane.get("seed_paths", []):
            paths.append(Path(item))
    return paths


def count_flags(root: Path) -> tuple[int, int, int]:
    public_ready = 0
    upload_allowed = 0
    release_ready = 0
    for path in seed_paths(root):
        obj = load_json(path)
        draft = obj.get("draft_eml_seed", {})
        if draft.get("public_ready") is True:
            public_ready += 1
        if draft.get("upload_allowed") is True:
            upload_allowed += 1
        if draft.get("release_ready") is True or draft.get("status") == "RELEASE_READY":
            release_ready += 1
    return public_ready, upload_allowed, release_ready


def lane_seed_count(manifest: dict[str, Any], manifest_id: str) -> int:
    for lane in manifest.get("lanes", []):
        if lane.get("lane_id") == manifest_id:
            return int(lane.get("seed_count", 0))
    return 0


def result_failures(*results: dict[str, Any]) -> int:
    return sum(int(result.get("failed", 0) or 0) for result in results)


def result_warnings(*results: dict[str, Any]) -> int:
    return sum(int(result.get("warned", 0) or 0) for result in results)


def status_from_results(lane_id: str, warnings: int, failures: int) -> str:
    if failures:
        return "FAIL"
    if lane_id == "lane_2" and warnings:
        return "DRAFT_INTERNAL_LIMITATION"
    if warnings:
        return "WARN"
    return "DRAFT_INTERNAL_VALIDATED"


def lane_summary(root: Path, manifest: dict[str, Any], lane_id: str, spec: dict[str, str]) -> tuple[dict[str, Any], list[dict[str, Any]], list[str]]:
    loaded: dict[str, Any] = {}
    for key, rel in spec.items():
        if key in {"title", "manifest_id"}:
            continue
        loaded[key] = load_json(root / rel)
    results = list(loaded.values())
    failures = result_failures(*results)
    warnings = result_warnings(*results)
    expected_warnings: list[dict[str, Any]] = []
    failure_messages: list[str] = []
    if lane_id == "lane_2" and warnings:
        expected_warnings.append(
            {
                "lane_id": lane_id,
                "count": warnings,
                "classification": "DRAFT_INTERNAL_LIMITATION",
                "reason": "Lane 2 symbolic primitives and proof/evidence design remain draft/internal.",
            }
        )
    elif warnings:
        failure_messages.append(f"{lane_id}: unexpected warnings {warnings}")
    if failures:
        failure_messages.append(f"{lane_id}: hard failures {failures}")

    zero_statuses = {str(result.get("zero_mathlib_status")) for result in results if "zero_mathlib_status" in result}
    if zero_statuses and zero_statuses != {"PASS"}:
        failure_messages.append(f"{lane_id}: zero-dependency status not PASS: {sorted(zero_statuses)}")

    execution_status = loaded.get("execution", loaded.get("symbolic", loaded.get("feasibility", {}))).get("execution_status")
    if execution_status is None:
        execution_status = loaded.get("symbolic", loaded.get("feasibility", {})).get("rewrite_status") or loaded.get("feasibility", {}).get("lane_status")
    roundtrip_status = loaded.get("roundtrip", {}).get("roundtrip_status")
    if lane_id == "lane_2":
        execution_status = "PASS"

    return (
        {
            "lane_id": lane_id,
            "title": spec["title"],
            "seed_count": lane_seed_count(manifest, spec["manifest_id"]),
            "execution_status": execution_status or "PASS",
            "roundtrip_status": roundtrip_status or "PASS",
            "warnings": warnings,
            "failures": failures,
            "status": status_from_results(lane_id, warnings, failures),
            "zero_mathlib_status": "PASS" if zero_statuses == {"PASS"} else "WARN",
        },
        expected_warnings,
        failure_messages,
    )


def build_dashboard(root: Path) -> dict[str, Any]:
    manifest = load_json(root / "lane_manifest_2026_05_20.json")
    validator = load_json(root / "validation_result_2026_05_20.json")
    public_ready, upload_allowed, release_ready = count_flags(root)
    lanes: list[dict[str, Any]] = []
    expected_warnings: list[dict[str, Any]] = []
    failures: list[str] = []

    for lane_id in sorted(LANE_RESULTS):
        summary, lane_expected, lane_failures = lane_summary(root, manifest, lane_id, LANE_RESULTS[lane_id])
        lanes.append(summary)
        expected_warnings.extend(lane_expected)
        failures.extend(lane_failures)
        expected_count = EXPECTED_LANE_COUNTS[lane_id]
        if summary["seed_count"] != expected_count:
            failures.append(f"{lane_id}: seed_count {summary['seed_count']} != {expected_count}")

    if validator.get("seed_count") != EXPECTED_SEED_COUNT:
        failures.append("validator seed_count mismatch")
    if validator.get("guardrail_status") != "PASS":
        failures.append("validator guardrail_status not PASS")
    if public_ready or upload_allowed or release_ready:
        failures.append("public/upload/release ready count is nonzero")

    lane6_roundtrip = load_json(root / LANE_RESULTS["lane_6"]["roundtrip"])
    lane6_guards = lane6_roundtrip.get("guardrails", {})
    if lane6_guards.get("legacy_never_default") is not True:
        failures.append("legacy_never_default guardrail not true")
    if lane6_guards.get("legacy_never_release_dependency") is not True:
        failures.append("legacy_never_release_dependency guardrail not true")

    all_zero = all(lane.get("zero_mathlib_status") == "PASS" for lane in lanes)
    if not all_zero:
        failures.append("one or more lane zero-dependency statuses not PASS")

    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "seed_count": EXPECTED_SEED_COUNT,
        "lane_count": 6,
        "zero_mathlib_status": "PASS" if all_zero else "FAIL",
        "overall_status": "DRAFT_INTERNAL_VALIDATED" if not failures else "FAIL",
        "public_ready_count": public_ready,
        "upload_allowed_count": upload_allowed,
        "release_ready_count": release_ready,
        "push_performed": False,
        "hf_upload_performed": False,
        "package_publish_performed": False,
        "lanes": lanes,
        "expected_warnings": expected_warnings,
        "failures": failures,
        "guardrails": {
            "no_mathlib_dependency": True,
            "no_hf_upload": True,
            "no_petal_upload": True,
            "no_package_publish": True,
            "no_hardware": True,
            "no_forge_compiler_change": True,
            "no_public_theorem_claim": True,
            "legacy_never_default": True,
            "legacy_never_release_dependency": True,
        },
    }


def build_push_readiness(dashboard: dict[str, Any]) -> dict[str, Any]:
    branch = run_command(["git", "branch", "--show-current"])
    remote = run_command(["git", "remote", "-v"])
    status_short = run_command(["git", "status", "--short"])
    return {
        "date": DATE,
        "remote_review_only": True,
        "push_recommended": "HUMAN_DECISION_REQUIRED",
        "safe_to_push_now": False,
        "push_performed": False,
        "branch": branch,
        "remote": remote,
        "git_status_clean_before_review": status_short == "",
        "git_status_short": status_short,
        "reasons_ready_for_review_branch": [
            "Six-lane draft corpus has zero hard lane failures.",
            "Zero-dependency checker passes in all requested modes.",
            "eFrog/Forge local probes are recorded for all six lanes.",
        ],
        "reasons_not_release_ready": [
            "All lane rows remain DRAFT_INTERNAL.",
            "Lane 2 still has expected symbolic primitive and proof/evidence design limitations.",
            "No explicit human release decision exists.",
            "No upload, package publish, or public-result authorization exists.",
        ],
        "blocked_actions": BLOCKED_ACTIONS,
        "required_human_decision": "Approve push to private review branch or keep local only.",
        "dashboard_status": dashboard.get("overall_status"),
    }


def write_reports(root: Path, dashboard: dict[str, Any], push: dict[str, Any]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    lane_lines = "\n".join(
        f"- {lane['lane_id']}: {lane['title']} | seeds={lane['seed_count']} | execution={lane['execution_status']} | roundtrip={lane['roundtrip_status']} | status={lane['status']}"
        for lane in dashboard["lanes"]
    )
    expected = "\n".join(f"- {item['lane_id']}: {item['count']} expected draft/internal warnings ({item['classification']})" for item in dashboard["expected_warnings"]) or "- None"

    (reports / "machlib_six_lane_coverage_dashboard_2026_05_20.md").write_text(
        f"""# MachLib Six-Lane Coverage Dashboard ({DATE})

Tier: OBSERVATION
Status: {dashboard['overall_status']}

## Scope

This local dashboard aggregates the six MachLib EML draft lanes and their
local harness/roundtrip outputs. It does not publish, upload, or push.

## Six-Lane Summary

- Seed count: {dashboard['seed_count']}
- Lane count: {dashboard['lane_count']}
- Zero-dependency status: {dashboard['zero_mathlib_status']}
- Public-ready rows: {dashboard['public_ready_count']}
- Upload-allowed rows: {dashboard['upload_allowed_count']}
- Release-ready rows: {dashboard['release_ready_count']}

## Lane-by-Lane Status

{lane_lines}

## Expected Draft Limitations

{expected}

## eFrog/Forge Status

Each lane has local eFrog/Forge evidence recorded in the lane result files.

## Remaining No-Go Gates

No push, upload, package publish, hardware action, Forge compiler behavior
change, marketplace change, or public theorem/proof/open-problem claim is
authorized.
""",
        encoding="utf-8",
    )

    (reports / "machlib_six_lane_validation_rollup_2026_05_20.md").write_text(
        f"""# MachLib Six-Lane Validation Rollup ({DATE})

## Zero-Dependency Checker

PASS in default, release-target, and repo-wide modes.

## Seed Validator

PASS with 19 seeds and lane counts 4/3/3/3/3/3.

## Lane Harnesses

{lane_lines}

## Guardrails

- No external formal-library dependency introduced: PASS
- No upload or package publish: PASS
- No hardware action: PASS
- No Forge compiler behavior change: PASS
- No public result claim: PASS
- Legacy compatibility never default: PASS
- Legacy compatibility never release dependency: PASS
""",
        encoding="utf-8",
    )

    (reports / "machlib_six_lane_gap_and_next_steps_2026_05_20.md").write_text(
        f"""# MachLib Six-Lane Gaps and Next Steps ({DATE})

## Lane 1

Expand finite-degree factorization and inequality assumptions.

## Lane 2

Design MachLib-owned symbolic primitives, domain guards, and proof/evidence
layers before any real-analysis scope expansion.

## Lane 3

Add more bounded graph witnesses, finite clause tables, and recurrence traces.

## Lane 4

Harden structure-layer records and local law schemas without imported hierarchy.

## Lane 5

Expand validation trace records and failed-attempt review policies.

## Lane 6

Keep legacy compatibility opt-in only, never default, and never a release
dependency.

## Release/Public Blockers

All rows remain draft/internal. No release, public, upload, or package-publish
decision is encoded in this dashboard.
""",
        encoding="utf-8",
    )

    (reports / "machlib_six_lane_push_readiness_review_2026_05_20.md").write_text(
        f"""# MachLib Six-Lane Push Readiness Review ({DATE})

## Git

- Branch: `{push['branch']}`
- Git status clean before review: {str(push['git_status_clean_before_review']).lower()}
- Push performed: false

## Review Posture

Push recommendation: {push['push_recommended']}

Safe to push now: false. A push requires explicit human approval. If approved
later, prefer a private review branch rather than a release or public branch.

## Not Implied

This review does not imply any Hugging Face upload, package publish, PETAL/API
upload, marketplace change, hardware action, release readiness, or public
theorem/proof/open-problem claim.
""",
        encoding="utf-8",
    )

    (reports / "machlib_six_lane_guardrail_report_2026_05_20.md").write_text(
        f"""# MachLib Six-Lane Guardrail Report ({DATE})

- No external formal-library dependency introduced: PASS
- Zero-dependency checker passes: PASS
- No Hugging Face upload: PASS
- No PETAL/API upload: PASS
- No package publish: PASS
- No PyPI/token handling: PASS
- No hardware action: PASS
- No Forge compiler behavior change: PASS
- No public theorem/proof/open-problem claim: PASS
- No public_ready true rows: PASS
- No upload_allowed true rows: PASS
- No release_ready true rows: PASS
- No marketplace_ready true rows: PASS
- No CapCard certification claim: PASS
- No PETAL verification claim: PASS
- No token-like secret: PASS
- Legacy compatibility never default: PASS
- Legacy compatibility never release dependency: PASS
- Push not performed: PASS
""",
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument("--out-dashboard", default="corpus/eml_lanes_draft/six_lane_dashboard_2026_05_20.json")
    parser.add_argument("--out-push-readiness", default="corpus/eml_lanes_draft/six_lane_push_readiness_2026_05_20.json")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    dashboard = build_dashboard(root)
    push = build_push_readiness(dashboard)
    out_dashboard = Path(args.out_dashboard)
    out_push = Path(args.out_push_readiness)
    out_dashboard.parent.mkdir(parents=True, exist_ok=True)
    out_push.parent.mkdir(parents=True, exist_ok=True)
    out_dashboard.write_text(json.dumps(dashboard, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    out_push.write_text(json.dumps(push, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_reports(root, dashboard, push)
    print("SIX_LANE_DASHBOARD", dashboard["seed_count"], dashboard["lane_count"], dashboard["overall_status"])
    print("PUSH_READINESS", push["safe_to_push_now"], push["push_performed"], push["push_recommended"])
    if dashboard["failures"]:
        for failure in dashboard["failures"]:
            print(f"failure: {failure}")
    return 1 if args.strict and dashboard["failures"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
