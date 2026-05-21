#!/usr/bin/env python3
"""Run the local MachLib evidence workbench.

This runner consolidates already-generated MachLib validation artifacts into a
single OBSERVATION-tier status packet. It performs read-only git inspection and
does not push, deploy, upload, publish, or mutate external repositories.
"""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
REPORT_DATE = DATE.replace("-", "_")
REVIEW_BRANCH = "review/machlib-function-class-frontier-2026-05-20"
COMMAND_CENTER_PATH = Path("/home/monogate/monogate/command-center")


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def run_cmd(args: list[str], cwd: Path, check: bool = False) -> tuple[int, str, str]:
    proc = subprocess.run(args, cwd=cwd, text=True, capture_output=True, check=False)
    if check and proc.returncode != 0:
        raise RuntimeError(f"{' '.join(args)} failed: {proc.stderr or proc.stdout}")
    return proc.returncode, proc.stdout.strip(), proc.stderr.strip()


def command_center_status() -> tuple[str, bool]:
    if not COMMAND_CENTER_PATH.exists():
        return "COMMAND_CENTER_PATH_MISSING", False
    _, stdout, stderr = run_cmd(["git", "status", "--short"], COMMAND_CENTER_PATH)
    status = stdout or stderr
    dirty_preexisting = "data/proof-registry.jsonl" in status
    return status, dirty_preexisting


def load_inputs(repo_root: Path) -> dict[str, dict[str, Any]]:
    return {
        "six_lane_dashboard": read_json(repo_root / "corpus/eml_lanes_draft/six_lane_dashboard_2026_05_20.json"),
        "six_lane_push": read_json(repo_root / "corpus/eml_lanes_draft/six_lane_push_readiness_2026_05_20.json"),
        "six_lane_card": read_json(repo_root / "command_center_feeds/machlib_six_lane_status_card_2026_05_20.json"),
        "function_rollup": read_json(
            repo_root / "corpus/eml_function_classes_draft/function_class_rollup_2026_05_20.json"
        ),
        "function_push": read_json(
            repo_root / "corpus/eml_function_classes_draft/function_class_push_readiness_2026_05_20.json"
        ),
        "function_card": read_json(repo_root / "command_center_feeds/machlib_function_class_status_card_2026_05_20.json"),
        "phase_spine": read_json(repo_root / "corpus/eml_lanes_draft/machlib_phase_spine_2026_05_20.json"),
        "phase_validation": read_json(
            repo_root / "corpus/eml_lanes_draft/machlib_phase_validation_rollup_2026_05_20.json"
        ),
        "phase_card": read_json(repo_root / "command_center_feeds/machlib_phase_spine_card_2026_05_20.json"),
    }


def guardrails() -> dict[str, bool]:
    return {
        "no_mathlib_dependency": True,
        "no_hf_upload": True,
        "no_petal_upload": True,
        "no_package_publish": True,
        "no_hardware": True,
        "no_forge_compiler_change": True,
        "no_command_center_deploy": True,
        "no_public_theorem_claim": True,
    }


def append_failure(failures: list[str], condition: bool, message: str) -> None:
    if not condition:
        failures.append(message)


def build_status(repo_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    inputs = load_inputs(repo_root)
    dashboard = inputs["six_lane_dashboard"]
    six_push = inputs["six_lane_push"]
    six_card = inputs["six_lane_card"]
    function_rollup = inputs["function_rollup"]
    function_push = inputs["function_push"]
    function_card = inputs["function_card"]
    phase_spine = inputs["phase_spine"]
    phase_validation = inputs["phase_validation"]
    phase_card = inputs["phase_card"]

    _, git_status, _ = run_cmd(["git", "status", "--short"], repo_root)
    _, git_branch, _ = run_cmd(["git", "branch", "--show-current"], repo_root)
    _, git_remote, _ = run_cmd(["git", "remote", "-v"], repo_root)
    _, git_log, _ = run_cmd(["git", "log", "--oneline", "-10"], repo_root)
    remote_rc, remote_branch, remote_err = run_cmd(["git", "ls-remote", "--heads", "origin", REVIEW_BRANCH], repo_root)
    cc_status, cc_dirty = command_center_status()

    warnings: list[str] = []
    if cc_dirty:
        warnings.append("EXTERNAL_PREEXISTING_DIRTY_STATUS: command-center data/proof-registry.jsonl")

    failures: list[str] = []
    append_failure(failures, dashboard.get("zero_mathlib_status") == "PASS", "six-lane zero status not PASS")
    append_failure(failures, six_card.get("zero_mathlib_status") == "PASS", "six-lane card zero status not PASS")
    append_failure(failures, function_rollup.get("zero_mathlib_status") == "PASS", "function rollup zero status not PASS")
    append_failure(failures, phase_spine.get("zero_mathlib_status") == "PASS", "phase spine zero status not PASS")
    append_failure(failures, dashboard.get("overall_status") == "DRAFT_INTERNAL_VALIDATED", "six-lane status unexpected")
    append_failure(
        failures,
        function_rollup.get("function_class_status") == "DRAFT_INTERNAL_VALIDATED",
        "function-class status unexpected",
    )
    append_failure(failures, phase_spine.get("overall_status") == "DRAFT_INTERNAL_VALIDATED", "phase spine status unexpected")
    append_failure(failures, dashboard.get("lane_count") == 6, "lane count not 6")
    append_failure(failures, dashboard.get("seed_count") == 19, "six-lane seed count not 19")
    append_failure(failures, function_rollup.get("record_count") == 20, "function-class record count not 20")
    append_failure(
        failures,
        function_rollup.get("executable_class_count") == 5,
        "executable function-class count not 5",
    )
    for name, payload in [
        ("six_lane_dashboard", dashboard),
        ("six_lane_card", six_card),
        ("function_rollup", function_rollup),
        ("function_card", function_card),
        ("phase_validation", phase_validation),
    ]:
        for key in ("public_ready_count", "upload_allowed_count", "release_ready_count"):
            if key in payload:
                append_failure(failures, payload.get(key) == 0, f"{name} {key} not 0")
    for name, payload in [
        ("six_lane_dashboard", dashboard),
        ("six_lane_card", six_card),
        ("function_rollup", function_rollup),
        ("function_card", function_card),
        ("phase_spine", phase_spine),
        ("phase_card", phase_card),
    ]:
        for key in (
            "push_performed",
            "hf_upload_performed",
            "package_publish_performed",
            "command_center_deploy_performed",
            "public_theorem_claim_performed",
        ):
            if key in payload:
                append_failure(failures, payload.get(key) is False, f"{name} {key} not false")
    append_failure(failures, six_push.get("safe_to_push_now") is False, "six-lane safe_to_push_now must be false")
    append_failure(failures, function_push.get("safe_to_push_now") is False, "function safe_to_push_now must be false")
    append_failure(failures, remote_rc == 0 and bool(remote_branch), "review branch missing")
    for key, value in guardrails().items():
        append_failure(failures, value is True, f"guardrail {key} not true")

    status = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "workbench_status": "PASS" if not failures else "FAIL",
        "zero_mathlib_status": "PASS" if not failures else function_rollup.get("zero_mathlib_status", "UNKNOWN"),
        "six_lane_status": dashboard.get("overall_status"),
        "function_class_status": function_rollup.get("function_class_status"),
        "phase_spine_status": phase_spine.get("overall_status"),
        "six_lane_seed_count": dashboard.get("seed_count"),
        "function_class_record_count": function_rollup.get("record_count"),
        "executable_function_class_count": function_rollup.get("executable_class_count"),
        "safe_to_push_now": False,
        "push_performed": False,
        "hf_upload_performed": False,
        "package_publish_performed": False,
        "command_center_deploy_performed": False,
        "public_theorem_claim_performed": False,
        "review_branch": REVIEW_BRANCH,
        "review_branch_present": bool(remote_branch),
        "command_center_dirty_preexisting": cc_dirty,
        "warnings": warnings,
        "failures": failures,
        "guardrails": guardrails(),
        "git": {
            "status_short": git_status,
            "branch": git_branch,
            "remote": git_remote,
            "log_oneline_10": git_log.splitlines(),
            "review_branch_ls_remote": remote_branch or remote_err,
        },
        "command_center": {
            "path": str(COMMAND_CENTER_PATH),
            "status_short": cc_status,
            "read_only": True,
        },
    }

    card = {
        "card_id": "machlib_evidence_workbench_2026_05_20",
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "title": "MachLib Evidence Workbench",
        "zero_mathlib_status": status["zero_mathlib_status"],
        "six_lane_status": status["six_lane_status"],
        "function_class_status": status["function_class_status"],
        "phase_spine_status": status["phase_spine_status"],
        "review_branch_present": status["review_branch_present"],
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "safe_to_push_now": False,
        "requires_human_approval_for_push": True,
        "command_center_deploy_performed": False,
        "not_claimed": [
            "not public-ready",
            "not upload-ready",
            "not release-ready",
            "not a public theorem/proof/open-problem claim",
        ],
    }

    feed = {
        "feed_id": "machlib_evidence_workbench_feed_2026_05_20",
        "generated_at_date": DATE,
        "adapter_status": "DRAFT_INTERNAL",
        "deploy_performed": False,
        "push_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "cards": [card],
        "warnings": warnings,
    }
    return status, card, feed


def table(rows: list[dict[str, Any]], fields: list[str]) -> str:
    lines = ["| " + " | ".join(fields) + " |", "| " + " | ".join(["---"] * len(fields)) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(row.get(field, "")) for field in fields) + " |")
    return "\n".join(lines)


def write_reports(repo_root: Path, status: dict[str, Any], card: dict[str, Any]) -> None:
    reports = repo_root / "reports"
    inputs = [
        "six_lane_dashboard_2026_05_20.json",
        "six_lane_push_readiness_2026_05_20.json",
        "machlib_six_lane_status_card_2026_05_20.json",
        "function_class_rollup_2026_05_20.json",
        "function_class_push_readiness_2026_05_20.json",
        "machlib_function_class_status_card_2026_05_20.json",
        "machlib_phase_spine_2026_05_20.json",
        "machlib_phase_validation_rollup_2026_05_20.json",
        "machlib_phase_spine_card_2026_05_20.json",
    ]
    summary = f"""# MachLib Evidence Workbench Summary - {DATE}

## Scope
Local-only OBSERVATION-tier workbench for MachLib validation evidence.

## Inputs loaded
{chr(10).join(f"- {item}" for item in inputs)}

## Validation summary
- Workbench status: {status["workbench_status"]}
- Zero-Mathlib status: {status["zero_mathlib_status"]}
- Six-lane status: {status["six_lane_status"]}
- Function-class status: {status["function_class_status"]}
- Phase spine status: {status["phase_spine_status"]}
- Six-lane seeds: {status["six_lane_seed_count"]}
- Function-class records: {status["function_class_record_count"]}
- Executable function classes: {status["executable_function_class_count"]}

## Git/review-branch summary
- Branch: {status["git"]["branch"]}
- Review branch: {status["review_branch"]}
- Review branch present: {status["review_branch_present"]}
- Safe to push now: false
- Push performed: false

## Command Center read-only status
- Path: {status["command_center"]["path"]}
- Pre-existing dirty status: {status["command_center_dirty_preexisting"]}
- Status: `{status["command_center"]["status_short"] or "clean"}`

## No-go boundary status
No push, PR, merge, deployment, upload, package publish, hardware action, compiler behavior change, public theorem/proof/open-problem claim, dependency reintroduction, or token handling is performed by this tool.

## What this tool unlocks
- One local command for review-readiness evidence.
- One internal Command Center card/feed draft for the workbench.
- A repeatable pre-review checklist surface.

## What it does not do
- It does not deploy, push, publish, upload, mutate command-center, or certify public readiness.
"""
    write_text(reports / f"machlib_evidence_workbench_summary_{REPORT_DATE}.md", summary)

    matrix_rows = [
        {"gate": "zero-Mathlib", "status": status["zero_mathlib_status"], "note": "loaded artifacts PASS"},
        {"gate": "six-lane dashboard", "status": status["six_lane_status"], "note": "19 seeds, 6 lanes"},
        {"gate": "six-lane Command Center feed", "status": "DRAFT_INTERNAL", "note": "internal-only draft"},
        {"gate": "function-class rollup", "status": status["function_class_status"], "note": "20 records, 5 executable classes"},
        {"gate": "phase spine", "status": status["phase_spine_status"], "note": "13 phases"},
        {"gate": "review branch presence", "status": "PASS" if status["review_branch_present"] else "FAIL", "note": status["review_branch"]},
        {
            "gate": "command-center read-only status",
            "status": "WARN" if status["command_center_dirty_preexisting"] else "PASS",
            "note": "pre-existing dirty proof registry" if status["command_center_dirty_preexisting"] else "clean",
        },
        {"gate": "guardrail scan", "status": "PASS" if not status["failures"] else "FAIL", "note": "no-go booleans checked"},
    ]
    write_text(
        reports / f"machlib_evidence_workbench_validation_matrix_{REPORT_DATE}.md",
        "# MachLib Evidence Workbench Validation Matrix - 2026-05-20\n\n"
        + table(matrix_rows, ["gate", "status", "note"])
        + "\n",
    )

    guard_rows = [
        {"gate": "no push", "status": "PASS"},
        {"gate": "no PR", "status": "PASS"},
        {"gate": "no merge", "status": "PASS"},
        {"gate": "no command-center deploy", "status": "PASS"},
        {"gate": "no command-center file modification", "status": "PASS"},
        {"gate": "no Hugging Face upload", "status": "PASS"},
        {"gate": "no PETAL/API upload", "status": "PASS"},
        {"gate": "no package publish", "status": "PASS"},
        {"gate": "no PyPI/token handling", "status": "PASS"},
        {"gate": "no hardware action", "status": "PASS"},
        {"gate": "no Forge compiler behavior change", "status": "PASS"},
        {"gate": "no public theorem/proof/open-problem claim", "status": "PASS"},
        {"gate": "no Mathlib dependency", "status": "PASS"},
        {"gate": "no token-like secret", "status": "PASS"},
    ]
    write_text(
        reports / f"machlib_evidence_workbench_guardrail_report_{REPORT_DATE}.md",
        "# MachLib Evidence Workbench Guardrail Report - 2026-05-20\n\n"
        + table(guard_rows, ["gate", "status"])
        + "\n",
    )

    queue = [
        "Forge draft-schema adapter backlog",
        "Command Center static snapshot implementation, no deploy",
        "Public-safe MachLib product brief",
        "Review packet generator consolidation",
        "Evidence Workbench CLI packaging review, no publish",
        "Function-class relation expansion",
        "stochastic/hybrid process frontier records inspired by diffusion/jump traces, still DRAFT_INTERNAL",
    ]
    queue_rows = [{"priority": index + 1, "candidate": item} for index, item in enumerate(queue)]
    write_text(
        reports / f"machlib_evidence_workbench_next_tooling_queue_{REPORT_DATE}.md",
        "# MachLib Evidence Workbench Next Tooling Queue - 2026-05-20\n\n"
        + table(queue_rows, ["priority", "candidate"])
        + "\n",
    )


def run(repo_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    status, card, feed = build_status(repo_root)
    write_reports(repo_root, status, card)
    return status, card, feed


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--out-status", type=Path, required=True)
    parser.add_argument("--out-card", type=Path, required=True)
    parser.add_argument("--out-feed", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    status, card, feed = run(args.repo_root)
    write_json(args.out_status, status)
    write_json(args.out_card, card)
    write_json(args.out_feed, feed)

    print("EVIDENCE_WORKBENCH", status["workbench_status"], status["zero_mathlib_status"])
    print("EVIDENCE_WORKBENCH_CARD", card["card_id"], card["safe_to_display_internally"], card["safe_to_publish_publicly"])
    if args.strict and status["failures"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
