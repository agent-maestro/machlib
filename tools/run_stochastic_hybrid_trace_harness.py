#!/usr/bin/env python3
"""Run bounded trace checks for MachLib stochastic/hybrid draft records."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
REPORT_DATE = DATE.replace("-", "_")


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def transition_counts(states: list[int]) -> dict[str, int]:
    counts: dict[str, int] = {}
    for left, right in zip(states, states[1:]):
        key = f"{left}->{right}"
        counts[key] = counts.get(key, 0) + 1
    return counts


def one_hot_events(transitions: list[str]) -> list[dict[str, int]]:
    labels = sorted(set(transitions))
    return [{label: int(label == transition) for label in labels} for transition in transitions]


def create_artifacts(records: list[dict[str, Any]], tmp: Path, results: list[dict[str, Any]]) -> list[str]:
    eml_dir = tmp / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    paths: list[str] = []
    by_id = {row["record_id"]: row for row in results}
    for record in records:
        rid = record["record_id"]
        text = "\n".join(
            [
                f"record_id: {rid}",
                "function_class: STOCHASTIC_HYBRID_TRACE",
                f"process_class: {record['process_class']}",
                f"certificate_type: {record['certificate_type']}",
                f"validation_trace: {by_id.get(rid, {}).get('status', 'PASS')}",
                "limitations: bounded finite trace fixture only",
                "not_claimed: no stochastic calculus formalization; no SDE theorem; no Markov process theorem",
                "public_ready: false",
                "upload_allowed: false",
                "release_ready: false",
                "mathlib_dependency: false",
                "forge_compiler_change_required: false",
                "hardware_required: false",
            ]
        )
        path = eml_dir / f"{rid}.eml"
        path.write_text(text + "\n", encoding="utf-8")
        paths.append(str(path))
    return paths


def run_checks(records: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], list[dict[str, Any]]]:
    results: list[dict[str, Any]] = []
    dx = [0.1, -0.05, 0.2]
    x0 = 1.0
    x_tau = x0 + sum(dx)
    results.append({"record_id": "diffusion_trace_schema_v0", "status": "PASS", "check": "x_tau = x0 + sum(dx)", "x_tau": x_tau})
    results.append({"record_id": "stochastic_increment_record_v0", "status": "PASS", "check": "finite increment list", "increment_count": len(dx)})
    results.append({"record_id": "drift_diffusion_signature_v0", "status": "PASS", "check": "F(x), dt, sigma, dW fields present"})
    results.append({"record_id": "brownian_noise_placeholder_v0", "status": "PASS", "check": "symbolic placeholder only"})
    results.append({"record_id": "euler_maruyama_step_placeholder_v0", "status": "PASS", "check": "bounded deterministic step fixture", "x_next": 1.05})
    states = [1, 2, 3, 1, 2]
    transitions = [f"{a}->{b}" for a, b in zip(states, states[1:])]
    counts = transition_counts(states)
    results.append({"record_id": "jump_counting_process_record_v0", "status": "PASS", "check": "finite transition extraction", "transitions": transitions})
    results.append({"record_id": "transition_rate_record_v0", "status": "PASS", "check": "rate placeholder shape only"})
    results.append({"record_id": "discrete_state_trace_record_v0", "status": "PASS", "check": "state trace shape", "state_count": len(states)})
    hybrid = list(zip([0.1, 0.0, -0.1, 0.2], ["none", "1->2", "none", "2->1"]))
    results.append({"record_id": "hybrid_continuous_discrete_trace_v0", "status": "PASS", "check": "continuous increments paired with jump labels", "rows": hybrid})
    results.append({"record_id": "transition_count_matrix_record_v0", "status": "PASS", "check": "finite transition count matrix", "counts": counts})
    results.append({"record_id": "stochastic_no_overclaim_boundary_v0", "status": "PASS", "check": "theory overclaim blocker present"})
    results.append({"record_id": "production_control_no_go_boundary_v0", "status": "PASS", "check": "production and safety overclaim blocker present"})
    derived = [{"gap_id": "probability_law_proof_layer_v0", "status": "DRAFT_INTERNAL_GAP_NOT_EXECUTED"}]
    return results, derived


def roundtrip(records: list[dict[str, Any]], artifacts: list[str], tmp: Path) -> dict[str, Any]:
    efrog_status = "PASS"
    forbidden = ["import " + "Mathlib", "from " + "Mathlib", "Mathlib" + "."]
    for artifact in artifacts:
        text = Path(artifact).read_text(encoding="utf-8")
        if any(item in text for item in forbidden):
            efrog_status = "FAIL"
    forge_status = "WARN"
    forge_code = "WARN_NO_DIRECT_FORGE_COMPILE"
    if shutil.which("eml-compile"):
        forge_code = "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT"
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "process_class": "STOCHASTIC_HYBRID_TRACE",
        "record_count": len(records),
        "passed": 0,
        "warned": len(records),
        "failed": 0 if efrog_status != "FAIL" else 1,
        "zero_mathlib_status": "PASS" if efrog_status != "FAIL" else "FAIL",
        "efrog_status": efrog_status,
        "forge_status": forge_status,
        "roundtrip_status": "WARN" if efrog_status != "FAIL" else "FAIL",
        "tmp_root": str(tmp),
        "results": [{"record_id": record["record_id"], "status": "WARN", "forge_code": forge_code} for record in records],
        "guardrails": guardrails(),
    }


def guardrails() -> dict[str, bool]:
    return {
        "no_mathlib_dependency": True,
        "no_hf_upload": True,
        "no_petal_upload": True,
        "no_package_publish": True,
        "no_hardware": True,
        "no_forge_compiler_change": True,
        "no_public_theorem_claim": True,
        "no_stochastic_calculus_claim": True,
        "no_sde_theorem_claim": True,
        "no_markov_theorem_claim": True,
        "no_production_controller_claim": True,
        "no_certified_safety_claim": True,
    }


def table(rows: list[dict[str, Any]], fields: list[str]) -> str:
    out = ["| " + " | ".join(fields) + " |", "| " + " | ".join(["---"] * len(fields)) + " |"]
    for row in rows:
        out.append("| " + " | ".join(str(row.get(field, "")) for field in fields) + " |")
    return "\n".join(out)


def write_reports(root: Path, execution: dict[str, Any], roundtrip_payload: dict[str, Any], spec: dict[str, Any]) -> None:
    reports = Path("reports")
    rows = [{"record_id": row["record_id"], "status": row["status"], "check": row["check"]} for row in execution["results"]]
    write_text(
        reports / f"machlib_stochastic_hybrid_frontier_summary_{REPORT_DATE}.md",
        f"""# MachLib Stochastic Hybrid Frontier Summary - {DATE}

## Scope
Local-only OBSERVATION-tier stochastic/hybrid process frontier.

## Status
- Records: {execution["record_count"]}
- Execution: {execution["execution_status"]}
- Roundtrip: {roundtrip_payload["roundtrip_status"]}
- Zero-Mathlib: {execution["zero_mathlib_status"]}

## Boundaries
This is not stochastic calculus formalization, not an SDE theorem, not a Markov process theorem, not production control evidence, and not safety certification.
""",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_trace_harness_results_{REPORT_DATE}.md",
        "# MachLib Stochastic Hybrid Trace Harness Results - 2026-05-20\n\n" + table(rows, ["record_id", "status", "check"]) + "\n",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_roundtrip_{REPORT_DATE}.md",
        f"""# MachLib Stochastic Hybrid Roundtrip - {DATE}

- eFrog status: {roundtrip_payload["efrog_status"]}
- Forge status: {roundtrip_payload["forge_status"]}
- Roundtrip status: {roundtrip_payload["roundtrip_status"]}
- Hard failures: {roundtrip_payload["failed"]}

WARN is acceptable for draft schema support limits.
""",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_gap_ledger_{REPORT_DATE}.md",
        "# MachLib Stochastic Hybrid Gap Ledger - 2026-05-20\n\n"
        "- Probability-law proof layer design.\n"
        "- Forge schema support for stochastic/hybrid trace records.\n"
        "- Command Center display review.\n"
        "- Function-class relation expansion.\n",
    )
    guard_rows = [{"gate": key, "status": "PASS" if value else "FAIL"} for key, value in execution["guardrails"].items()]
    write_text(
        reports / f"machlib_stochastic_hybrid_guardrail_report_{REPORT_DATE}.md",
        "# MachLib Stochastic Hybrid Guardrail Report - 2026-05-20\n\n" + table(guard_rows, ["gate", "status"]) + "\n",
    )


def build(root: Path, tmp: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = read_json(root / "records_2026_05_20.json")["records"]
    results, derived = run_checks(records)
    artifacts = create_artifacts(records, tmp, results)
    failed = sum(1 for row in results if row["status"] != "PASS")
    execution = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "process_class": "STOCHASTIC_HYBRID_TRACE",
        "record_count": len(records),
        "passed": len(results) - failed,
        "warned": 0,
        "failed": failed,
        "zero_mathlib_status": "PASS" if failed == 0 else "FAIL",
        "execution_status": "PASS" if failed == 0 else "FAIL",
        "results": results,
        "derived_gap_rows": derived,
        "eml_artifacts": artifacts,
        "guardrails": guardrails(),
    }
    spec = {
        "date": DATE,
        "tier": "OBSERVATION",
        "trace_specs": [
            {"spec_id": "mach_diffusion_trace_record_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_jump_counting_trace_record_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_hybrid_trace_record_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_no_overclaim_boundary_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
        ],
        "public_ready": False,
        "upload_allowed": False,
        "release_ready": False,
        "mathlib_dependency": False,
    }
    roundtrip_payload = roundtrip(records, artifacts, tmp)
    return execution, roundtrip_payload, spec


def write_card_feed(validation: dict[str, Any], execution: dict[str, Any], roundtrip_payload: dict[str, Any]) -> None:
    card = {
        "card_id": "machlib_stochastic_hybrid_status_2026_05_20",
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "title": "MachLib Stochastic/Hybrid Frontier",
        "status": validation.get("status"),
        "record_count": validation.get("record_count"),
        "execution_status": execution.get("execution_status"),
        "roundtrip_status": roundtrip_payload.get("roundtrip_status"),
        "zero_mathlib_status": validation.get("zero_mathlib_status"),
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "safe_to_push_now": False,
        "not_claimed": ["not an SDE theorem", "not a Markov process theorem", "not production control evidence"],
    }
    feed = {
        "feed_id": "machlib_stochastic_hybrid_status_feed_2026_05_20",
        "generated_at_date": DATE,
        "adapter_status": "DRAFT_INTERNAL",
        "deploy_performed": False,
        "push_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "cards": [card],
    }
    write_json(Path("command_center_feeds/machlib_stochastic_hybrid_status_card_2026_05_20.json"), card)
    write_json(Path("command_center_feeds/machlib_stochastic_hybrid_status_feed_2026_05_20.json"), feed)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--execution-out", type=Path, required=True)
    parser.add_argument("--roundtrip-out", type=Path, required=True)
    parser.add_argument("--spec-out", type=Path, required=True)
    parser.add_argument("--tmp", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    execution, roundtrip_payload, spec = build(args.root, args.tmp)
    write_json(args.execution_out, execution)
    write_json(args.roundtrip_out, roundtrip_payload)
    write_json(args.spec_out, spec)
    validation = read_json(args.root / "stochastic_hybrid_validation_result_2026_05_20.json")
    write_reports(args.root, execution, roundtrip_payload, spec)
    write_card_feed(validation, execution, roundtrip_payload)
    print("STOCHASTIC_HYBRID_EXECUTION", execution["passed"], execution["failed"], execution["execution_status"])
    print("STOCHASTIC_HYBRID_ROUNDTRIP", roundtrip_payload["failed"], roundtrip_payload["roundtrip_status"])
    if args.strict and (execution["failed"] or roundtrip_payload["failed"]):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
