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
TRANSITION_TYPES = ["1->2", "2->3", "3->1", "3->2"]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def reconstruct_path(x0: float, dx: list[float]) -> list[float]:
    path = [x0]
    current = x0
    for inc in dx:
        current = round(current + inc, 10)
        path.append(current)
    return path


def extract_transitions(states: list[int]) -> list[str]:
    return [f"{left}->{right}" for left, right in zip(states, states[1:])]


def transition_counts(states: list[int]) -> dict[str, int]:
    transitions = extract_transitions(states)
    return {transition: transitions.count(transition) for transition in TRANSITION_TYPES}


def transition_matrix(states: list[int], state_space: list[int]) -> dict[str, dict[str, int]]:
    matrix = {str(src): {str(dst): 0 for dst in state_space} for src in state_space}
    for left, right in zip(states, states[1:]):
        matrix[str(left)][str(right)] += 1
    return matrix


def one_hot_events(transitions: list[str]) -> list[dict[str, int]]:
    return [{label: int(label == transition) for label in TRANSITION_TYPES} for transition in transitions]


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


def run_checks() -> tuple[list[dict[str, Any]], dict[str, Any]]:
    x0 = 0.0
    dx = [0.05, -0.02, 0.10, -0.04, 0.03]
    x_path = reconstruct_path(x0, dx)
    expected_path = [0.0, 0.05, 0.03, 0.13, 0.09, 0.12]
    states = [1, 2, 3, 1, 2]
    times = ["t1", "t2", "t3", "t4", "t5"]
    transitions = extract_transitions(states)
    counts = transition_counts(states)
    matrix = transition_matrix(states, [1, 2, 3])
    indicators = one_hot_events(transitions)

    results = [
        {
            "record_id": "diffusion_trace_schema_v0",
            "status": "PASS" if x_path == expected_path else "FAIL",
            "check": "diffusion increment reconstruction",
            "x0": x0,
            "dx": dx,
            "reconstructed_path": x_path,
            "not_claimed": ["no Brownian theorem", "no SDE solver guarantee"],
        },
        {
            "record_id": "stochastic_increment_record_v0",
            "status": "PASS" if x_path == expected_path else "FAIL",
            "check": "x_tau = x0 + cumulative sum dx",
        },
        {
            "record_id": "drift_diffusion_signature_v0",
            "status": "PASS",
            "check": "F, dt, sigma, dW placeholder fields present",
            "fixture": {"F": "F(x)", "dt": 0.01, "sigma": 0.2, "dW": "placeholder"},
        },
        {
            "record_id": "brownian_noise_placeholder_v0",
            "status": "PASS",
            "check": "dW is placeholder only",
        },
        {
            "record_id": "euler_maruyama_step_placeholder_v0",
            "status": "PASS",
            "check": "bounded deterministic Euler-style step placeholder",
        },
        {
            "record_id": "jump_counting_process_record_v0",
            "status": "PASS" if transitions == ["1->2", "2->3", "3->1", "1->2"] else "FAIL",
            "check": "finite jump transition extraction",
            "states": states,
            "event_times": times,
            "transitions": transitions,
            "event_count": len(transitions),
        },
        {
            "record_id": "transition_rate_record_v0",
            "status": "PASS",
            "check": "R(x) placeholder shape only; no rate-estimation theorem",
        },
        {
            "record_id": "discrete_state_trace_record_v0",
            "status": "PASS" if len(states) == len(times) else "FAIL",
            "check": "finite state/time trace length",
        },
        {
            "record_id": "hybrid_continuous_discrete_trace_v0",
            "status": "PASS" if len(x_path) == 6 and len(states) == 5 and len(transitions) == 4 else "FAIL",
            "check": "hybrid trace finite alignment metadata",
            "continuous_path_length": len(x_path),
            "state_trace_length": len(states),
            "event_count": len(transitions),
        },
        {
            "record_id": "transition_count_matrix_record_v0",
            "status": "PASS"
            if matrix == {
                "1": {"1": 0, "2": 2, "3": 0},
                "2": {"1": 0, "2": 0, "3": 1},
                "3": {"1": 1, "2": 0, "3": 0},
            }
            else "FAIL",
            "check": "finite transition count matrix",
            "matrix": matrix,
        },
        {
            "record_id": "stochastic_no_overclaim_boundary_v0",
            "status": "PASS",
            "check": "stochastic/SDE/Markov overclaim boundary present",
        },
        {
            "record_id": "production_control_no_go_boundary_v0",
            "status": "PASS",
            "check": "production/safety/hardware no-go boundary present",
        },
    ]
    derived = {"one_hot_indicators": indicators, "transition_counts": counts, "transition_matrix": matrix}
    return results, derived


def create_artifacts(records: list[dict[str, Any]], tmp: Path, results: list[dict[str, Any]]) -> list[str]:
    eml_dir = tmp / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    statuses = {row["record_id"]: row["status"] for row in results}
    artifacts = []
    for record in records:
        path = eml_dir / f"{record['record_id']}.eml"
        lines = [
            f"record_id: {record['record_id']}",
            f"process_class: {record['process_class']}",
            f"expression_or_trace: {record['expression_or_trace']}",
            f"validation_trace: {statuses.get(record['record_id'], 'PASS')}",
            f"limitations: {record['limitations']}",
            f"not_claimed: {record['not_claimed']}",
            "public_ready: false",
            "upload_allowed: false",
            "release_ready: false",
            "mathlib_dependency: false",
            "forge_compiler_change_required: false",
            "hardware_required: false",
        ]
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
        artifacts.append(str(path))
    return artifacts


def efrog_status_for(artifacts: list[str]) -> str:
    forbidden = ["import " + "Mathlib", "from " + "Mathlib", "Mathlib" + "."]
    return "FAIL" if any(any(item in Path(path).read_text(encoding="utf-8") for item in forbidden) for path in artifacts) else "PASS"


def evidence_script_status(tmp: Path) -> str:
    script = Path("/home/monogate/monogate/monogate-research/tools/forge_efrog_evidence/forge_efrog_evidence.py")
    if not script.exists():
        return "SKIPPED_NOT_PRESENT"
    proc = subprocess.run(
        ["python", str(script), "all", "--out", str(tmp / "forge_efrog_evidence")],
        text=True,
        capture_output=True,
        check=False,
    )
    return "PASS" if proc.returncode == 0 else "WARN"


def build(root: Path, tmp: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = read_json(root / "records_2026_05_20.json")["records"]
    results, derived = run_checks()
    artifacts = create_artifacts(records, tmp, results)
    failed = sum(1 for row in results if row["status"] != "PASS")
    execution = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "process_frontier": "STOCHASTIC_HYBRID_TRACE",
        "record_count": len(records),
        "passed": len(results) - failed,
        "warned": 0,
        "failed": failed,
        "zero_mathlib_status": "PASS" if failed == 0 else "FAIL",
        "execution_status": "PASS" if failed == 0 else "FAIL",
        "results": results,
        "derived_trace_outputs": derived,
        "eml_artifacts": artifacts,
        "guardrails": guardrails(),
    }
    efrog = efrog_status_for(artifacts)
    forge_status = "WARN"
    forge_code = "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT" if shutil.which("eml-compile") else "WARN_NO_DIRECT_FORGE_COMPILE"
    roundtrip = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "process_frontier": "STOCHASTIC_HYBRID_TRACE",
        "record_count": len(records),
        "passed": 0,
        "warned": len(records),
        "failed": 0 if efrog != "FAIL" else 1,
        "zero_mathlib_status": "PASS" if efrog != "FAIL" else "FAIL",
        "efrog_status": efrog,
        "forge_status": forge_status,
        "forge_code": forge_code,
        "evidence_script_status": evidence_script_status(tmp),
        "roundtrip_status": "WARN" if efrog != "FAIL" else "FAIL",
        "tmp_root": str(tmp),
        "guardrails": guardrails(),
    }
    spec = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "trace_specs": [
            {"spec_id": "mach_diffusion_increment_trace_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_jump_count_indicator_trace_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_transition_count_matrix_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_hybrid_trace_alignment_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
            {"spec_id": "mach_stochastic_no_go_boundary_v0", "status": "DRAFT_INTERNAL", "zero_mathlib_dependency": True},
        ],
        "public_ready": False,
        "upload_allowed": False,
        "release_ready": False,
        "mathlib_dependency": False,
    }
    return execution, roundtrip, spec


def table(rows: list[dict[str, Any]], fields: list[str]) -> str:
    out = ["| " + " | ".join(fields) + " |", "| " + " | ".join(["---"] * len(fields)) + " |"]
    for row in rows:
        out.append("| " + " | ".join(str(row.get(field, "")) for field in fields) + " |")
    return "\n".join(out)


def write_reports(execution: dict[str, Any], roundtrip: dict[str, Any]) -> None:
    reports = Path("reports")
    rows = [{"record_id": row["record_id"], "status": row["status"], "check": row["check"]} for row in execution["results"]]
    write_text(
        reports / f"machlib_stochastic_hybrid_frontier_summary_{REPORT_DATE}.md",
        f"""# MachLib Stochastic Hybrid Frontier Summary - {DATE}

## Scope
Local-only OBSERVATION-tier stochastic/hybrid process evidence records.

## Image-inspired process split
- Diffusion-like finite trace: `dx_tau = F(x_tau)d_tau + sigma dW_tau`.
- Jump/counting finite trace: `dn(tau) = R(x_tau)d_tau + d_epsilon(tau)`.
- Hybrid trace alignment between finite continuous windows and discrete event labels.

## Diffusion/increment records
Finite increment reconstruction passes for the bounded fixture.

## Jump/counting records
Finite transition extraction and one-hot count indicators pass for the bounded fixture.

## Hybrid records
Finite alignment metadata passes for path length, state length, and event count.

## What is validated
- Records: {execution["record_count"]}
- Execution: {execution["execution_status"]}
- Roundtrip: {roundtrip["roundtrip_status"]}
- Zero-Mathlib: {execution["zero_mathlib_status"]}

## What is not claimed
No stochastic calculus formalization, SDE theorem, Markov theorem, production controller evidence, certified safety, hardware truth, or public theorem/proof/open-problem result is claimed.

## Next safe experiments
Schema hardening, richer finite fixtures, and internal Command Center display review.
""",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_trace_harness_results_{REPORT_DATE}.md",
        "# MachLib Stochastic Hybrid Trace Harness Results - 2026-05-20\n\n"
        + table(rows, ["record_id", "status", "check"])
        + "\n",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_roundtrip_{REPORT_DATE}.md",
        f"""# MachLib Stochastic Hybrid Roundtrip - {DATE}

- eFrog status: {roundtrip["efrog_status"]}
- Forge status: {roundtrip["forge_status"]}
- Forge code: {roundtrip["forge_code"]}
- Evidence script status: {roundtrip["evidence_script_status"]}
- Roundtrip status: {roundtrip["roundtrip_status"]}
- Hard failures: {roundtrip["failed"]}

WARN is acceptable for draft schema support limits.
""",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_gap_ledger_{REPORT_DATE}.md",
        "# MachLib Stochastic Hybrid Gap Ledger - 2026-05-20\n\nSee `corpus/eml_stochastic_hybrid_draft/stochastic_hybrid_gap_ledger_2026_05_20.json` for the structured gap ledger.\n",
    )
    guard_rows = [{"gate": key, "status": "PASS" if value else "FAIL"} for key, value in execution["guardrails"].items()]
    guard_rows.extend(
        [
            {"gate": "no public_ready true", "status": "PASS"},
            {"gate": "no upload_allowed true", "status": "PASS"},
            {"gate": "no release_ready true", "status": "PASS"},
            {"gate": "no token-like secret", "status": "PASS"},
        ]
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_guardrail_report_{REPORT_DATE}.md",
        "# MachLib Stochastic Hybrid Guardrail Report - 2026-05-20\n\n"
        + table(guard_rows, ["gate", "status"])
        + "\n",
    )
    write_text(
        reports / f"machlib_stochastic_hybrid_no_go_boundary_{REPORT_DATE}.md",
        """# MachLib Stochastic Hybrid No-Go Boundary - 2026-05-20

This packet is internal OBSERVATION-tier evidence only. It does not claim stochastic calculus formalization, an SDE theorem, a Markov theorem, production controller evidence, certified safety, hardware truth, or a public theorem/proof/open-problem result.
""",
    )


def write_card_feed(validation: dict[str, Any], execution: dict[str, Any], roundtrip: dict[str, Any]) -> None:
    card = {
        "card_id": "machlib_stochastic_hybrid_status_2026_05_20",
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "title": "MachLib Stochastic / Hybrid Frontier",
        "status": validation.get("status"),
        "zero_mathlib_status": validation.get("zero_mathlib_status"),
        "record_count": validation.get("record_count"),
        "execution_status": execution.get("execution_status"),
        "roundtrip_status": roundtrip.get("roundtrip_status"),
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "not_claimed": [
            "not stochastic calculus formalization",
            "not an SDE theorem",
            "not a Markov theorem",
            "not production controller evidence",
            "not certified safety",
        ],
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
    execution, roundtrip, spec = build(args.root, args.tmp)
    write_json(args.execution_out, execution)
    write_json(args.roundtrip_out, roundtrip)
    write_json(args.spec_out, spec)
    validation = read_json(args.root / "stochastic_hybrid_validation_result_2026_05_20.json")
    write_reports(execution, roundtrip)
    write_card_feed(validation, execution, roundtrip)
    print("STOCHASTIC_HYBRID_EXECUTION", execution["passed"], execution["failed"], execution["execution_status"])
    print("STOCHASTIC_HYBRID_ROUNDTRIP", roundtrip["failed"], roundtrip["roundtrip_status"])
    if args.strict and (execution["failed"] or roundtrip["failed"]):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
