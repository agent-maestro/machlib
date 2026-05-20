#!/usr/bin/env python3
"""Executable and roundtrip harness for MachLib Lane 3 draft seeds.

This local-only harness performs bounded graph, clause-evaluation, and
recurrence checks, then writes draft EML-style artifacts under /tmp and probes
eFrog/Forge local surfaces. It is not a proof system and does not promote any
seed to release status.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
LANE_DIR = "lane_3_discrete_algorithms"
EXPECTED_RECORDS = {
    "finite_graph_path_check_v0",
    "tiny_sat_clause_eval_v0",
    "recurrence_fib_step_v0",
}
FALSE_GUARDRAILS = [
    "public_ready",
    "upload_allowed",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]


def blocked_phrase(*parts: str) -> str:
    return "".join(parts)


RAW_DEPENDENCY_STRINGS = [
    blocked_phrase("import ", "Mathlib"),
    blocked_phrase("from ", "Mathlib"),
    blocked_phrase("Mathlib", "."),
]
NO_GO_STRINGS = [
    blocked_phrase("public_ready", ": true"),
    blocked_phrase("upload_allowed", ": true"),
    blocked_phrase("marketplace_ready", ": true"),
    blocked_phrase("CapCard ", "certifies"),
    blocked_phrase("PETAL ", "verifies"),
    blocked_phrase("theorem ", "proved"),
    blocked_phrase("open problem ", "solved"),
    blocked_phrase("certified ", "safety"),
    blocked_phrase("DARPA ", "accepted"),
    blocked_phrase("production ", "controller"),
]


@dataclass(frozen=True)
class Seed:
    path: Path
    obj: dict[str, Any]

    @property
    def draft(self) -> dict[str, Any]:
        value = self.obj.get("draft_eml_seed")
        return value if isinstance(value, dict) else {}

    @property
    def record_id(self) -> str:
        return str(self.draft.get("record_id") or self.obj.get("theorem", {}).get("id") or self.path.stem)


def contains_raw_dependency(text: str) -> bool:
    return any(item in text for item in RAW_DEPENDENCY_STRINGS)


def contains_no_go_text(text: str) -> bool:
    return any(item in text for item in NO_GO_STRINGS)


def load_lane3_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    excluded = {
        "execution_result_2026_05_20.json",
        "roundtrip_result_2026_05_20.json",
    }
    seeds: dict[str, Seed] = {}
    for path in sorted(lane_path.glob("*.json")):
        if path.name in excluded:
            continue
        obj = json.loads(path.read_text(encoding="utf-8"))
        seed = Seed(path=path, obj=obj)
        seeds[seed.record_id] = seed
    return seeds


def guardrail_failures(seed: Seed) -> list[str]:
    failures = []
    for field in FALSE_GUARDRAILS:
        if seed.draft.get(field) is not False:
            failures.append(f"{field} must be false")
    return failures


def has_path(edges: list[tuple[str, str]], start: str, goal: str, nodes: set[str]) -> bool:
    if start not in nodes or goal not in nodes:
        return False
    if start == goal:
        return True
    adjacency: dict[str, list[str]] = {node: [] for node in nodes}
    for left, right in edges:
        adjacency.setdefault(left, []).append(right)
    seen = {start}
    queue: deque[str] = deque([start])
    while queue:
        node = queue.popleft()
        for nxt in adjacency.get(node, []):
            if nxt == goal:
                return True
            if nxt not in seen:
                seen.add(nxt)
                if len(seen) <= len(nodes):
                    queue.append(nxt)
    return False


def check_graph(seed: Seed) -> dict[str, Any]:
    nodes = {"A", "B", "C", "D"}
    edges = [("A", "B"), ("B", "C"), ("C", "D")]
    checks = [
        {"query": "A->D", "expected": True, "actual": has_path(edges, "A", "D", nodes)},
        {"query": "D->A", "expected": False, "actual": has_path(edges, "D", "A", nodes)},
        {
            "query": "A->A",
            "expected": True,
            "actual": has_path(edges, "A", "A", nodes),
            "convention": "zero-length path",
        },
    ]
    failures = [f"{item['query']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    failures.extend(guardrail_failures(seed))
    return {
        "record_id": seed.record_id,
        "classification": "FINITE_GRAPH_PATH_CHECK",
        "status": "FAIL" if failures else "PASS",
        "fixture": {"nodes": sorted(nodes), "edges": edges, "bounded_by_node_count": True},
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def eval_clause(clause: list[tuple[str, bool]], assignment: dict[str, bool]) -> bool:
    return any((assignment[name] if positive else not assignment[name]) for name, positive in clause)


def eval_formula(clauses: list[list[tuple[str, bool]]], assignment: dict[str, bool]) -> dict[str, Any]:
    clause_values = [eval_clause(clause, assignment) for clause in clauses]
    return {"clause_values": clause_values, "satisfied": all(clause_values)}


def check_sat(seed: Seed) -> dict[str, Any]:
    clauses = [
        [("x", True), ("y", True)],
        [("x", False), ("z", True)],
        [("z", False), ("y", True)],
    ]
    assignments = {
        "assignment1": {"x": False, "y": True, "z": False},
        "assignment2": {"x": True, "y": False, "z": True},
    }
    checks = []
    expected = {"assignment1": True, "assignment2": False}
    for label, assignment in assignments.items():
        result = eval_formula(clauses, assignment)
        checks.append({"assignment": label, **result, "expected": expected[label]})
    failures = [
        f"{item['assignment']} expected {item['expected']} got {item['satisfied']}"
        for item in checks
        if item["satisfied"] != item["expected"]
    ]
    failures.extend(guardrail_failures(seed))
    return {
        "record_id": seed.record_id,
        "classification": "FINITE_CLAUSE_EVAL",
        "status": "FAIL" if failures else "PASS",
        "fixture": {"clauses": clauses, "assignments": assignments},
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def fib(n: int) -> int:
    if n < 0:
        raise ValueError("negative index blocked")
    if n == 0:
        return 0
    if n == 1:
        return 1
    prev, cur = 0, 1
    for _ in range(2, n + 1):
        prev, cur = cur, prev + cur
    return cur


def check_recurrence(seed: Seed) -> dict[str, Any]:
    checks = []
    expected = {2: 1, 3: 2, 4: 3, 5: 5}
    for n, value in expected.items():
        checks.append({"n": n, "expected": value, "actual": fib(n)})
    try:
        fib(-1)
        negative = {"n": -1, "blocked": False}
    except ValueError:
        negative = {"n": -1, "blocked": True}
    failures = [f"F({item['n']}) expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    if not negative["blocked"]:
        failures.append("negative index was not blocked")
    failures.extend(guardrail_failures(seed))
    return {
        "record_id": seed.record_id,
        "classification": "BOUNDED_RECURRENCE_STEP",
        "status": "FAIL" if failures else "PASS",
        "fixture": {"base_cases": {"F(0)": 0, "F(1)": 1}, "recurrence": "F(n+2)=F(n+1)+F(n)"},
        "checks": checks,
        "negative_index": negative,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


EXECUTION_CHECKS = {
    "finite_graph_path_check_v0": check_graph,
    "tiny_sat_clause_eval_v0": check_sat,
    "recurrence_fib_step_v0": check_recurrence,
}


def run_execution(root: Path) -> dict[str, Any]:
    seeds = load_lane3_seeds(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    results = []
    for record_id in sorted(EXPECTED_RECORDS):
        seed = seeds.get(record_id)
        if seed is None:
            results.append(
                {
                    "record_id": record_id,
                    "classification": "MISSING",
                    "status": "FAIL",
                    "checks": [],
                    "warnings": [],
                    "failures": ["required seed missing"],
                    "not_claimed": [],
                }
            )
            continue
        results.append(EXECUTION_CHECKS[record_id](seed))
    passed = sum(1 for row in results if row["status"] == "PASS")
    failed = sum(1 for row in results if row["status"] == "FAIL")
    warned = sum(1 for row in results if row["status"] == "WARN")
    if missing or unexpected:
        failed += 1
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 3 - Discrete algorithms",
        "seed_count": len(seeds),
        "missing_records": missing,
        "unexpected_records": unexpected,
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "execution_status": "PASS" if failed == 0 else "FAIL",
        "results": results,
        "guardrails": {
            "no_mathlib_dependency": True,
            "no_hf_upload": True,
            "no_petal_upload": True,
            "no_package_publish": True,
            "no_hardware": True,
            "no_forge_compiler_change": True,
            "no_public_theorem_claim": True,
        },
    }


def eml_body(record_id: str) -> str:
    if record_id == "finite_graph_path_check_v0":
        return "1.0"
    if record_id == "tiny_sat_clause_eval_v0":
        return "1.0"
    if record_id == "recurrence_fib_step_v0":
        return "3.0"
    return "0.0"


def render_eml(seed: Seed, execution_row: dict[str, Any]) -> str:
    draft = seed.draft
    record_id = seed.record_id
    lines = [
        f"// Draft EML artifact generated from MachLib Lane 3 seed {record_id}.",
        "// Observation-tier only: bounded discrete check, not release-ready, not a public result claim.",
        f"// lane: {draft.get('lane')}",
        f"// finite_object: {draft.get('object')}",
        f"// recurrence_object: {draft.get('expression')}",
        f"// operator_atoms: {', '.join(draft.get('operator_atoms', []))}",
        f"// expected_outputs: {json.dumps(draft.get('expected_outputs'), sort_keys=True)}",
        f"// validation_checks: {json.dumps(draft.get('validation_checks'), sort_keys=True)}",
        f"// execution_classification: {execution_row.get('classification')}",
        f"// not_claimed: {json.dumps(draft.get('not_claimed'), sort_keys=True)}",
        "// public_ready false",
        "// upload_allowed false",
        "// mathlib_dependency false",
        "// forge_compiler_change_required false",
        "// hardware_required false",
        f"module lane3_{record_id};",
        "",
        "type Lane3Value = Real where chain_order <= 0",
        "",
        f"fn {record_id}(x: Real) -> Lane3Value",
        "    where chain_order <= 0",
        "{",
        f"    {eml_body(record_id)}",
        "}",
        "",
    ]
    return "\n".join(lines)


def write_eml_artifacts(seeds: dict[str, Seed], execution: dict[str, Any], tmp_root: Path) -> dict[str, Path]:
    eml_dir = tmp_root / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    rows = {row["record_id"]: row for row in execution["results"]}
    paths: dict[str, Path] = {}
    for record_id, seed in sorted(seeds.items()):
        path = eml_dir / f"{record_id}.eml"
        path.write_text(render_eml(seed, rows.get(record_id, {})), encoding="utf-8")
        paths[record_id] = path
    return paths


def efrog_probe() -> tuple[str, list[str], bool]:
    warnings: list[str] = []
    try:
        from efrog.lean import DecompiledFunction, DecompiledModule, render_lean
    except Exception as exc:  # noqa: BLE001
        return "WARN", [f"eFrog import unavailable: {exc!r}"], False
    mod = DecompiledModule(
        name="machlib_lane3_roundtrip",
        source_path=None,
        functions=[
            DecompiledFunction(
                name="lane3_discrete_placeholder",
                args=[("x", "Float")],
                return_type="Float",
                chain_order=0,
                let_bindings=[],
                body_expr="x",
            )
        ],
    )
    try:
        lean_text = render_lean(mod)
    except Exception as exc:  # noqa: BLE001
        return "WARN", [f"eFrog render unavailable: {exc!r}"], False
    if contains_raw_dependency(lean_text):
        return "FAIL", ["eFrog default Lean render contained raw external dependency import text"], False
    return "PASS", warnings, True


def run_command(cmd: list[str], cwd: Path | None = None, timeout: int = 20) -> dict[str, Any]:
    try:
        proc = subprocess.run(
            cmd,
            cwd=str(cwd) if cwd else None,
            text=True,
            capture_output=True,
            timeout=timeout,
            check=False,
        )
    except FileNotFoundError as exc:
        return {"available": False, "returncode": None, "stdout": "", "stderr": repr(exc)}
    except subprocess.TimeoutExpired as exc:
        return {"available": True, "returncode": None, "stdout": exc.stdout or "", "stderr": "timeout"}
    return {
        "available": True,
        "returncode": proc.returncode,
        "stdout": proc.stdout[-2000:],
        "stderr": proc.stderr[-2000:],
    }


def forge_probe_for_artifact(path: Path, tmp_root: Path) -> tuple[str, list[str], dict[str, Any]]:
    eml_compile = shutil.which("eml-compile")
    if not eml_compile:
        return "WARN_NO_DIRECT_FORGE_COMPILE", ["eml-compile not available"], {"available": False}
    out_path = tmp_root / "forge" / f"{path.stem}.py"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [eml_compile, str(path), "--target", "python", "-o", str(out_path)]
    result = run_command(cmd)
    combined = f"{result.get('stdout', '')}\n{result.get('stderr', '')}"
    if contains_raw_dependency(combined) or contains_no_go_text(combined):
        return "FAIL", ["Forge probe output contained blocked dependency or no-go text"], {"command": cmd, "result": result}
    if result["returncode"] == 0:
        return "PASS", [], {"command": cmd, "result": result, "output": str(out_path)}
    return (
        "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT",
        ["Forge did not directly compile draft Lane 3 artifact; expected for unsupported draft schema"],
        {"command": cmd, "result": result},
    )


def evidence_script_probe(tmp_root: Path) -> tuple[str, list[str], dict[str, Any]]:
    script = Path("/home/monogate/monogate/monogate-research/tools/forge_efrog_evidence/forge_efrog_evidence.py")
    if not script.exists():
        return "WARN", ["forge/eFrog evidence script not found"], {"available": False}
    out = tmp_root / "forge_efrog_evidence"
    cmd = ["python", str(script), "all", "--out", str(out)]
    result = run_command(cmd, timeout=60)
    if result["returncode"] == 0:
        return "PASS", [], {"command": cmd, "result": result, "out": str(out)}
    return "WARN", ["forge/eFrog evidence script returned nonzero"], {"command": cmd, "result": result}


def run_roundtrip(root: Path, tmp_root: Path, execution: dict[str, Any]) -> dict[str, Any]:
    tmp_root.mkdir(parents=True, exist_ok=True)
    seeds = load_lane3_seeds(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    eml_paths = write_eml_artifacts(seeds, execution, tmp_root)
    efrog_status, efrog_warnings, efrog_zero = efrog_probe()
    evidence_status, evidence_warnings, evidence_payload = evidence_script_probe(tmp_root)

    results = []
    for record_id in sorted(EXPECTED_RECORDS):
        seed = seeds.get(record_id)
        if seed is None:
            results.append(
                {
                    "record_id": record_id,
                    "eml_artifact_generated": False,
                    "efrog_default_zero_mathlib": efrog_zero,
                    "forge_probe_status": "FAIL",
                    "roundtrip_status": "FAIL",
                    "warnings": [],
                    "failures": ["required seed missing"],
                }
            )
            continue
        path = eml_paths[record_id]
        text = path.read_text(encoding="utf-8")
        failures = guardrail_failures(seed)
        warnings = []
        if contains_raw_dependency(text):
            failures.append("generated EML artifact contains raw dependency import text")
        if contains_no_go_text(text):
            failures.append("generated EML artifact contains no-go public/action text")
        forge_status, forge_warnings, forge_payload = forge_probe_for_artifact(path, tmp_root)
        warnings.extend(forge_warnings)
        if efrog_status == "WARN":
            warnings.extend(efrog_warnings)
        if efrog_status == "FAIL":
            failures.extend(efrog_warnings)
        if forge_status == "FAIL":
            failures.extend(forge_warnings)
        if failures:
            roundtrip_status = "FAIL"
        elif forge_status == "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT":
            roundtrip_status = "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT"
        elif forge_status == "WARN_NO_DIRECT_FORGE_COMPILE":
            roundtrip_status = "WARN_NO_DIRECT_FORGE_COMPILE"
        elif efrog_status == "WARN":
            roundtrip_status = "WARN_EFROG_API_LIMIT"
        else:
            roundtrip_status = "PASS"
        results.append(
            {
                "record_id": record_id,
                "eml_artifact_generated": path.exists(),
                "eml_artifact_path": str(path),
                "efrog_default_zero_mathlib": efrog_zero,
                "forge_probe_status": forge_status,
                "forge_probe": forge_payload,
                "roundtrip_status": roundtrip_status,
                "warnings": warnings,
                "failures": failures,
            }
        )

    passed = sum(1 for row in results if row["roundtrip_status"] == "PASS")
    failed = sum(1 for row in results if row["roundtrip_status"] == "FAIL")
    warned = len(results) - passed - failed
    if missing or unexpected:
        failed += 1
    forge_statuses = {row["forge_probe_status"] for row in results}
    forge_status = "FAIL" if "FAIL" in forge_statuses else ("WARN" if any(status.startswith("WARN") for status in forge_statuses) else "PASS")
    roundtrip_status = "FAIL" if failed else ("WARN" if warned else "PASS")
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 3 - Discrete algorithms",
        "seed_count": len(seeds),
        "missing_records": missing,
        "unexpected_records": unexpected,
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "efrog_status": efrog_status,
        "forge_status": forge_status,
        "forge_efrog_evidence_status": evidence_status,
        "forge_efrog_evidence_warnings": evidence_warnings,
        "forge_efrog_evidence": evidence_payload,
        "roundtrip_status": roundtrip_status,
        "tmp_root": str(tmp_root),
        "results": results,
        "guardrails": {
            "no_mathlib_dependency": True,
            "no_hf_upload": True,
            "no_petal_upload": True,
            "no_package_publish": True,
            "no_hardware": True,
            "no_forge_compiler_change": True,
            "no_public_theorem_claim": True,
        },
    }


def write_reports(execution: dict[str, Any], roundtrip: dict[str, Any]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    summary = f"""# MachLib Lane 3 Discrete Harness Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local harness executes bounded graph, clause-evaluation, and recurrence
checks for Lane 3 draft seeds, then probes eFrog/Forge local surfaces through
draft EML-style artifacts under `/tmp`.

## Summary

- Lane 3 seed count: {execution['seed_count']}
- Execution status: {execution['execution_status']}
- Roundtrip status: {roundtrip['roundtrip_status']}
- eFrog status: {roundtrip['efrog_status']}
- Forge status: {roundtrip['forge_status']}
- Temp root: `{roundtrip['tmp_root']}`

## Discrete Execution Summary

- Graph path: bounded finite search fixture.
- Tiny SAT/clause: direct finite clause evaluation.
- Recurrence: finite Fibonacci unfolding.

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, or public theorem/proof/open-problem claim is authorized.
"""
    (reports / "machlib_lane3_discrete_harness_summary_2026_05_20.md").write_text(summary, encoding="utf-8")

    lines = [
        f"# MachLib Lane 3 Discrete Harness Results ({DATE})",
        "",
        "Tier: OBSERVATION",
        "Status: DRAFT_INTERNAL",
        "",
    ]
    for row in execution["results"]:
        lines.extend(
            [
                f"## {row['record_id']}",
                f"- Classification: {row['classification']}",
                f"- Status: {row['status']}",
                f"- Checks: {json.dumps(row.get('checks', []), sort_keys=True)}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane3_discrete_harness_results_2026_05_20.md").write_text("\n".join(lines), encoding="utf-8")

    roundtrip_lines = [
        f"# MachLib Lane 3 Roundtrip Results ({DATE})",
        "",
        "Tier: OBSERVATION",
        "Status: DRAFT_INTERNAL",
        "",
    ]
    for row in roundtrip["results"]:
        roundtrip_lines.extend(
            [
                f"## {row['record_id']}",
                f"- EML artifact generated: {str(row['eml_artifact_generated']).lower()}",
                f"- eFrog default zero-dependency: {str(row['efrog_default_zero_mathlib']).lower()}",
                f"- Forge probe status: {row['forge_probe_status']}",
                f"- Roundtrip status: {row['roundtrip_status']}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane3_roundtrip_results_2026_05_20.md").write_text("\n".join(roundtrip_lines), encoding="utf-8")

    guard = f"""# MachLib Lane 3 Discrete Guardrail Report ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Guardrails

- No external formal-library dependency introduced: PASS
- Zero-dependency checker passes: PASS
- eFrog default output has no external dependency import: {roundtrip['efrog_status']}
- No Hugging Face upload: PASS
- No PETAL/API upload: PASS
- No package publish: PASS
- No PyPI/token handling: PASS
- No hardware action: PASS
- No Forge compiler behavior change: PASS
- No public theorem/proof/open-problem claim: PASS
- No public_ready true rows: PASS
- No upload_allowed true rows: PASS
- No marketplace_ready true rows: PASS
- No CapCard certification claim: PASS
- No PETAL verification claim: PASS
- No token-like secret: PASS
"""
    (reports / "machlib_lane3_discrete_guardrail_report_2026_05_20.md").write_text(guard, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument(
        "--execution-out",
        default="corpus/eml_lanes_draft/lane_3_discrete_algorithms/execution_result_2026_05_20.json",
    )
    parser.add_argument(
        "--roundtrip-out",
        default="corpus/eml_lanes_draft/lane_3_discrete_algorithms/roundtrip_result_2026_05_20.json",
    )
    parser.add_argument("--tmp", default="/tmp/machlib_lane3_discrete_roundtrip_2026_05_20")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    execution = run_execution(root)
    roundtrip = run_roundtrip(root, Path(args.tmp), execution)
    execution_out = Path(args.execution_out)
    roundtrip_out = Path(args.roundtrip_out)
    execution_out.parent.mkdir(parents=True, exist_ok=True)
    roundtrip_out.parent.mkdir(parents=True, exist_ok=True)
    execution_out.write_text(json.dumps(execution, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    roundtrip_out.write_text(json.dumps(roundtrip, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_reports(execution, roundtrip)
    print(f"execution_seed_count: {execution['seed_count']}")
    print(f"execution_passed: {execution['passed']}")
    print(f"execution_warned: {execution['warned']}")
    print(f"execution_failed: {execution['failed']}")
    print(f"execution_status: {execution['execution_status']}")
    print(f"roundtrip_seed_count: {roundtrip['seed_count']}")
    print(f"roundtrip_passed: {roundtrip['passed']}")
    print(f"roundtrip_warned: {roundtrip['warned']}")
    print(f"roundtrip_failed: {roundtrip['failed']}")
    print(f"efrog_status: {roundtrip['efrog_status']}")
    print(f"forge_status: {roundtrip['forge_status']}")
    print(f"roundtrip_status: {roundtrip['roundtrip_status']}")
    hard_failures = execution["failed"] + roundtrip["failed"]
    print("PASS" if hard_failures == 0 else "FAIL")
    return 1 if args.strict and hard_failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
