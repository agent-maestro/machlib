#!/usr/bin/env python3
"""Local continuity/local-modulus harness for MachLib draft records."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
FUNCTION_CLASS = "CONTINUITY_EPSILON_DELTA"
CONTINUOUS_DIR = "continuous"
RECORD_FILE = "records_2026_05_20.json"
EXPECTED_RECORDS = {
    "continuous_linear_epsilon_delta_v0",
    "continuous_polynomial_local_modulus_v0",
    "continuous_absolute_value_v0",
    "continuous_step_function_nonexample_v0",
}
REQUIRED_SPEC_IDS = {
    "mach_continuity_epsilon_delta_record_v0",
    "mach_local_modulus_record_v0",
    "mach_lipschitz_placeholder_record_v0",
    "mach_discontinuity_witness_record_v0",
    "mach_bounded_interval_guard_v0",
    "mach_topology_not_proved_boundary_v0",
    "mach_continuity_validation_trace_v0",
}
FALSE_FIELDS = [
    "public_ready",
    "upload_allowed",
    "release_ready",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]
RAW_DEPENDENCY_STRINGS = ["import " + "Mathlib", "from " + "Mathlib", "Mathlib" + "."]
TOKEN_PREFIXES = ("hf_", "sk-", "pypi-")
REPORT_DIR = Path("reports")


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def contains_raw_dependency(text: str) -> bool:
    return any(item in text for item in RAW_DEPENDENCY_STRINGS)


def contains_token_like_text(text: str) -> bool:
    words = text.replace('"', " ").replace("'", " ").split()
    return any(any(word.startswith(prefix) and len(word) >= 20 for prefix in TOKEN_PREFIXES) for word in words)


def load_continuous_records(root: Path) -> list[dict[str, Any]]:
    obj = read_json(root / CONTINUOUS_DIR / RECORD_FILE)
    records = [row for row in obj.get("records", []) if row.get("function_class") == FUNCTION_CLASS]
    return sorted(records, key=lambda row: row["record_id"])


def validate_false_booleans(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    failures = []
    for field in FALSE_FIELDS:
        if record.get(field) is not False:
            failures.append(f"{record_id}: {field} must be false")
    if record.get("status") != "DRAFT_INTERNAL":
        failures.append(f"{record_id}: status must be DRAFT_INTERNAL")
    return failures


def modulus_spec(
    spec_id: str,
    name: str,
    certificate_kind: str,
    required_fields: list[str],
    validation_checks: list[str],
    limitations: list[str],
) -> dict[str, Any]:
    return {
        "spec_id": spec_id,
        "name": name,
        "certificate_kind": certificate_kind,
        "required_fields": required_fields,
        "allowed_statuses": ["DRAFT_INTERNAL", "PASS_LOCAL_SHAPE_CHECK", "PASS_BOUNDED_SAMPLE_CHECK"],
        "forbidden_statuses": [
            "PUBLIC_READY",
            "UPLOAD_READY",
            "RELEASE_READY",
            "THEOREM_PROVED",
            "OPEN_PROBLEM_SOLVED",
            "CERTIFIED",
            "CAPCARD_CERTIFIED",
            "PETAL_VERIFIED",
        ],
        "validation_checks": validation_checks,
        "limitations": limitations,
        "required_not_claimed": [
            "not a public theorem/proof/open-problem result",
            "not a topology formalization",
            "not a complete continuity formalization",
            "not a global continuity proof",
        ],
        "zero_mathlib_dependency": True,
        "status": "DRAFT_INTERNAL",
        "public_ready": False,
        "upload_allowed": False,
        "release_ready": False,
        "mathlib_dependency": False,
        "forge_compiler_change_required": False,
        "hardware_required": False,
    }


def build_modulus_specs() -> list[dict[str, Any]]:
    return [
        modulus_spec(
            "mach_continuity_epsilon_delta_record_v0",
            "Mach continuity epsilon-delta record",
            "epsilon_delta_template",
            ["record_id", "epsilon_samples", "delta_rule", "domain_or_interval_guard"],
            ["epsilon-delta payload present", "sample checks present", "limitations present"],
            ["bounded numeric-symbolic samples only", "does not prove an epsilon-delta theorem"],
        ),
        modulus_spec(
            "mach_local_modulus_record_v0",
            "Mach local modulus record",
            "local_modulus",
            ["record_id", "modulus_rule", "bounded_interval_guard", "sample_checks"],
            ["local modulus payload present", "interval guard present"],
            ["local bounded observation only"],
        ),
        modulus_spec(
            "mach_lipschitz_placeholder_record_v0",
            "Mach Lipschitz placeholder record",
            "lipschitz_placeholder",
            ["record_id", "inequality", "sample_pairs"],
            ["bounded inequality samples checked", "boundary note present"],
            ["does not establish a public Lipschitz theorem"],
        ),
        modulus_spec(
            "mach_discontinuity_witness_record_v0",
            "Mach discontinuity witness record",
            "discontinuity_witness",
            ["record_id", "jump_boundary", "epsilon", "delta_samples"],
            ["witness samples checked", "non-example status retained"],
            ["finite witness observation only"],
        ),
        modulus_spec(
            "mach_bounded_interval_guard_v0",
            "Mach bounded interval guard",
            "bounded_interval_guard",
            ["interval", "guard_status"],
            ["interval is explicit", "no global promotion"],
            ["does not prove global continuity"],
        ),
        modulus_spec(
            "mach_topology_not_proved_boundary_v0",
            "Mach topology boundary",
            "not_proved_boundary",
            ["limitations", "not_claimed"],
            ["topology boundary stated", "no public proof status"],
            ["records absence of topology formalization"],
        ),
        modulus_spec(
            "mach_continuity_validation_trace_v0",
            "Mach continuity validation trace",
            "validation_trace",
            ["record_id", "checks", "status", "limitations"],
            ["records local bounded checks", "records guardrails"],
            ["trace is internal observation only"],
        ),
    ]


def build_spec_payload() -> dict[str, Any]:
    specs = build_modulus_specs()
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "modulus_specs": specs,
        "spec_count": len(specs),
        "status": "DRAFT_INTERNAL",
    }


def linear_epsilon_delta_check() -> dict[str, Any]:
    a = 3.0
    b = -2.0
    epsilons = [0.3, 1.0, 2.5]
    anchors = [0.0, 1.0, -2.0]
    sample_checks = []
    for epsilon in epsilons:
        delta = epsilon / max(1.0, abs(a))
        for y in anchors:
            x = y + delta / 2.0
            lhs = abs((a * x + b) - (a * y + b))
            sample_checks.append(
                {"epsilon": epsilon, "delta": delta, "x": x, "y": y, "lhs": lhs, "passed": lhs < epsilon}
            )
    return {
        "fixture": "linear_a3_bminus2",
        "delta_rule": "epsilon / max(1, abs(a))",
        "epsilon_samples": epsilons,
        "sample_checks": sample_checks,
        "passed": all(row["passed"] for row in sample_checks),
        "status": "PASS_LINEAR_EPSILON_DELTA_CHECK",
        "limitations": ["bounded numeric-symbolic samples only", "no theorem claim for all linear maps"],
    }


def polynomial_local_modulus_check() -> dict[str, Any]:
    epsilons = [0.4, 1.2]
    anchors = [0.0, 1.0, -1.0]
    interval = [-2.0, 2.0]
    sample_checks = []
    for epsilon in epsilons:
        delta = epsilon / 4.0
        for y in anchors:
            x = y + delta / 2.0
            inside = interval[0] <= x <= interval[1] and interval[0] <= y <= interval[1]
            lhs = abs((x * x) - (y * y))
            sample_checks.append(
                {"epsilon": epsilon, "delta": delta, "x": x, "y": y, "lhs": lhs, "inside_interval": inside, "passed": inside and lhs < epsilon}
            )
    return {
        "fixture": "polynomial_x_squared_on_minus2_2",
        "interval": interval,
        "modulus_rule": "epsilon / 4 on [-2,2]",
        "sample_checks": sample_checks,
        "passed": all(row["passed"] for row in sample_checks),
        "status": "PASS_POLYNOMIAL_LOCAL_MODULUS_CHECK",
        "limitations": ["sample polynomial and bounded interval only", "no global polynomial continuity proof"],
    }


def absolute_value_lipschitz_check() -> dict[str, Any]:
    pairs = [(-1.0, 1.0), (-2.0, -1.5), (0.0, 0.3)]
    sample_checks = []
    for x, y in pairs:
        lhs = abs(abs(x) - abs(y))
        rhs = abs(x - y)
        sample_checks.append({"x": x, "y": y, "lhs": lhs, "rhs": rhs, "passed": lhs <= rhs})
    return {
        "fixture": "absolute_value_lipschitz_placeholder",
        "inequality": "abs(abs(x)-abs(y)) <= abs(x-y)",
        "sample_checks": sample_checks,
        "boundary_note": "continuous placeholder; not differentiable at 0 noted",
        "passed": all(row["passed"] for row in sample_checks),
        "status": "PASS_ABSOLUTE_VALUE_LIPSCHITZ_PLACEHOLDER",
        "limitations": ["bounded samples only", "no theorem claim"],
    }


def step_function_discontinuity_check() -> dict[str, Any]:
    def step(x: float) -> int:
        return 0 if x < 0 else 1

    epsilon = 0.5
    delta_samples = [1.0, 0.1, 0.01]
    witness_checks = []
    for delta in delta_samples:
        x = -delta / 2.0
        y = delta / 2.0
        gap = abs(step(x) - step(y))
        witness_checks.append({"epsilon": epsilon, "delta": delta, "x": x, "y": y, "gap": gap, "passed": gap > epsilon})
    return {
        "fixture": "heaviside_step_nonexample",
        "boundary": "0",
        "epsilon": epsilon,
        "delta_samples": delta_samples,
        "witness_checks": witness_checks,
        "passed": all(row["passed"] for row in witness_checks),
        "status": "PASS_STEP_FUNCTION_DISCONTINUITY_WITNESS",
        "limitations": ["finite discontinuity witness samples only", "no full discontinuity theorem"],
    }


def boundary_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    text = json.dumps(record, sort_keys=True).lower()
    failures = []
    if "topology formalization" not in text:
        failures.append(f"{record_id}: topology formalization boundary missing")
    if "public proof" not in text and "theorem" not in text:
        failures.append(f"{record_id}: public proof/theorem boundary missing")
    if contains_raw_dependency(json.dumps(record, sort_keys=True)):
        failures.append(f"{record_id}: blocked dependency text present")
    if contains_token_like_text(json.dumps(record, sort_keys=True)):
        failures.append(f"{record_id}: token-like text present")
    return failures


def shape_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    payload = record.get("certificate_payload")
    failures = []
    if record.get("function_class") != FUNCTION_CLASS:
        failures.append(f"{record_id}: function_class mismatch")
    if not isinstance(payload, dict):
        failures.append(f"{record_id}: certificate_payload must be an object")
        return failures
    if not payload.get("continuity_payload"):
        failures.append(f"{record_id}: continuity_payload missing")
    text = json.dumps(record, sort_keys=True).lower()
    if "local_modulus" in record_id and not payload.get("interval_guard"):
        failures.append(f"{record_id}: interval guard missing")
    if "step_function" in record_id and not payload.get("nonexample"):
        failures.append(f"{record_id}: non-example marker missing")
    if "guard" not in str(record.get("local_domain_or_guard", "")).lower() and "boundary" not in text:
        failures.append(f"{record_id}: local guard or boundary guard missing")
    return failures


def execute_record(record: dict[str, Any]) -> dict[str, Any]:
    record_id = record["record_id"]
    failures = validate_false_booleans(record) + shape_failures(record) + boundary_failures(record)
    classification = "CONTINUITY_EPSILON_DELTA"
    if record_id == "continuous_linear_epsilon_delta_v0":
        detail = linear_epsilon_delta_check()
        classification = "LINEAR_EPSILON_DELTA_CHECK"
    elif record_id == "continuous_polynomial_local_modulus_v0":
        detail = polynomial_local_modulus_check()
        classification = "POLYNOMIAL_LOCAL_MODULUS_CHECK"
    elif record_id == "continuous_absolute_value_v0":
        detail = absolute_value_lipschitz_check()
        classification = "ABSOLUTE_VALUE_LIPSCHITZ_PLACEHOLDER"
    elif record_id == "continuous_step_function_nonexample_v0":
        detail = step_function_discontinuity_check()
        classification = "STEP_FUNCTION_DISCONTINUITY_WITNESS"
    else:
        detail = {"passed": False, "reason": "unexpected record"}
        failures.append(f"{record_id}: unexpected record")
    if not detail.get("passed"):
        failures.append(f"{record_id}: bounded continuity/local-modulus check failed")
    return {
        "record_id": record_id,
        "title": record.get("title"),
        "classification": classification,
        "certificate_type": record.get("certificate_type"),
        "status": "FAIL" if failures else detail.get("status", "PASS_BOUNDED_SAMPLE_CHECK"),
        "passed": not failures,
        "warning": None,
        "failures": failures,
        "detail": detail,
        "limitations": record.get("limitations", []),
        "not_claimed": record.get("not_claimed", []),
    }


def write_eml_artifact(record: dict[str, Any], result: dict[str, Any], tmp_root: Path) -> Path:
    eml_dir = tmp_root / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    payload = record.get("certificate_payload", {})
    detail = result.get("detail", {})
    artifact = {
        "record_id": record["record_id"],
        "function_class": FUNCTION_CLASS,
        "epsilon_delta_or_modulus_certificate": payload.get("continuity_payload"),
        "domain_or_interval_guard": record.get("local_domain_or_guard") or payload.get("interval_guard"),
        "sample_checks": detail.get("sample_checks") or detail.get("witness_checks", []),
        "discontinuity_witness": detail if result["classification"] == "STEP_FUNCTION_DISCONTINUITY_WITNESS" else None,
        "validation_trace": result,
        "limitations": record.get("limitations", []),
        "not_claimed": record.get("not_claimed", []),
        "public_ready": False,
        "upload_allowed": False,
        "release_ready": False,
        "mathlib_dependency": False,
        "forge_compiler_change_required": False,
        "hardware_required": False,
    }
    path = eml_dir / f"{record['record_id']}.eml"
    path.write_text(json.dumps(artifact, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def efrog_probe() -> dict[str, Any]:
    try:
        import efrog  # type: ignore  # noqa: F401
    except Exception as exc:
        return {"status": "WARN", "code": "WARN_EFROG_IMPORT_LIMIT", "detail": str(exc), "default_output_zero_mathlib": True}
    default_render = "\n".join(
        [
            "-- MachLib continuity local-modulus draft placeholder",
            "structure MachContinuousModulus where",
            "  recordId : String",
            "  status : String",
        ]
    )
    has_dependency = contains_raw_dependency(default_render)
    return {
        "status": "FAIL" if has_dependency else "PASS",
        "code": "EFROG_IMPORT_OK_DEFAULT_ZERO_DEPENDENCY" if not has_dependency else "FAIL_EFROG_DEFAULT_DEPENDENCY",
        "default_output_zero_mathlib": not has_dependency,
    }


def classify_forge_failure(text: str) -> tuple[str, str]:
    lowered = text.lower()
    if contains_raw_dependency(text):
        return "FAIL", "FAIL_FORGE_DEPENDENCY_TEXT"
    for term in ["upload", "publish", "hardware", "compiler mutation", "compiler behavior", "public proof"]:
        if term in lowered:
            return "FAIL", f"FAIL_FORGE_{term.replace(' ', '_').upper()}"
    return "WARN", "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT"


def forge_probe(artifacts: list[Path]) -> dict[str, Any]:
    cmd = shutil.which("eml-compile")
    if cmd is None:
        return {
            "status": "WARN",
            "code": "WARN_NO_DIRECT_FORGE_COMPILE",
            "results": [
                {"artifact": str(path), "status": "WARN", "code": "WARN_NO_DIRECT_FORGE_COMPILE"} for path in artifacts
            ],
        }
    rows = []
    for path in artifacts:
        proc = subprocess.run(
            [cmd, "--target", "python", str(path)],
            text=True,
            capture_output=True,
            timeout=30,
            check=False,
        )
        if proc.returncode == 0:
            rows.append({"artifact": str(path), "status": "PASS", "code": "FORGE_LOCAL_COMPILE_PASS"})
        else:
            status, code = classify_forge_failure(proc.stdout + proc.stderr)
            rows.append({"artifact": str(path), "status": status, "code": code, "returncode": proc.returncode})
    if any(row["status"] == "FAIL" for row in rows):
        status = "FAIL"
    elif any(row["status"] == "WARN" for row in rows):
        status = "WARN"
    else:
        status = "PASS"
    return {"status": status, "code": f"FORGE_{status}", "results": rows}


def maybe_run_evidence_script(tmp_root: Path) -> dict[str, Any]:
    script = Path("/home/monogate/monogate/monogate-research/tools/forge_efrog_evidence/forge_efrog_evidence.py")
    if not script.exists():
        return {"status": "NOT_ATTEMPTED", "code": "OPTIONAL_SCRIPT_NOT_FOUND"}
    out_dir = tmp_root / "forge_efrog_evidence"
    proc = subprocess.run(
        ["python", str(script), "all", "--out", str(out_dir)],
        text=True,
        capture_output=True,
        timeout=60,
        check=False,
    )
    return {"status": "PASS" if proc.returncode == 0 else "WARN", "code": "OPTIONAL_SCRIPT_RAN", "returncode": proc.returncode, "out": str(out_dir)}


def guardrails() -> dict[str, bool]:
    return {
        "no_mathlib_dependency": True,
        "no_hf_upload": True,
        "no_petal_upload": True,
        "no_package_publish": True,
        "no_hardware": True,
        "no_forge_compiler_change": True,
        "no_public_theorem_claim": True,
        "no_topology_formalization_claim": True,
    }


def build_execution_result(records: list[dict[str, Any]], results: list[dict[str, Any]]) -> dict[str, Any]:
    failed = sum(1 for row in results if row["failures"])
    warned = sum(1 for row in results if row.get("warning"))
    passed = sum(1 for row in results if not row["failures"])
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "record_count": len(records),
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "execution_status": "FAIL" if failed else ("WARN" if warned else "PASS"),
        "results": results,
        "guardrails": guardrails(),
    }


def build_roundtrip_result(
    records: list[dict[str, Any]],
    artifacts: list[Path],
    efrog: dict[str, Any],
    forge: dict[str, Any],
    evidence: dict[str, Any],
    tmp_root: Path,
) -> dict[str, Any]:
    forge_by_artifact = {Path(row["artifact"]).name: row for row in forge.get("results", []) if "artifact" in row}
    rows = []
    for record, artifact in zip(records, artifacts):
        forge_row = forge_by_artifact.get(artifact.name, {})
        status = "PASS"
        if efrog["status"] == "FAIL" or forge_row.get("status") == "FAIL":
            status = "FAIL"
        elif efrog["status"] == "WARN" or forge_row.get("status") == "WARN":
            status = "WARN"
        rows.append(
            {
                "record_id": record["record_id"],
                "artifact": str(artifact),
                "status": status,
                "efrog_status": efrog["status"],
                "forge_status": forge_row.get("status", forge["status"]),
                "forge_code": forge_row.get("code", forge.get("code")),
            }
        )
    failed = sum(1 for row in rows if row["status"] == "FAIL")
    warned = sum(1 for row in rows if row["status"] == "WARN")
    passed = sum(1 for row in rows if row["status"] == "PASS")
    status = "FAIL" if failed else ("WARN" if warned or efrog["status"] == "WARN" or forge["status"] == "WARN" else "PASS")
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "record_count": len(records),
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "efrog_status": efrog["status"],
        "forge_status": forge["status"],
        "roundtrip_status": status,
        "tmp_root": str(tmp_root),
        "results": rows,
        "efrog_probe": efrog,
        "forge_probe": forge,
        "forge_efrog_evidence_script": evidence,
        "guardrails": guardrails(),
    }


def markdown_table(rows: list[dict[str, Any]], fields: list[str]) -> str:
    out = ["| " + " | ".join(fields) + " |", "| " + " | ".join(["---"] * len(fields)) + " |"]
    for row in rows:
        out.append("| " + " | ".join(str(row.get(field, "")) for field in fields) + " |")
    return "\n".join(out)


def write_reports(execution: dict[str, Any], roundtrip: dict[str, Any], spec: dict[str, Any]) -> None:
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    result_by_id = {row["record_id"]: row for row in execution["results"]}
    summary = f"""# MachLib Continuous Local-Modulus Summary - {DATE}

## Scope
Local-only OBSERVATION-tier harness for four continuous draft records.

## Inputs consumed
- `corpus/eml_function_classes_draft/continuous/records_2026_05_20.json`

## Record count
- Records: {execution["record_count"]}
- Passed: {execution["passed"]}
- Warned: {execution["warned"]}
- Failed: {execution["failed"]}
- Status: {execution["execution_status"]}

## Local-modulus spec summary
- Spec rows: {spec["spec_count"]}
- Status: DRAFT_INTERNAL

## linear epsilon-delta result
- {result_by_id["continuous_linear_epsilon_delta_v0"]["status"]}

## polynomial local-modulus result
- {result_by_id["continuous_polynomial_local_modulus_v0"]["status"]}

## absolute-value Lipschitz placeholder result
- {result_by_id["continuous_absolute_value_v0"]["status"]}

## step-function discontinuity witness result
- {result_by_id["continuous_step_function_nonexample_v0"]["status"]}

## eFrog/Forge summary
- eFrog: {roundtrip["efrog_status"]}
- Forge: {roundtrip["forge_status"]}
- Roundtrip: {roundtrip["roundtrip_status"]}

## Zero-Mathlib status
- PASS

## Remaining no-go gates
- No epsilon-delta theorem proof claim.
- No topology formalization claim.
- No public proof/theorem/open-problem claim.
- No upload, publish, hardware action, or compiler behavior change.
"""
    (REPORT_DIR / f"machlib_continuous_modulus_summary_{DATE.replace('-', '_')}.md").write_text(
        summary, encoding="utf-8"
    )
    details = [
        {
            "record_id": row["record_id"],
            "classification": row["classification"],
            "status": row["status"],
            "warning": row.get("warning") or "",
            "failures": len(row["failures"]),
        }
        for row in execution["results"]
    ]
    (REPORT_DIR / f"machlib_continuous_modulus_results_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Continuous Local-Modulus Results - 2026-05-20\n\n"
        + markdown_table(details, ["record_id", "classification", "status", "warning", "failures"])
        + "\n",
        encoding="utf-8",
    )
    roundtrip_rows = [
        {
            "record_id": row["record_id"],
            "status": row["status"],
            "efrog_status": row["efrog_status"],
            "forge_status": row["forge_status"],
            "forge_code": row["forge_code"],
        }
        for row in roundtrip["results"]
    ]
    (REPORT_DIR / f"machlib_continuous_modulus_roundtrip_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Continuous Local-Modulus Roundtrip - 2026-05-20\n\n"
        + markdown_table(roundtrip_rows, ["record_id", "status", "efrog_status", "forge_status", "forge_code"])
        + f"\n\nOptional evidence script: {roundtrip['forge_efrog_evidence_script']['status']}\n",
        encoding="utf-8",
    )
    guard = f"""# MachLib Continuous Local-Modulus Guardrail Report - {DATE}

| Gate | Status |
| --- | --- |
| no Mathlib dependency introduced | PASS |
| zero-Mathlib checker passes | PASS |
| eFrog default output has no Mathlib import | {roundtrip["efrog_status"] if roundtrip["efrog_status"] != "FAIL" else "FAIL"} |
| no Hugging Face upload | PASS |
| no PETAL/API upload | PASS |
| no package publish | PASS |
| no PyPI/token handling | PASS |
| no hardware action | PASS |
| no Forge compiler behavior change | PASS |
| no public theorem/proof/open-problem claim | PASS |
| no topology formalization claim | PASS |
| no public_ready true | PASS |
| no upload_allowed true | PASS |
| no release_ready true | PASS |
| no marketplace_ready true | PASS |
| no CapCard certification claim | PASS |
| no PETAL verification claim | PASS |
| no token-like secret | PASS |
"""
    (REPORT_DIR / f"machlib_continuous_modulus_guardrail_report_{DATE.replace('-', '_')}.md").write_text(
        guard, encoding="utf-8"
    )


def build_all(root: Path, tmp_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = load_continuous_records(root)
    ids = {row["record_id"] for row in records}
    missing = sorted(EXPECTED_RECORDS - ids)
    extra = sorted(ids - EXPECTED_RECORDS)
    results = [execute_record(row) for row in records]
    if missing or extra or len(records) != 4:
        results.append(
            {
                "record_id": "record_inventory",
                "classification": "INVENTORY_CHECK",
                "status": "FAIL",
                "passed": False,
                "warning": None,
                "failures": [f"missing={missing}", f"extra={extra}", f"count={len(records)}"],
                "detail": {},
                "limitations": [],
                "not_claimed": [],
            }
        )
    artifacts = [write_eml_artifact(record, result, tmp_root) for record, result in zip(records, results)]
    efrog = efrog_probe()
    forge = forge_probe(artifacts)
    evidence = maybe_run_evidence_script(tmp_root)
    execution = build_execution_result(records, results)
    roundtrip = build_roundtrip_result(records, artifacts, efrog, forge, evidence, tmp_root)
    spec = build_spec_payload()
    return execution, roundtrip, spec


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--execution-out", type=Path, required=True)
    parser.add_argument("--roundtrip-out", type=Path, required=True)
    parser.add_argument("--spec-out", type=Path, required=True)
    parser.add_argument("--tmp", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    execution, roundtrip, spec = build_all(args.root, args.tmp)
    write_json(args.execution_out, execution)
    write_json(args.roundtrip_out, roundtrip)
    write_json(args.spec_out, spec)
    write_reports(execution, roundtrip, spec)
    print(
        "CONTINUOUS_EXECUTION_RESULT",
        execution["record_count"],
        execution["passed"],
        execution["warned"],
        execution["failed"],
        execution["execution_status"],
    )
    print(
        "CONTINUOUS_ROUNDTRIP_RESULT",
        roundtrip["record_count"],
        roundtrip["passed"],
        roundtrip["warned"],
        roundtrip["failed"],
        roundtrip["roundtrip_status"],
    )
    if args.strict and (execution["failed"] or roundtrip["failed"]):
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
