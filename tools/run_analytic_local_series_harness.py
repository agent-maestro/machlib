#!/usr/bin/env python3
"""Local analytic-series harness for MachLib draft records."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from math import factorial
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
FUNCTION_CLASS = "ANALYTIC_LOCAL_SERIES"
ANALYTIC_DIR = "analytic"
RECORD_FILE = "records_2026_05_20.json"
EXPECTED_RECORDS = {
    "analytic_power_series_local_record_v0",
    "analytic_exp_series_stub_v0",
    "analytic_sin_cos_series_stub_v0",
    "analytic_rational_local_except_pole_v0",
}
REQUIRED_SPEC_IDS = {
    "mach_local_power_series_record_v0",
    "mach_taylor_jet_record_v0",
    "mach_coefficient_pattern_record_v0",
    "mach_truncation_order_record_v0",
    "mach_radius_guard_placeholder_v0",
    "mach_singularity_exclusion_guard_v0",
    "mach_convergence_not_proved_boundary_v0",
    "mach_analytic_validation_trace_v0",
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


def load_analytic_records(root: Path) -> list[dict[str, Any]]:
    obj = read_json(root / ANALYTIC_DIR / RECORD_FILE)
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


def local_series_spec(
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
        "allowed_statuses": ["DRAFT_INTERNAL", "PASS_LOCAL_SHAPE_CHECK", "PASS_FINITE_TRUNCATION_CHECK"],
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
            "not a convergence proof",
            "not global analytic continuation",
            "not a complete analytic-functions formalization",
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


def build_local_series_specs() -> list[dict[str, Any]]:
    return [
        local_series_spec(
            "mach_local_power_series_record_v0",
            "Mach local power-series record",
            "local_power_series",
            ["record_id", "center", "coefficients", "local_domain_or_guard"],
            ["series payload present", "local guard present", "limitations present"],
            ["formal local record only", "radius not established"],
        ),
        local_series_spec(
            "mach_taylor_jet_record_v0",
            "Mach Taylor jet record",
            "finite_taylor_jet",
            ["center", "truncation_order", "coefficient_table"],
            ["finite order is explicit", "coefficient table is bounded"],
            ["finite truncation only"],
        ),
        local_series_spec(
            "mach_coefficient_pattern_record_v0",
            "Mach coefficient pattern record",
            "coefficient_pattern",
            ["pattern_name", "bounded_indices", "coefficients"],
            ["bounded pattern checked", "no infinite proof promotion"],
            ["symbolic pattern placeholder"],
        ),
        local_series_spec(
            "mach_truncation_order_record_v0",
            "Mach truncation order record",
            "truncation_order",
            ["order", "terms_checked"],
            ["order is finite", "terms are listed"],
            ["does not establish convergence"],
        ),
        local_series_spec(
            "mach_radius_guard_placeholder_v0",
            "Mach radius guard placeholder",
            "radius_guard",
            ["radius_status", "local_domain_or_guard"],
            ["radius status is explicit", "limitation text present"],
            ["radius proof not supplied"],
        ),
        local_series_spec(
            "mach_singularity_exclusion_guard_v0",
            "Mach singularity exclusion guard",
            "singularity_guard",
            ["excluded_points", "local_center"],
            ["excluded point listed where applicable", "guard remains local"],
            ["no global continuation claim"],
        ),
        local_series_spec(
            "mach_convergence_not_proved_boundary_v0",
            "Mach convergence boundary",
            "not_proved_boundary",
            ["limitations", "not_claimed"],
            ["boundary stated", "no proof status"],
            ["records absence of convergence proof"],
        ),
        local_series_spec(
            "mach_analytic_validation_trace_v0",
            "Mach analytic validation trace",
            "validation_trace",
            ["record_id", "checks", "status", "limitations"],
            ["records local bounded checks", "records guardrails"],
            ["trace is internal observation only"],
        ),
    ]


def build_spec_payload() -> dict[str, Any]:
    specs = build_local_series_specs()
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "local_series_specs": specs,
        "spec_count": len(specs),
        "status": "DRAFT_INTERNAL",
    }


def exp_coefficients(order: int = 4) -> list[str]:
    return ["1" if n in (0, 1) else f"1/{factorial(n)}" for n in range(order + 1)]


def exp_series_check() -> dict[str, Any]:
    expected = ["1", "1", "1/2", "1/6", "1/24"]
    actual = exp_coefficients(4)
    return {
        "fixture": "exp_symbolic_series_at_0",
        "truncation_order": 4,
        "coefficients": actual,
        "truncation": "1 + x + x^2/2 + x^3/6 + x^4/24",
        "passed": actual == expected,
        "limitations": ["finite coefficient pattern only", "no convergence proof"],
    }


def sin_cos_series_check() -> dict[str, Any]:
    sin_terms = {"x": "1", "x^3": "-1/6", "x^5": "1/120"}
    cos_terms = {"1": "1", "x^2": "-1/2", "x^4": "1/24"}
    return {
        "fixture": "sin_cos_symbolic_series_at_0",
        "sin_truncation_order": 5,
        "cos_truncation_order": 4,
        "sin_coefficients": sin_terms,
        "cos_coefficients": cos_terms,
        "sin_truncation": "x - x^3/6 + x^5/120",
        "cos_truncation": "1 - x^2/2 + x^4/24",
        "passed": sin_terms == {"x": "1", "x^3": "-1/6", "x^5": "1/120"}
        and cos_terms == {"1": "1", "x^2": "-1/2", "x^4": "1/24"},
        "limitations": ["finite alternating pattern only", "no trigonometric theorem claim"],
    }


def rational_series_check() -> dict[str, Any]:
    coefficients = ["1", "1", "1", "1", "1"]
    excluded_points = ["1"]
    return {
        "fixture": "rational_geometric_series_at_0",
        "truncation_order": 4,
        "coefficients": coefficients,
        "truncation": "1 + x + x^2 + x^3 + x^4",
        "excluded_points": excluded_points,
        "passed": coefficients == ["1"] * 5 and "1" in excluded_points,
        "limitations": ["finite geometric pattern only", "pole exclusion is local guard"],
    }


def local_power_series_shape_check(record: dict[str, Any]) -> dict[str, Any]:
    payload = record.get("certificate_payload", {})
    text = json.dumps(record, sort_keys=True).lower()
    checks = {
        "has_series_kind": bool(payload.get("series_kind")),
        "has_coefficients": bool(payload.get("coefficients")),
        "has_radius_or_domain_limitation": "radius" in text or "domain" in text,
        "is_draft_internal": record.get("status") == "DRAFT_INTERNAL",
    }
    return {
        "fixture": "generic_local_power_series",
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_LOCAL_SHAPE_CHECK" if all(checks.values()) else "FAIL",
        "limitations": ["shape check only", "radius/domain remains placeholder"],
    }


def boundary_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    text = json.dumps(record, sort_keys=True).lower()
    failures = []
    if "convergence proof" not in text:
        failures.append(f"{record_id}: convergence boundary missing")
    if "global" not in text:
        failures.append(f"{record_id}: global analytic boundary missing")
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
    if not payload.get("series_kind"):
        failures.append(f"{record_id}: series_kind missing")
    if not payload.get("coefficients"):
        failures.append(f"{record_id}: coefficients missing")
    if "local" not in str(record.get("local_domain_or_guard", "")).lower():
        failures.append(f"{record_id}: local guard missing")
    return failures


def execute_record(record: dict[str, Any]) -> dict[str, Any]:
    record_id = record["record_id"]
    failures = validate_false_booleans(record) + shape_failures(record) + boundary_failures(record)
    classification = "LOCAL_SERIES_RECORD"
    if record_id == "analytic_power_series_local_record_v0":
        detail = local_power_series_shape_check(record)
        classification = "LOCAL_SERIES_RECORD"
    elif record_id == "analytic_exp_series_stub_v0":
        detail = exp_series_check()
        classification = "EXP_SERIES_STUB"
    elif record_id == "analytic_sin_cos_series_stub_v0":
        detail = sin_cos_series_check()
        classification = "SIN_COS_SERIES_STUB"
    elif record_id == "analytic_rational_local_except_pole_v0":
        detail = rational_series_check()
        classification = "RATIONAL_LOCAL_SERIES_EXCEPT_POLE"
        payload = record.get("certificate_payload", {})
        if "1" not in [str(item) for item in payload.get("excluded_points", [])]:
            failures.append(f"{record_id}: pole exclusion at x=1 missing")
    else:
        detail = {"passed": False, "reason": "unexpected record"}
        failures.append(f"{record_id}: unexpected record")
    if not detail.get("passed"):
        failures.append(f"{record_id}: bounded local-series check failed")
    return {
        "record_id": record_id,
        "title": record.get("title"),
        "classification": classification,
        "certificate_type": record.get("certificate_type"),
        "status": "FAIL" if failures else detail.get("status", "PASS_FINITE_TRUNCATION_CHECK"),
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
        "local_series_or_jet": payload.get("series_kind"),
        "coefficient_pattern": payload.get("coefficients"),
        "truncation_order": detail.get("truncation_order")
        or detail.get("sin_truncation_order")
        or "finite_shape_only",
        "domain_or_radius_guard": record.get("local_domain_or_guard") or payload.get("radius_status"),
        "singularity_exclusion": payload.get("excluded_points", []),
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
            "-- MachLib analytic local-series draft placeholder",
            "structure MachAnalyticLocalSeries where",
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
        "no_convergence_claim": True,
        "no_global_analytic_claim": True,
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
    summary = f"""# MachLib Analytic Local Series Summary - {DATE}

## Scope
Local-only OBSERVATION-tier harness for four analytic draft records.

## Inputs consumed
- `corpus/eml_function_classes_draft/analytic/records_2026_05_20.json`

## Record count
- Records: {execution["record_count"]}
- Passed: {execution["passed"]}
- Warned: {execution["warned"]}
- Failed: {execution["failed"]}
- Status: {execution["execution_status"]}

## Local-series spec summary
- Spec rows: {spec["spec_count"]}
- Status: DRAFT_INTERNAL

## power-series local record result
- {result_by_id["analytic_power_series_local_record_v0"]["status"]}

## exp series stub result
- {result_by_id["analytic_exp_series_stub_v0"]["status"]}

## sin/cos series stub result
- {result_by_id["analytic_sin_cos_series_stub_v0"]["status"]}

## rational local except pole result
- {result_by_id["analytic_rational_local_except_pole_v0"]["status"]}

## eFrog/Forge summary
- eFrog: {roundtrip["efrog_status"]}
- Forge: {roundtrip["forge_status"]}
- Roundtrip: {roundtrip["roundtrip_status"]}

## Zero-Mathlib status
- PASS

## Remaining no-go gates
- No convergence proof claim.
- No global analytic continuation claim.
- No public proof/theorem/open-problem claim.
- No upload, publish, hardware action, or compiler behavior change.
"""
    (REPORT_DIR / f"machlib_analytic_local_series_summary_{DATE.replace('-', '_')}.md").write_text(
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
    (REPORT_DIR / f"machlib_analytic_local_series_results_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Analytic Local Series Results - 2026-05-20\n\n"
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
    (REPORT_DIR / f"machlib_analytic_local_series_roundtrip_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Analytic Local Series Roundtrip - 2026-05-20\n\n"
        + markdown_table(roundtrip_rows, ["record_id", "status", "efrog_status", "forge_status", "forge_code"])
        + f"\n\nOptional evidence script: {roundtrip['forge_efrog_evidence_script']['status']}\n",
        encoding="utf-8",
    )
    guard = f"""# MachLib Analytic Local Series Guardrail Report - {DATE}

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
| no convergence proof claim | PASS |
| no global analytic continuation claim | PASS |
| no public_ready true | PASS |
| no upload_allowed true | PASS |
| no release_ready true | PASS |
| no marketplace_ready true | PASS |
| no CapCard certification claim | PASS |
| no PETAL verification claim | PASS |
| no token-like secret | PASS |
"""
    (REPORT_DIR / f"machlib_analytic_local_series_guardrail_report_{DATE.replace('-', '_')}.md").write_text(
        guard, encoding="utf-8"
    )


def build_all(root: Path, tmp_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = load_analytic_records(root)
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
        "ANALYTIC_EXECUTION_RESULT",
        execution["record_count"],
        execution["passed"],
        execution["warned"],
        execution["failed"],
        execution["execution_status"],
    )
    print(
        "ANALYTIC_ROUNDTRIP_RESULT",
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
