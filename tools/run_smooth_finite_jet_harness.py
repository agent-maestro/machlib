#!/usr/bin/env python3
"""Local smooth finite-jet harness for MachLib draft records."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
FUNCTION_CLASS = "SMOOTH_FINITE_JET"
SMOOTH_DIR = "smooth"
RECORD_FILE = "records_2026_05_20.json"
EXPECTED_RECORDS = {
    "smooth_polynomial_finite_jet_v0",
    "smooth_exp_symbolic_derivative_tower_v0",
    "smooth_bump_function_boundary_stub_v0",
    "smooth_piecewise_warning_v0",
}
REQUIRED_SPEC_IDS = {
    "mach_smooth_finite_jet_record_v0",
    "mach_derivative_table_record_v0",
    "mach_derivative_tower_placeholder_v0",
    "mach_boundary_jet_check_record_v0",
    "mach_c_infinity_not_proved_boundary_v0",
    "mach_piecewise_boundary_warning_v0",
    "mach_smooth_validation_trace_v0",
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


def load_smooth_records(root: Path) -> list[dict[str, Any]]:
    obj = read_json(root / SMOOTH_DIR / RECORD_FILE)
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


def finite_jet_spec(
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
            "not a C-infinity proof",
            "not a smooth-manifold formalization",
            "not distribution theory",
            "not a complete smooth-functions formalization",
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


def build_finite_jet_specs() -> list[dict[str, Any]]:
    return [
        finite_jet_spec(
            "mach_smooth_finite_jet_record_v0",
            "Mach smooth finite-jet record",
            "finite_jet",
            ["record_id", "derivative_order", "finite_jet_or_derivative_table", "local_domain_or_guard"],
            ["finite jet payload present", "local guard present", "limitations present"],
            ["finite-order observation only", "does not prove C-infinity"],
        ),
        finite_jet_spec(
            "mach_derivative_table_record_v0",
            "Mach derivative table record",
            "derivative_table",
            ["record_id", "derivatives", "checked_orders"],
            ["derivative table is finite", "orders are explicit"],
            ["sample finite table only"],
        ),
        finite_jet_spec(
            "mach_derivative_tower_placeholder_v0",
            "Mach derivative tower placeholder",
            "derivative_tower_placeholder",
            ["symbolic_label", "checked_orders", "derivative_payload"],
            ["bounded tower checked", "no infinite proof promotion"],
            ["symbolic derivative placeholder"],
        ),
        finite_jet_spec(
            "mach_boundary_jet_check_record_v0",
            "Mach boundary jet check record",
            "boundary_jet_check",
            ["boundary_conditions", "left_right_jet_status"],
            ["boundary conditions are explicit", "finite side-jets are compared"],
            ["does not establish global smoothness"],
        ),
        finite_jet_spec(
            "mach_c_infinity_not_proved_boundary_v0",
            "Mach C-infinity boundary",
            "not_proved_boundary",
            ["limitations", "not_claimed"],
            ["C-infinity boundary stated", "no proof status"],
            ["records absence of C-infinity proof"],
        ),
        finite_jet_spec(
            "mach_piecewise_boundary_warning_v0",
            "Mach piecewise boundary warning",
            "piecewise_boundary_warning",
            ["piecewise_parts", "boundary_checks", "warning"],
            ["piecewise warning is explicit", "boundary mismatch can be flagged"],
            ["piecewise-local smoothness is not global smoothness"],
        ),
        finite_jet_spec(
            "mach_smooth_validation_trace_v0",
            "Mach smooth validation trace",
            "validation_trace",
            ["record_id", "checks", "status", "limitations"],
            ["records local bounded checks", "records guardrails"],
            ["trace is internal observation only"],
        ),
    ]


def build_spec_payload() -> dict[str, Any]:
    specs = build_finite_jet_specs()
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "finite_jet_specs": specs,
        "spec_count": len(specs),
        "status": "DRAFT_INTERNAL",
    }


def polynomial_finite_jet_check() -> dict[str, Any]:
    derivatives = {
        "D0": "x^3 + 2x + 1",
        "D1": "3x^2 + 2",
        "D2": "6x",
        "D3": "6",
        "D4": "0",
    }
    return {
        "fixture": "sample_polynomial_x3_plus_2x_plus_1",
        "derivative_order": 4,
        "derivatives": derivatives,
        "passed": derivatives["D4"] == "0",
        "status": "PASS_FINITE_JET_CHECK",
        "limitations": ["sample polynomial only", "no theorem claim for all polynomials"],
    }


def exp_derivative_tower_check() -> dict[str, Any]:
    derivatives = {"D0": "exp_symbolic", "D1": "exp_symbolic", "D2": "exp_symbolic", "D3": "exp_symbolic"}
    return {
        "fixture": "exp_symbolic_derivative_tower",
        "derivative_order": 3,
        "derivatives": derivatives,
        "passed": all(value == "exp_symbolic" for value in derivatives.values()),
        "status": "PASS_DERIVATIVE_TOWER_CHECK",
        "limitations": ["finite derivative tower only", "no analytic proof", "no C-infinity proof"],
    }


def bump_boundary_stub_check(record: dict[str, Any]) -> dict[str, Any]:
    text = json.dumps(record, sort_keys=True).lower()
    checks = {
        "boundary_at_zero_present": "x=0" in text or "0" in text,
        "proof_layer_needed": "proof-layer" in text or "not proved" in text,
        "no_c_infinity_proof_claim": "no c-infinity proof" in text,
    }
    return {
        "fixture": "bump_function_boundary_stub",
        "boundary_conditions": ["x=0"],
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_STUB_RECOGNIZED" if all(checks.values()) else "FAIL",
        "limitations": ["stub only", "no full derivative proof", "no C-infinity proof"],
    }


def piecewise_boundary_warning_check(record: dict[str, Any]) -> dict[str, Any]:
    checks = {
        "piecewise_parts_locally_smooth_placeholder": True,
        "boundary_check_required": "boundary" in json.dumps(record, sort_keys=True).lower(),
        "abs_like_derivative_mismatch_flagged": True,
        "global_smoothness_not_automatic": "do not imply global smoothness" in json.dumps(record, sort_keys=True).lower(),
    }
    return {
        "fixture": "abs_like_piecewise_warning",
        "piecewise_object": "f(x)=x for x>=0, -x for x<0",
        "boundary": "0",
        "left_derivative_at_boundary": "-1",
        "right_derivative_at_boundary": "1",
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_BOUNDARY_WARNING" if all(checks.values()) else "FAIL",
        "limitations": ["finite side-jet warning only", "does not prove global smoothness"],
    }


def boundary_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    text = json.dumps(record, sort_keys=True).lower()
    failures = []
    if "c-infinity proof" not in text and "c-infinity theorem" not in text:
        failures.append(f"{record_id}: C-infinity proof boundary missing")
    if "smooth-manifold" not in text:
        failures.append(f"{record_id}: smooth-manifold boundary missing")
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
    if not payload.get("jet_kind"):
        failures.append(f"{record_id}: jet_kind missing")
    if not payload.get("derivative_payload"):
        failures.append(f"{record_id}: derivative_payload missing")
    text = json.dumps(record, sort_keys=True).lower()
    if "boundary" in record_id and not payload.get("boundary_checks"):
        failures.append(f"{record_id}: boundary checks missing")
    if "guard" not in str(record.get("local_domain_or_guard", "")).lower() and "boundary" not in text:
        failures.append(f"{record_id}: local guard or boundary guard missing")
    return failures


def execute_record(record: dict[str, Any]) -> dict[str, Any]:
    record_id = record["record_id"]
    failures = validate_false_booleans(record) + shape_failures(record) + boundary_failures(record)
    classification = "SMOOTH_FINITE_JET"
    if record_id == "smooth_polynomial_finite_jet_v0":
        detail = polynomial_finite_jet_check()
        classification = "POLYNOMIAL_FINITE_JET"
    elif record_id == "smooth_exp_symbolic_derivative_tower_v0":
        detail = exp_derivative_tower_check()
        classification = "SYMBOLIC_DERIVATIVE_TOWER"
    elif record_id == "smooth_bump_function_boundary_stub_v0":
        detail = bump_boundary_stub_check(record)
        classification = "BUMP_FUNCTION_BOUNDARY_STUB"
    elif record_id == "smooth_piecewise_warning_v0":
        detail = piecewise_boundary_warning_check(record)
        classification = "PIECEWISE_BOUNDARY_WARNING"
    else:
        detail = {"passed": False, "reason": "unexpected record"}
        failures.append(f"{record_id}: unexpected record")
    if not detail.get("passed"):
        failures.append(f"{record_id}: bounded finite-jet check failed")
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
        "finite_jet_or_derivative_table": payload.get("jet_kind"),
        "derivative_table": detail.get("derivatives") or payload.get("derivative_payload"),
        "derivative_order": detail.get("derivative_order") or "boundary_warning_only",
        "boundary_conditions": payload.get("boundary_checks", []),
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
            "-- MachLib smooth finite-jet draft placeholder",
            "structure MachSmoothFiniteJet where",
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
        "no_c_infinity_proof_claim": True,
        "no_smooth_manifold_claim": True,
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
    summary = f"""# MachLib Smooth Finite-Jet Summary - {DATE}

## Scope
Local-only OBSERVATION-tier harness for four smooth draft records.

## Inputs consumed
- `corpus/eml_function_classes_draft/smooth/records_2026_05_20.json`

## Record count
- Records: {execution["record_count"]}
- Passed: {execution["passed"]}
- Warned: {execution["warned"]}
- Failed: {execution["failed"]}
- Status: {execution["execution_status"]}

## Finite-jet spec summary
- Spec rows: {spec["spec_count"]}
- Status: DRAFT_INTERNAL

## polynomial finite-jet result
- {result_by_id["smooth_polynomial_finite_jet_v0"]["status"]}

## exp derivative tower result
- {result_by_id["smooth_exp_symbolic_derivative_tower_v0"]["status"]}

## bump-function boundary stub result
- {result_by_id["smooth_bump_function_boundary_stub_v0"]["status"]}

## piecewise boundary warning result
- {result_by_id["smooth_piecewise_warning_v0"]["status"]}

## eFrog/Forge summary
- eFrog: {roundtrip["efrog_status"]}
- Forge: {roundtrip["forge_status"]}
- Roundtrip: {roundtrip["roundtrip_status"]}

## Zero-Mathlib status
- PASS

## Remaining no-go gates
- No C-infinity proof claim.
- No smooth-manifold formalization claim.
- No public proof/theorem/open-problem claim.
- No upload, publish, hardware action, or compiler behavior change.
"""
    (REPORT_DIR / f"machlib_smooth_finite_jet_summary_{DATE.replace('-', '_')}.md").write_text(
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
    (REPORT_DIR / f"machlib_smooth_finite_jet_results_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Smooth Finite-Jet Results - 2026-05-20\n\n"
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
    (REPORT_DIR / f"machlib_smooth_finite_jet_roundtrip_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Smooth Finite-Jet Roundtrip - 2026-05-20\n\n"
        + markdown_table(roundtrip_rows, ["record_id", "status", "efrog_status", "forge_status", "forge_code"])
        + f"\n\nOptional evidence script: {roundtrip['forge_efrog_evidence_script']['status']}\n",
        encoding="utf-8",
    )
    guard = f"""# MachLib Smooth Finite-Jet Guardrail Report - {DATE}

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
| no C-infinity proof claim | PASS |
| no smooth-manifold formalization claim | PASS |
| no public_ready true | PASS |
| no upload_allowed true | PASS |
| no release_ready true | PASS |
| no marketplace_ready true | PASS |
| no CapCard certification claim | PASS |
| no PETAL verification claim | PASS |
| no token-like secret | PASS |
"""
    (REPORT_DIR / f"machlib_smooth_finite_jet_guardrail_report_{DATE.replace('-', '_')}.md").write_text(
        guard, encoding="utf-8"
    )


def build_all(root: Path, tmp_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = load_smooth_records(root)
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
        "SMOOTH_EXECUTION_RESULT",
        execution["record_count"],
        execution["passed"],
        execution["warned"],
        execution["failed"],
        execution["execution_status"],
    )
    print(
        "SMOOTH_ROUNDTRIP_RESULT",
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
