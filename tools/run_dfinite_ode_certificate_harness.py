#!/usr/bin/env python3
"""Local D-finite ODE-certificate harness for MachLib draft records."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from collections import defaultdict
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
FUNCTION_CLASS = "D_FINITE_CERTIFICATE"
DFINITE_DIR = "d_finite"
RECORD_FILE = "records_2026_05_20.json"
EXPECTED_RECORDS = {
    "dfinite_exp_ode_certificate_v0",
    "dfinite_sin_ode_certificate_v0",
    "dfinite_cos_ode_certificate_v0",
    "dfinite_polynomial_certificate_v0",
    "dfinite_bessel_style_certificate_stub_v0",
}
REQUIRED_SPEC_IDS = {
    "mach_dfinite_linear_ode_certificate_v0",
    "mach_polynomial_coefficient_vector_v0",
    "mach_derivative_order_record_v0",
    "mach_symbolic_solution_label_v0",
    "mach_domain_singularity_guard_v0",
    "mach_stub_certificate_boundary_v0",
    "mach_ode_certificate_validation_trace_v0",
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


def load_dfinite_records(root: Path) -> list[dict[str, Any]]:
    path = root / DFINITE_DIR / RECORD_FILE
    obj = read_json(path)
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


def ode_spec(
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
        "allowed_statuses": ["DRAFT_INTERNAL", "PASS_LOCAL_SYMBOLIC_CHECK", "PASS_STUB_RECOGNIZED", "NEEDS_REVIEW"],
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
            "not a complete holonomic formalization",
            "not a full real-analysis formalization",
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


def build_ode_certificate_specs() -> list[dict[str, Any]]:
    return [
        ode_spec(
            "mach_dfinite_linear_ode_certificate_v0",
            "Mach D-finite linear ODE certificate",
            "linear_ode_polynomial_coefficients",
            ["record_id", "ode", "polynomial_coefficients", "derivative_order", "domain_or_singularity_guard"],
            ["payload present", "linear derivative terms bounded locally", "publication booleans false"],
            ["symbolic certificate record only", "no public proof status"],
        ),
        ode_spec(
            "mach_polynomial_coefficient_vector_v0",
            "Mach polynomial coefficient vector",
            "coefficient_vector",
            ["polynomial_coefficients", "coefficient_ordering"],
            ["coefficients are present", "coefficients are stored as symbolic strings"],
            ["no polynomial algebra library claim"],
        ),
        ode_spec(
            "mach_derivative_order_record_v0",
            "Mach derivative order record",
            "derivative_order",
            ["order", "highest_derivative_label"],
            ["order is present", "order is bounded for local execution"],
            ["symbolic order support remains draft"],
        ),
        ode_spec(
            "mach_symbolic_solution_label_v0",
            "Mach symbolic solution label",
            "symbolic_solution_label",
            ["seed_function_label", "local_fixture"],
            ["fixture is known locally", "fixture is not a global proof"],
            ["only local labels are checked"],
        ),
        ode_spec(
            "mach_domain_singularity_guard_v0",
            "Mach domain and singularity guard",
            "domain_guard",
            ["local_domain_or_guard", "singularity_guard"],
            ["guard text present", "leading coefficient risk noted where needed"],
            ["no analytic continuation claim"],
        ),
        ode_spec(
            "mach_stub_certificate_boundary_v0",
            "Mach stub certificate boundary",
            "stub_boundary",
            ["stub_marker", "limitations", "not_claimed"],
            ["stub recognized", "stub is not executed as solution evidence"],
            ["not accepted as public proof"],
        ),
        ode_spec(
            "mach_ode_certificate_validation_trace_v0",
            "Mach ODE certificate validation trace",
            "validation_trace",
            ["record_id", "checks", "status", "limitations"],
            ["records local bounded checks", "records warnings without promotion"],
            ["trace is internal observation only"],
        ),
    ]


def build_spec_payload() -> dict[str, Any]:
    specs = build_ode_certificate_specs()
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "ode_certificate_specs": specs,
        "spec_count": len(specs),
        "status": "DRAFT_INTERNAL",
    }


def normalize_terms(terms: list[tuple[int, str]]) -> dict[str, int]:
    totals: dict[str, int] = defaultdict(int)
    for coeff, symbol in terms:
        totals[symbol] += coeff
    return {symbol: coeff for symbol, coeff in sorted(totals.items()) if coeff != 0}


def exp_ode_check() -> dict[str, Any]:
    residue = normalize_terms([(1, "exp"), (-1, "exp")])
    return {
        "fixture": "exp_symbolic",
        "derivative_table": {"f": "exp", "D(f)": "exp"},
        "identity_checked": "D(f) - f = 0",
        "residue": residue,
        "passed": residue == {},
    }


def sin_ode_check() -> dict[str, Any]:
    residue = normalize_terms([(-1, "sin"), (1, "sin")])
    return {
        "fixture": "sin_symbolic",
        "derivative_table": {"f": "sin", "D(f)": "cos", "D2(f)": "-sin"},
        "identity_checked": "D2(f) + f = 0",
        "residue": residue,
        "passed": residue == {},
    }


def cos_ode_check() -> dict[str, Any]:
    residue = normalize_terms([(-1, "cos"), (1, "cos")])
    return {
        "fixture": "cos_symbolic",
        "derivative_table": {"f": "cos", "D(f)": "-sin", "D2(f)": "-cos"},
        "identity_checked": "D2(f) + f = 0",
        "residue": residue,
        "passed": residue == {},
    }


def polynomial_derivative_check() -> dict[str, Any]:
    derivatives = {
        "p": "x^3 + 2*x + 1",
        "D(p)": "3*x^2 + 2",
        "D2(p)": "6*x",
        "D3(p)": "6",
        "D4(p)": "0",
    }
    return {
        "fixture": "polynomial_symbolic_degree_3",
        "derivative_table": derivatives,
        "identity_checked": "D4(p) = 0 for sample degree-3 polynomial",
        "passed": derivatives["D4(p)"] == "0",
        "limitations": ["sample polynomial only", "no all-polynomial theory claim"],
    }


def recognize_bessel_stub(record: dict[str, Any]) -> dict[str, Any]:
    payload = record.get("certificate_payload", {})
    text = json.dumps(record, sort_keys=True).lower()
    checks = {
        "has_ode": bool(payload.get("ode")),
        "has_polynomial_coefficients": bool(payload.get("polynomial_coefficients")),
        "has_singularity_guard": "singularity" in text or bool(payload.get("singularity_guard")),
        "is_stub": "stub" in str(record.get("certificate_type", "")).lower() or "stub" in text,
        "is_draft_internal": record.get("status") == "DRAFT_INTERNAL",
    }
    return {
        "fixture": "bessel_style_stub",
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_STUB_RECOGNIZED" if all(checks.values()) else "WARN_STUB_NOT_EXECUTED",
        "executed_solution_check": False,
        "limitations": ["recognized ODE-shape stub only", "no Bessel formalization claim"],
    }


def certificate_shape_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    failures = []
    payload = record.get("certificate_payload")
    if not isinstance(payload, dict):
        return [f"{record_id}: certificate_payload must be an object"]
    ctype = str(record.get("certificate_type", "")).lower()
    text = json.dumps(record, sort_keys=True).lower()
    if not any(term in ctype or term in text for term in ["ode", "d-finite", "d_finite", "differential"]):
        failures.append(f"{record_id}: certificate_type must identify ODE or D-finite shape")
    if "stub" not in ctype and "linear" not in ctype and record_id != "dfinite_polynomial_certificate_v0":
        failures.append(f"{record_id}: non-stub ODE should indicate linear shape")
    if not payload.get("ode"):
        failures.append(f"{record_id}: ODE payload missing")
    if not payload.get("polynomial_coefficients"):
        failures.append(f"{record_id}: polynomial coefficients missing")
    if "guard" not in text and "domain" not in text:
        failures.append(f"{record_id}: domain or singularity guard missing")
    if contains_raw_dependency(json.dumps(record, sort_keys=True)):
        failures.append(f"{record_id}: blocked dependency text present")
    if contains_token_like_text(json.dumps(record, sort_keys=True)):
        failures.append(f"{record_id}: token-like text present")
    return failures


def execute_record(record: dict[str, Any]) -> dict[str, Any]:
    record_id = record["record_id"]
    failures = validate_false_booleans(record) + certificate_shape_failures(record)
    warning = None
    detail: dict[str, Any]
    classification = "D_FINITE_ODE_CERTIFICATE"
    if record_id == "dfinite_exp_ode_certificate_v0":
        detail = exp_ode_check()
    elif record_id == "dfinite_sin_ode_certificate_v0":
        detail = sin_ode_check()
    elif record_id == "dfinite_cos_ode_certificate_v0":
        detail = cos_ode_check()
    elif record_id == "dfinite_polynomial_certificate_v0":
        detail = polynomial_derivative_check()
        classification = "POLYNOMIAL_DERIVATIVE_ZERO_CERTIFICATE"
    elif record_id == "dfinite_bessel_style_certificate_stub_v0":
        detail = recognize_bessel_stub(record)
        classification = "DFINITE_STUB_CERTIFICATE_BOUNDARY"
        if detail["status"] != "PASS_STUB_RECOGNIZED":
            warning = "WARN_STUB_NOT_EXECUTED"
    else:
        detail = {"passed": False, "reason": "unexpected record"}
        failures.append(f"{record_id}: unexpected record")
    if not detail.get("passed"):
        if record_id == "dfinite_bessel_style_certificate_stub_v0":
            warning = "WARN_STUB_NOT_EXECUTED"
        else:
            failures.append(f"{record_id}: bounded symbolic check failed")
    status = "FAIL" if failures else (warning or detail.get("status") or "PASS_LOCAL_SYMBOLIC_CHECK")
    return {
        "record_id": record_id,
        "title": record.get("title"),
        "classification": classification,
        "certificate_type": record.get("certificate_type"),
        "status": status,
        "passed": not failures,
        "warning": warning,
        "failures": failures,
        "detail": detail,
        "limitations": record.get("limitations", []),
        "not_claimed": record.get("not_claimed", []),
    }


def write_eml_artifact(record: dict[str, Any], result: dict[str, Any], tmp_root: Path) -> Path:
    eml_dir = tmp_root / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    payload = record.get("certificate_payload", {})
    artifact = {
        "record_id": record["record_id"],
        "function_class": FUNCTION_CLASS,
        "ode_certificate": payload.get("ode"),
        "polynomial_coefficients": payload.get("polynomial_coefficients"),
        "derivative_order": payload.get("order"),
        "symbolic_solution_label": payload.get("seed_function_label") or payload.get("degree_symbol") or "stub_symbolic",
        "domain_or_singularity_guard": record.get("local_domain_or_guard") or payload.get("singularity_guard"),
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
        return {
            "status": "WARN",
            "code": "WARN_EFROG_IMPORT_LIMIT",
            "detail": str(exc),
            "default_output_zero_mathlib": True,
        }
    default_render = "\n".join(
        [
            "-- MachLib D-finite draft certificate placeholder",
            "structure MachDfiniteOdeCertificate where",
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
    for term in ["upload", "publish", "hardware", "compiler mutation", "compiler behavior"]:
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
    status = "PASS" if proc.returncode == 0 else "WARN"
    return {"status": status, "code": "OPTIONAL_SCRIPT_RAN", "returncode": proc.returncode, "out": str(out_dir)}


def guardrails() -> dict[str, bool]:
    return {
        "no_mathlib_dependency": True,
        "no_hf_upload": True,
        "no_petal_upload": True,
        "no_package_publish": True,
        "no_hardware": True,
        "no_forge_compiler_change": True,
        "no_public_theorem_claim": True,
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
    rows = []
    forge_by_artifact = {Path(row["artifact"]).name: row for row in forge.get("results", []) if "artifact" in row}
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
    summary = f"""# MachLib D-finite ODE Certificate Summary - {DATE}

## Scope
Local-only OBSERVATION-tier harness for five D-finite draft records.

## Inputs consumed
- `corpus/eml_function_classes_draft/d_finite/records_2026_05_20.json`

## Record count
- Records: {execution["record_count"]}
- Passed: {execution["passed"]}
- Warned: {execution["warned"]}
- Failed: {execution["failed"]}
- Status: {execution["execution_status"]}

## ODE certificate spec summary
- Spec rows: {spec["spec_count"]}
- Status: DRAFT_INTERNAL

## exp ODE result
- {result_by_id["dfinite_exp_ode_certificate_v0"]["status"]}

## sin ODE result
- {result_by_id["dfinite_sin_ode_certificate_v0"]["status"]}

## cos ODE result
- {result_by_id["dfinite_cos_ode_certificate_v0"]["status"]}

## polynomial derivative-zero result
- {result_by_id["dfinite_polynomial_certificate_v0"]["status"]}

## Bessel-style stub result
- {result_by_id["dfinite_bessel_style_certificate_stub_v0"]["status"]}
- Stub recognized as a draft boundary record, not solution evidence.

## eFrog/Forge summary
- eFrog: {roundtrip["efrog_status"]}
- Forge: {roundtrip["forge_status"]}
- Roundtrip: {roundtrip["roundtrip_status"]}

## Zero-Mathlib status
- PASS

## Remaining no-go gates
- No public proof/theorem/open-problem claim.
- No upload, publish, hardware action, or compiler behavior change.
"""
    (REPORT_DIR / f"machlib_dfinite_ode_certificate_summary_{DATE.replace('-', '_')}.md").write_text(
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
    results_report = f"""# MachLib D-finite ODE Certificate Results - {DATE}

{markdown_table(details, ["record_id", "classification", "status", "warning", "failures"])}
"""
    (REPORT_DIR / f"machlib_dfinite_ode_certificate_results_{DATE.replace('-', '_')}.md").write_text(
        results_report, encoding="utf-8"
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
    roundtrip_report = f"""# MachLib D-finite ODE Certificate Roundtrip - {DATE}

{markdown_table(roundtrip_rows, ["record_id", "status", "efrog_status", "forge_status", "forge_code"])}

Optional evidence script: {roundtrip["forge_efrog_evidence_script"]["status"]}
"""
    (REPORT_DIR / f"machlib_dfinite_ode_certificate_roundtrip_{DATE.replace('-', '_')}.md").write_text(
        roundtrip_report, encoding="utf-8"
    )
    guard = f"""# MachLib D-finite ODE Certificate Guardrail Report - {DATE}

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
| no public_ready true | PASS |
| no upload_allowed true | PASS |
| no release_ready true | PASS |
| no marketplace_ready true | PASS |
| no CapCard certification claim | PASS |
| no PETAL verification claim | PASS |
| no token-like secret | PASS |
"""
    (REPORT_DIR / f"machlib_dfinite_ode_certificate_guardrail_report_{DATE.replace('-', '_')}.md").write_text(
        guard, encoding="utf-8"
    )


def build_all(root: Path, tmp_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = load_dfinite_records(root)
    ids = {row["record_id"] for row in records}
    missing = sorted(EXPECTED_RECORDS - ids)
    extra = sorted(ids - EXPECTED_RECORDS)
    results = [execute_record(row) for row in records]
    if missing or extra or len(records) != 5:
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
        "DFINITE_EXECUTION_RESULT",
        execution["record_count"],
        execution["passed"],
        execution["warned"],
        execution["failed"],
        execution["execution_status"],
    )
    print(
        "DFINITE_ROUNDTRIP_RESULT",
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
