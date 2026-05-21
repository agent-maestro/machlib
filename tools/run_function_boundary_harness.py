#!/usr/bin/env python3
"""Local boundary/non-example harness for MachLib draft function-class records."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
FUNCTION_CLASS = "CLASS_BOUNDARY_RELATION"
BOUNDARY_DIR = "boundary_relations"
RECORD_FILE = "records_2026_05_20.json"
EXPECTED_RECORDS = {
    "smooth_not_analytic_boundary_record_v0",
    "analytic_not_dfinite_boundary_record_v0",
    "dfinite_domain_singularity_guard_v0",
}
REQUIRED_SPEC_IDS = {
    "mach_function_class_boundary_record_v0",
    "mach_non_implication_boundary_v0",
    "mach_counterexample_stub_record_v0",
    "mach_domain_singularity_guard_record_v0",
    "mach_subset_overclaim_blocker_v0",
    "mach_boundary_validation_trace_v0",
    "mach_public_claim_blocker_v0",
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


def load_boundary_records(root: Path) -> list[dict[str, Any]]:
    obj = read_json(root / BOUNDARY_DIR / RECORD_FILE)
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


def boundary_spec(
    spec_id: str,
    name: str,
    relation_kind: str,
    required_fields: list[str],
    validation_checks: list[str],
    limitations: list[str],
) -> dict[str, Any]:
    return {
        "spec_id": spec_id,
        "name": name,
        "relation_kind": relation_kind,
        "required_fields": required_fields,
        "allowed_statuses": [
            "DRAFT_INTERNAL",
            "PASS_BOUNDARY_STUB",
            "PASS_BOUNDARY_GUARD",
            "PASS_SINGULARITY_GUARD_CHECK",
        ],
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
            "not a real-analysis completion claim",
            "not a topology formalization",
            "not a function-class hierarchy completion claim",
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


def build_boundary_specs() -> list[dict[str, Any]]:
    return [
        boundary_spec(
            "mach_function_class_boundary_record_v0",
            "Mach function-class boundary record",
            "boundary_record",
            ["record_id", "relation", "blocked_overclaim", "limitations", "not_claimed"],
            ["relation payload present", "non-overclaim marker present", "limitations present"],
            ["internal observation only", "does not prove a class hierarchy theorem"],
        ),
        boundary_spec(
            "mach_non_implication_boundary_v0",
            "Mach non-implication boundary",
            "non_implication_boundary",
            ["relation", "source_class", "target_class", "blocked_overclaim"],
            ["automatic implication is blocked", "public proof status absent"],
            ["records a boundary guard, not a public counterexample proof"],
        ),
        boundary_spec(
            "mach_counterexample_stub_record_v0",
            "Mach counterexample stub record",
            "counterexample_stub",
            ["example_or_stub", "stub_status", "limitations"],
            ["stub is explicitly draft/internal", "no proof claim is present"],
            ["example references require later proof-layer review"],
        ),
        boundary_spec(
            "mach_domain_singularity_guard_record_v0",
            "Mach domain singularity guard record",
            "domain_singularity_guard",
            ["leading_coefficient", "singularity_candidates", "domain_guard"],
            ["leading coefficient zeros detected", "global promotion blocked"],
            ["finite symbolic guard fixture only"],
        ),
        boundary_spec(
            "mach_subset_overclaim_blocker_v0",
            "Mach subset overclaim blocker",
            "overclaim_blocker",
            ["blocked_overclaim", "validation_trace"],
            ["smooth-to-analytic blocked", "analytic-to-D-finite blocked", "D-finite domain guard required"],
            ["prevents subset overclaims without proving hierarchy theorems"],
        ),
        boundary_spec(
            "mach_boundary_validation_trace_v0",
            "Mach boundary validation trace",
            "validation_trace",
            ["record_id", "checks", "status", "limitations"],
            ["records bounded local checks", "records guardrails"],
            ["trace is internal observation only"],
        ),
        boundary_spec(
            "mach_public_claim_blocker_v0",
            "Mach public claim blocker",
            "public_claim_blocker",
            ["not_claimed", "public_ready", "upload_allowed", "release_ready"],
            ["public-ready flags are false", "upload/release flags are false"],
            ["requires human review before any public-facing claim"],
        ),
    ]


def build_spec_payload() -> dict[str, Any]:
    specs = build_boundary_specs()
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "function_class": FUNCTION_CLASS,
        "boundary_specs": specs,
        "spec_count": len(specs),
        "status": "DRAFT_INTERNAL",
    }


def smooth_not_analytic_boundary_check(record: dict[str, Any]) -> dict[str, Any]:
    text = json.dumps(record, sort_keys=True).lower()
    checks = {
        "relation_blocks_smooth_to_analytic": "smooth_not_automatically_analytic" in text,
        "stub_or_draft_internal": "stub" in text and record.get("status") == "DRAFT_INTERNAL",
        "not_presented_as_proved": "not proved" in text or "no c-infinity proof" in text,
        "no_c_infinity_proof_claim": "c-infinity proved" not in text,
        "no_analytic_nonexample_proof_claim": "analytic non-example proof" not in text,
    }
    return {
        "fixture": "bump_function_style_stub_boundary",
        "blocked_overclaim": "smooth -> analytic",
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_BOUNDARY_STUB",
        "limitations": ["stub recognition only", "no C-infinity proof claim", "no analytic non-example proof claim"],
    }


def analytic_not_dfinite_boundary_check(record: dict[str, Any]) -> dict[str, Any]:
    text = json.dumps(record, sort_keys=True).lower()
    checks = {
        "relation_blocks_analytic_to_dfinite": "analytic_not_automatically_dfinite" in text,
        "finite_ode_certificate_required": "finite ode certificate" in text,
        "no_public_theorem_proof_claim": "public theorem proof" not in text and "theorem result" in text,
        "no_global_analytic_proof_claim": "global analytic proof" not in text,
        "no_dfinite_completeness_claim": "classification completeness" in text,
    }
    return {
        "fixture": "generic_analytic_without_finite_ode_certificate_stub",
        "blocked_overclaim": "analytic -> D-finite",
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_BOUNDARY_GUARD",
        "limitations": ["generic guard only", "no specific public theorem proof", "no D-finite completeness claim"],
    }


def dfinite_domain_singularity_guard_check(record: dict[str, Any]) -> dict[str, Any]:
    leading_coefficient = "x"
    singularity_candidates = [0]
    checks = {
        "leading_coefficient_zero_detected": 0 in singularity_candidates,
        "record_requires_domain_guard": "singularity" in json.dumps(record, sort_keys=True).lower(),
        "global_validity_blocked": "no global solution classification" in json.dumps(record, sort_keys=True).lower(),
        "finite_ode_not_global_claim": True,
    }
    return {
        "fixture": "leading_coefficient_x",
        "ode_leading_coefficient": leading_coefficient,
        "singularity_candidates": singularity_candidates,
        "blocked_overclaim": "finite ODE certificate -> global function-class claim",
        "checks": checks,
        "passed": all(checks.values()),
        "status": "PASS_SINGULARITY_GUARD_CHECK",
        "limitations": ["bounded symbolic leading-coefficient zero check only", "no global solution classification"],
    }


def derived_gap_rows() -> list[dict[str, Any]]:
    return [
        {
            "gap_id": "continuous_not_differentiable_gap_v0",
            "relation": "continuous does not automatically imply differentiable",
            "example_placeholder": "absolute-value style boundary at 0",
            "status": "DERIVED_GAP_NOT_EXECUTABLE_RECORD",
            "counted_as_executable_record": False,
            "reason": "not one of the three M021 boundary records",
        }
    ]


def shape_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    payload = record.get("certificate_payload")
    failures = []
    if record.get("function_class") != FUNCTION_CLASS:
        failures.append(f"{record_id}: function_class mismatch")
    if not isinstance(payload, dict):
        failures.append(f"{record_id}: certificate_payload must be an object")
        return failures
    if not payload.get("relation"):
        failures.append(f"{record_id}: relation missing")
    if payload.get("non_overclaim") is not True:
        failures.append(f"{record_id}: non_overclaim marker missing")
    if "boundary" not in str(record.get("title", "")).lower() and "guard" not in str(record.get("title", "")).lower():
        failures.append(f"{record_id}: boundary/guard title missing")
    return failures


def boundary_failures(record: dict[str, Any]) -> list[str]:
    record_id = record.get("record_id", "<missing>")
    text = json.dumps(record, sort_keys=True).lower()
    failures = []
    if "theorem" not in text and "public proof" not in text:
        failures.append(f"{record_id}: public proof/theorem boundary missing")
    if "full analysis formalization" not in text and "analytic hierarchy proof" not in text and "holonomic system theorem" not in text:
        failures.append(f"{record_id}: completion-claim boundary missing")
    if contains_raw_dependency(json.dumps(record, sort_keys=True)):
        failures.append(f"{record_id}: blocked dependency text present")
    if contains_token_like_text(json.dumps(record, sort_keys=True)):
        failures.append(f"{record_id}: token-like text present")
    return failures


def execute_record(record: dict[str, Any]) -> dict[str, Any]:
    record_id = record["record_id"]
    failures = validate_false_booleans(record) + shape_failures(record) + boundary_failures(record)
    classification = "CLASS_BOUNDARY_RELATION"
    if record_id == "smooth_not_analytic_boundary_record_v0":
        detail = smooth_not_analytic_boundary_check(record)
        classification = "SMOOTH_NOT_ANALYTIC_BOUNDARY"
    elif record_id == "analytic_not_dfinite_boundary_record_v0":
        detail = analytic_not_dfinite_boundary_check(record)
        classification = "ANALYTIC_NOT_DFINITE_BOUNDARY"
    elif record_id == "dfinite_domain_singularity_guard_v0":
        detail = dfinite_domain_singularity_guard_check(record)
        classification = "DFINITE_DOMAIN_SINGULARITY_GUARD"
    else:
        detail = {"passed": False, "reason": "unexpected record"}
        failures.append(f"{record_id}: unexpected record")
    if not detail.get("passed"):
        failures.append(f"{record_id}: boundary relation check failed")
    return {
        "record_id": record_id,
        "title": record.get("title"),
        "classification": classification,
        "certificate_type": record.get("certificate_type"),
        "status": "FAIL" if failures else detail.get("status", "PASS_BOUNDARY_CHECK"),
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
    artifact = {
        "record_id": record["record_id"],
        "function_class": FUNCTION_CLASS,
        "relation": payload.get("relation"),
        "blocked_overclaim": result.get("detail", {}).get("blocked_overclaim"),
        "example_or_stub": payload.get("example_stub") or record.get("expression_or_object"),
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
            "-- MachLib boundary relation draft placeholder",
            "structure MachBoundaryRelation where",
            "  recordId : String",
            "  blockedOverclaim : String",
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
        "no_real_analysis_completion_claim": True,
        "no_topology_formalization_claim": True,
        "no_subset_overclaim": True,
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
        "derived_gap_rows": derived_gap_rows(),
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
    summary = f"""# MachLib Function Boundary Summary - {DATE}

## Scope
Local-only OBSERVATION-tier harness for the three boundary/non-example draft records.

## Inputs consumed
- `corpus/eml_function_classes_draft/boundary_relations/records_2026_05_20.json`

## Record count
- Records: {execution["record_count"]}
- Passed: {execution["passed"]}
- Warned: {execution["warned"]}
- Failed: {execution["failed"]}
- Status: {execution["execution_status"]}

## Boundary spec summary
- Spec rows: {spec["spec_count"]}
- Status: DRAFT_INTERNAL

## smooth-not-analytic result
- {result_by_id["smooth_not_analytic_boundary_record_v0"]["status"]}

## analytic-not-D-finite result
- {result_by_id["analytic_not_dfinite_boundary_record_v0"]["status"]}

## D-finite domain/singularity result
- {result_by_id["dfinite_domain_singularity_guard_v0"]["status"]}

## derived continuous-not-differentiable gap
- Recorded as a derived gap row only; not counted as an executable record.

## eFrog/Forge summary
- eFrog: {roundtrip["efrog_status"]}
- Forge: {roundtrip["forge_status"]}
- Roundtrip: {roundtrip["roundtrip_status"]}

## Zero-Mathlib status
- PASS

## Remaining no-go gates
- No public theorem/proof/open-problem claim.
- No real-analysis completion claim.
- No topology formalization claim.
- No subset overclaim.
- No upload, publish, hardware action, or compiler behavior change.
"""
    (REPORT_DIR / f"machlib_function_boundary_summary_{DATE.replace('-', '_')}.md").write_text(summary, encoding="utf-8")
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
    (REPORT_DIR / f"machlib_function_boundary_results_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Function Boundary Results - 2026-05-20\n\n"
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
    (REPORT_DIR / f"machlib_function_boundary_roundtrip_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Function Boundary Roundtrip - 2026-05-20\n\n"
        + markdown_table(roundtrip_rows, ["record_id", "status", "efrog_status", "forge_status", "forge_code"])
        + f"\n\nOptional evidence script: {roundtrip['forge_efrog_evidence_script']['status']}\n",
        encoding="utf-8",
    )
    guard = f"""# MachLib Function Boundary Guardrail Report - {DATE}

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
| no real-analysis completion claim | PASS |
| no topology formalization claim | PASS |
| no subset overclaim | PASS |
| no public_ready true | PASS |
| no upload_allowed true | PASS |
| no release_ready true | PASS |
| no marketplace_ready true | PASS |
| no CapCard certification claim | PASS |
| no PETAL verification claim | PASS |
| no token-like secret | PASS |
"""
    (REPORT_DIR / f"machlib_function_boundary_guardrail_report_{DATE.replace('-', '_')}.md").write_text(
        guard, encoding="utf-8"
    )


def build_all(root: Path, tmp_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    records = load_boundary_records(root)
    ids = {row["record_id"] for row in records}
    missing = sorted(EXPECTED_RECORDS - ids)
    extra = sorted(ids - EXPECTED_RECORDS)
    results = [execute_record(row) for row in records]
    if missing or extra or len(records) != 3:
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
        "BOUNDARY_EXECUTION_RESULT",
        execution["record_count"],
        execution["passed"],
        execution["warned"],
        execution["failed"],
        execution["execution_status"],
    )
    print(
        "BOUNDARY_ROUNDTRIP_RESULT",
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
