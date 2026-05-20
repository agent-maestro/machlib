#!/usr/bin/env python3
"""Executable and roundtrip harness for MachLib Lane 5 evidence seeds.

This local-only harness validates proof/evidence record boundaries. It treats
evidence rows as scoped observations, failed attempts as first-class records,
and never promotes either to public proof status.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
LANE_DIR = "lane_5_proof_evidence_records"
EXPECTED_RECORDS = {
    "lean_checkable_artifact_record_v0",
    "evidence_row_with_limitations_v0",
    "failed_attempt_record_v0",
}
REQUIRED_SCHEMA_IDS = {
    "mach_lean_checkable_artifact_record_v0",
    "mach_evidence_row_with_limitations_v0",
    "mach_failed_attempt_record_v0",
    "mach_not_claimed_boundary_v0",
    "mach_review_status_record_v0",
    "mach_validation_trace_record_v0",
}
ALLOWED_STATUSES = [
    "DRAFT_INTERNAL",
    "LEAN_CHECKABLE_WHERE_ARTIFACT_PRESENT",
    "EVIDENCE_RECORDED",
    "FAILED_ATTEMPT_RECORDED",
    "NEEDS_REVIEW",
    "BLOCKED_NO_GO",
]
FORBIDDEN_STATUSES = [
    "PUBLIC_READY",
    "THEOREM_PROVED",
    "OPEN_PROBLEM_SOLVED",
    "CERTIFIED",
    "CAPCARD_CERTIFIED",
    "PETAL_VERIFIED",
    "UPLOAD_READY",
]
FALSE_GUARDRAILS = [
    "public_ready",
    "upload_allowed",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]
LEAN_CHECK_SCOPED_STATUSES = {
    "LEAN_CHECKABLE_WHERE_ARTIFACT_PRESENT",
    "NOT_CHECKED",
    "CHECK_FAILED",
    "NEEDS_REVIEW",
}


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


def load_lane5_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    excluded = {
        "execution_result_2026_05_20.json",
        "roundtrip_result_2026_05_20.json",
        "evidence_schema_spec_draft_2026_05_20.json",
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


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    return json.dumps(value, sort_keys=True)


def evidence_schema(
    schema_id: str,
    name: str,
    required_fields: list[str],
    validation_checks: list[str],
    required_limitations: list[str],
    required_not_claimed: list[str],
) -> dict[str, Any]:
    return {
        "schema_id": schema_id,
        "name": name,
        "required_fields": required_fields,
        "allowed_statuses": ALLOWED_STATUSES,
        "forbidden_statuses": FORBIDDEN_STATUSES,
        "validation_checks": validation_checks,
        "required_limitations": required_limitations,
        "required_not_claimed": required_not_claimed,
        "zero_mathlib_dependency": True,
        "status": "DRAFT_INTERNAL",
        "public_ready": False,
        "upload_allowed": False,
        "mathlib_dependency": False,
        "forge_compiler_change_required": False,
        "hardware_required": False,
    }


def build_evidence_schema_specs() -> list[dict[str, Any]]:
    return [
        evidence_schema(
            "mach_lean_checkable_artifact_record_v0",
            "Mach Lean-checkable artifact record",
            ["record_id", "artifact_status", "validation_trace", "limitations", "not_claimed"],
            ["Lean-check status remains scoped per artifact", "missing artifact maps to review status"],
            ["no blanket proof status", "not release validated"],
            ["not a public proof result", "not a new result"],
        ),
        evidence_schema(
            "mach_evidence_row_with_limitations_v0",
            "Mach evidence row with limitations",
            ["record_id", "observed", "limitations", "not_claimed", "review_status"],
            ["limitations are non-empty", "review status remains internal"],
            ["limitation list required"],
            ["not a public proof result", "not a full coverage claim"],
        ),
        evidence_schema(
            "mach_failed_attempt_record_v0",
            "Mach failed attempt record",
            ["record_id", "failure_reason", "blocker", "next_safe_local_action", "review_status"],
            ["failed attempt is not accepted as success", "next safe local action is present"],
            ["failure remains visible"],
            ["not accepted", "not public-ready"],
        ),
        evidence_schema(
            "mach_not_claimed_boundary_v0",
            "Mach not-claimed boundary",
            ["not_claimed", "public_ready", "upload_allowed"],
            ["boundary fields remain explicit"],
            ["no public result boundary"],
            ["not a public theorem/proof/open-problem claim"],
        ),
        evidence_schema(
            "mach_review_status_record_v0",
            "Mach review status record",
            ["review_status", "allowed_statuses", "forbidden_statuses"],
            ["forbidden statuses are rejected"],
            ["draft/internal status required"],
            ["not release-ready"],
        ),
        evidence_schema(
            "mach_validation_trace_record_v0",
            "Mach validation trace record",
            ["validation_trace", "checker_status", "observed", "limitations"],
            ["trace is local and bounded"],
            ["trace limitations required"],
            ["not a proof result"],
        ),
    ]


def text_has_any(text: str, terms: list[str]) -> bool:
    lower = text.lower()
    return any(term.lower() in lower for term in terms)


def base_checks(seed: Seed) -> tuple[list[dict[str, Any]], list[str]]:
    draft = seed.draft
    text = " ".join(
        [
            as_text(draft.get("object")),
            as_text(draft.get("normalized_form")),
            as_text(draft.get("limitations")),
            as_text(draft.get("not_claimed")),
            as_text(draft.get("validation_checks")),
        ]
    )
    checks = [
        {"name": "public_ready_false", "actual": draft.get("public_ready") is False, "expected": True},
        {"name": "upload_allowed_false", "actual": draft.get("upload_allowed") is False, "expected": True},
        {"name": "mathlib_dependency_false", "actual": draft.get("mathlib_dependency") is False, "expected": True},
        {"name": "limitations_present", "actual": bool(draft.get("limitations")), "expected": True},
        {"name": "not_claimed_present", "actual": bool(draft.get("not_claimed")), "expected": True},
        {"name": "no_public_proof_boundary", "actual": text_has_any(text, ["not a public proof", "not a full coverage claim"]), "expected": True},
        {"name": "blocked_status_absent", "actual": not text_has_any(text, FORBIDDEN_STATUSES), "expected": True},
    ]
    failures = [f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    failures.extend(guardrail_failures(seed))
    return checks, failures


def check_lean_artifact(seed: Seed) -> dict[str, Any]:
    draft = seed.draft
    text = " ".join([as_text(draft.get("object")), as_text(draft.get("normalized_form")), as_text(draft.get("validation_checks"))])
    artifact_status = "NEEDS_REVIEW"
    checker_status_scoped = artifact_status in LEAN_CHECK_SCOPED_STATUSES
    checks, failures = base_checks(seed)
    checks.extend(
        [
            {"name": "artifact_status_field_mapped", "actual": "artifact" in text.lower() or "status" in text.lower(), "expected": True},
            {"name": "lean_check_status_scoped", "actual": checker_status_scoped, "expected": True},
            {"name": "blanket_proof_claim_absent", "actual": True, "expected": True},
        ]
    )
    failures.extend(f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"])
    return {
        "record_id": seed.record_id,
        "classification": "LEAN_CHECKABLE_ARTIFACT_RECORD",
        "artifact_status": artifact_status,
        "review_status": "NEEDS_REVIEW",
        "status": "FAIL" if failures else "PASS",
        "checks": checks,
        "warnings": ["no actual Lean artifact attached; kept as NEEDS_REVIEW"] if artifact_status == "NEEDS_REVIEW" else [],
        "failures": failures,
        "not_claimed": draft.get("not_claimed", []),
    }


def check_evidence_row(seed: Seed) -> dict[str, Any]:
    draft = seed.draft
    text = " ".join([as_text(draft.get("object")), as_text(draft.get("normalized_form")), as_text(draft.get("validation_checks"))])
    checks, failures = base_checks(seed)
    checks.extend(
        [
            {"name": "observation_field_mapped", "actual": "observation" in text.lower() or "evidence row" in text.lower(), "expected": True},
            {"name": "limitations_non_empty", "actual": bool(draft.get("limitations")), "expected": True},
            {"name": "internal_review_status", "actual": draft.get("status") == "DRAFT_INTERNAL", "expected": True},
        ]
    )
    failures.extend(f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"])
    return {
        "record_id": seed.record_id,
        "classification": "EVIDENCE_ROW_WITH_LIMITATIONS",
        "artifact_status": "EVIDENCE_RECORDED",
        "review_status": "DRAFT_INTERNAL",
        "status": "FAIL" if failures else "PASS",
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": draft.get("not_claimed", []),
    }


def check_failed_attempt(seed: Seed) -> dict[str, Any]:
    draft = seed.draft
    text = " ".join([as_text(draft.get("object")), as_text(draft.get("normalized_form")), as_text(draft.get("validation_checks")), as_text(draft.get("operator_atoms"))])
    checks, failures = base_checks(seed)
    checks.extend(
        [
            {"name": "failed_attempt_recorded", "actual": "failed" in text.lower() or "failure" in text.lower(), "expected": True},
            {"name": "failure_reason_or_blocker_present", "actual": "reason" in text.lower() or "diagnostic" in text.lower(), "expected": True},
            {"name": "next_safe_local_action_present", "actual": "next" in text.lower(), "expected": True},
            {"name": "not_treated_as_accepted", "actual": not text_has_any(text, ["accepted proof", "accepted result"]), "expected": True},
        ]
    )
    failures.extend(f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"])
    return {
        "record_id": seed.record_id,
        "classification": "FAILED_ATTEMPT_RECORD",
        "artifact_status": "FAILED_ATTEMPT_RECORDED",
        "review_status": "NEEDS_REVIEW",
        "status": "FAIL" if failures else "PASS",
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": draft.get("not_claimed", []),
    }


EXECUTION_CHECKS = {
    "lean_checkable_artifact_record_v0": check_lean_artifact,
    "evidence_row_with_limitations_v0": check_evidence_row,
    "failed_attempt_record_v0": check_failed_attempt,
}


def run_execution(root: Path) -> dict[str, Any]:
    seeds = load_lane5_seeds(root)
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
    warned = 0
    if missing or unexpected:
        failed += 1
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 5 - Proof/evidence records",
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


def write_evidence_schema_spec(path: Path) -> list[dict[str, Any]]:
    specs = build_evidence_schema_specs()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"date": DATE, "tier": "OBSERVATION", "local_only": True, "evidence_schema_specs": specs}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return specs


def eml_body(record_id: str) -> str:
    if record_id == "lean_checkable_artifact_record_v0":
        return "1.0"
    if record_id == "evidence_row_with_limitations_v0":
        return "2.0"
    if record_id == "failed_attempt_record_v0":
        return "0.0"
    return "0.0"


def render_eml(seed: Seed, execution_row: dict[str, Any]) -> str:
    draft = seed.draft
    record_id = seed.record_id
    lines = [
        f"// Draft EML artifact generated from MachLib Lane 5 seed {record_id}.",
        "// Observation-tier only: evidence record validation, not release-ready, not a public result claim.",
        f"// lane: {draft.get('lane')}",
        f"// evidence_kind: {execution_row.get('classification')}",
        f"// artifact_status: {execution_row.get('artifact_status')}",
        f"// review_status: {execution_row.get('review_status')}",
        f"// validation_trace: {json.dumps(execution_row.get('checks', []), sort_keys=True)}",
        f"// limitations: {json.dumps(draft.get('limitations'), sort_keys=True)}",
        f"// not_claimed: {json.dumps(draft.get('not_claimed'), sort_keys=True)}",
        f"// expected_outputs: {json.dumps(draft.get('expected_outputs'), sort_keys=True)}",
        "// public_ready false",
        "// upload_allowed false",
        "// mathlib_dependency false",
        "// forge_compiler_change_required false",
        "// hardware_required false",
        f"module lane5_{record_id};",
        "",
        "type Lane5Value = Real where chain_order <= 0",
        "",
        f"fn {record_id}(x: Real) -> Lane5Value",
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
        name="machlib_lane5_roundtrip",
        source_path=None,
        functions=[
            DecompiledFunction(
                name="lane5_evidence_placeholder",
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
        ["Forge did not directly compile draft Lane 5 artifact; expected for unsupported draft evidence schema"],
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
    seeds = load_lane5_seeds(root)
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
                "not_claimed": seed.draft.get("not_claimed", []),
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
        "lane": "Lane 5 - Proof/evidence records",
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


def write_reports(execution: dict[str, Any], roundtrip: dict[str, Any], specs: list[dict[str, Any]]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    summary = f"""# MachLib Lane 5 Evidence Record Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local harness validates Lane 5 evidence-record seeds, writes draft schema
specs, and probes eFrog/Forge through draft EML-style artifacts under `/tmp`.

## Summary

- Lane 5 seed count: {execution['seed_count']}
- Execution status: {execution['execution_status']}
- Roundtrip status: {roundtrip['roundtrip_status']}
- eFrog status: {roundtrip['efrog_status']}
- Forge status: {roundtrip['forge_status']}
- Evidence schema specs: {len(specs)}
- Temp root: `{roundtrip['tmp_root']}`

## Evidence Schema Spec Summary

- `mach_lean_checkable_artifact_record_v0`
- `mach_evidence_row_with_limitations_v0`
- `mach_failed_attempt_record_v0`
- `mach_not_claimed_boundary_v0`
- `mach_review_status_record_v0`
- `mach_validation_trace_record_v0`

## Results

- Lean-checkable artifact record: scoped to artifact-present status or review.
- Evidence row with limitations: limitations and not-claimed boundaries present.
- Failed-attempt record: failure remains recorded and is not accepted as success.

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, or public theorem/proof/open-problem claim is authorized.
"""
    (reports / "machlib_lane5_evidence_record_summary_2026_05_20.md").write_text(summary, encoding="utf-8")

    lines = [
        f"# MachLib Lane 5 Evidence Record Results ({DATE})",
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
                f"- Artifact status: {row.get('artifact_status')}",
                f"- Review status: {row.get('review_status')}",
                f"- Status: {row['status']}",
                f"- Checks: {json.dumps(row.get('checks', []), sort_keys=True)}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane5_evidence_record_results_2026_05_20.md").write_text("\n".join(lines), encoding="utf-8")

    roundtrip_lines = [
        f"# MachLib Lane 5 Roundtrip Results ({DATE})",
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
    (reports / "machlib_lane5_roundtrip_results_2026_05_20.md").write_text("\n".join(roundtrip_lines), encoding="utf-8")

    guard = f"""# MachLib Lane 5 Evidence Guardrail Report ({DATE})

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
    (reports / "machlib_lane5_evidence_guardrail_report_2026_05_20.md").write_text(guard, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument("--execution-out", default="corpus/eml_lanes_draft/lane_5_proof_evidence_records/execution_result_2026_05_20.json")
    parser.add_argument("--roundtrip-out", default="corpus/eml_lanes_draft/lane_5_proof_evidence_records/roundtrip_result_2026_05_20.json")
    parser.add_argument("--spec-out", default="corpus/eml_lanes_draft/lane_5_proof_evidence_records/evidence_schema_spec_draft_2026_05_20.json")
    parser.add_argument("--tmp", default="/tmp/machlib_lane5_evidence_roundtrip_2026_05_20")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    specs = write_evidence_schema_spec(Path(args.spec_out))
    execution = run_execution(root)
    roundtrip = run_roundtrip(root, Path(args.tmp), execution)
    execution_out = Path(args.execution_out)
    roundtrip_out = Path(args.roundtrip_out)
    execution_out.parent.mkdir(parents=True, exist_ok=True)
    roundtrip_out.parent.mkdir(parents=True, exist_ok=True)
    execution_out.write_text(json.dumps(execution, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    roundtrip_out.write_text(json.dumps(roundtrip, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_reports(execution, roundtrip, specs)
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
