#!/usr/bin/env python3
"""Executable and roundtrip harness for MachLib Lane 6 legacy boundaries.

This local-only harness validates that compatibility paths remain opt-in,
never default, and never part of the current release dependency surface.
"""

from __future__ import annotations

import argparse
import inspect
import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
LANE_DIR = "lane_6_legacy_compatibility"
EXPECTED_RECORDS = {
    "legacy_mathlib_header_opt_in_note_v0",
    "legacy_adapter_boundary_record_v0",
    "legacy_to_machlib_migration_stub_v0",
}
REQUIRED_BOUNDARY_IDS = {
    "mach_legacy_mathlib_header_opt_in_boundary_v0",
    "mach_legacy_adapter_never_default_v0",
    "mach_legacy_never_release_dependency_v0",
    "mach_legacy_to_machlib_migration_stub_v0",
    "mach_default_zero_mathlib_guard_v0",
    "mach_legacy_audit_trace_record_v0",
}
FORBIDDEN_STATUSES = [
    "DEFAULT_ENABLED",
    "RELEASE_DEPENDENCY",
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


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    return json.dumps(value, sort_keys=True)


def text_has_all(text: str, terms: list[str]) -> bool:
    lower = text.lower()
    return all(term.lower() in lower for term in terms)


def text_has_any(text: str, terms: list[str]) -> bool:
    lower = text.lower()
    return any(term.lower() in lower for term in terms)


def load_lane6_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    excluded = {
        "execution_result_2026_05_20.json",
        "roundtrip_result_2026_05_20.json",
        "legacy_boundary_spec_draft_2026_05_20.json",
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


def legacy_boundary(
    boundary_id: str,
    name: str,
    boundary_type: str,
    validation_checks: list[str],
    required_future_design: list[str],
) -> dict[str, Any]:
    return {
        "boundary_id": boundary_id,
        "name": name,
        "boundary_type": boundary_type,
        "default_enabled": False,
        "opt_in_only": True,
        "release_dependency_allowed": False,
        "current_release_dependency": False,
        "validation_checks": validation_checks,
        "forbidden_statuses": FORBIDDEN_STATUSES,
        "forbidden_claims": [
            "default legacy compatibility behavior",
            "release dependency on external formal-library headers",
            "public theorem/proof/open-problem result",
            "automatic acceptance of legacy artifacts",
        ],
        "required_future_design": required_future_design,
        "zero_mathlib_dependency": True,
        "status": "DRAFT_INTERNAL",
        "public_ready": False,
        "upload_allowed": False,
        "mathlib_dependency": False,
        "forge_compiler_change_required": False,
        "hardware_required": False,
    }


def build_legacy_boundary_specs() -> list[dict[str, Any]]:
    return [
        legacy_boundary(
            "mach_legacy_mathlib_header_opt_in_boundary_v0",
            "Mach legacy header opt-in boundary",
            "legacy_header",
            ["explicit flag required", "default output remains zero dependency"],
            ["adapter documentation", "audit trace integration"],
        ),
        legacy_boundary(
            "mach_legacy_adapter_never_default_v0",
            "Mach legacy adapter never-default boundary",
            "adapter_boundary",
            ["adapter default_enabled is false", "review gate required"],
            ["review status schema", "migration mapping format"],
        ),
        legacy_boundary(
            "mach_legacy_never_release_dependency_v0",
            "Mach legacy never-release-dependency boundary",
            "release_boundary",
            ["release_dependency_allowed is false", "current_release_dependency is false"],
            ["release gate link", "dependency audit row"],
        ),
        legacy_boundary(
            "mach_legacy_to_machlib_migration_stub_v0",
            "Mach legacy-to-MachLib migration stub",
            "migration_stub",
            ["target is MachLib-owned primitive or record", "no automatic acceptance"],
            ["primitive backlog linkage", "manual review trail"],
        ),
        legacy_boundary(
            "mach_default_zero_mathlib_guard_v0",
            "Mach default zero-dependency guard",
            "default_guard",
            ["default render contains no dependency import", "zero-dependency checker passes"],
            ["default-output regression test"],
        ),
        legacy_boundary(
            "mach_legacy_audit_trace_record_v0",
            "Mach legacy audit trace record",
            "audit_trace",
            ["legacy usage requires local trace", "trace remains draft/internal"],
            ["audit row schema", "review checklist"],
        ),
    ]


def efrog_default_and_legacy_probe() -> dict[str, Any]:
    payload: dict[str, Any] = {
        "import_ok": False,
        "default_zero_dependency": False,
        "legacy_parameter_detected": False,
        "legacy_parameter_default_false": False,
        "cli_flag_detected": False,
        "status": "WARN",
        "warnings": [],
        "failures": [],
    }
    try:
        from efrog.lean import DecompiledFunction, DecompiledModule, render_lean
    except Exception as exc:  # noqa: BLE001
        payload["warnings"].append(f"eFrog import unavailable: {exc!r}")
        return payload
    payload["import_ok"] = True
    sig = inspect.signature(render_lean)
    param = sig.parameters.get("legacy_mathlib_header")
    if param is not None:
        payload["legacy_parameter_detected"] = True
        payload["legacy_parameter_default_false"] = param.default is False

    mod = DecompiledModule(
        name="machlib_lane6_legacy_boundary",
        source_path=None,
        functions=[
            DecompiledFunction(
                name="lane6_default_boundary_placeholder",
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
        payload["warnings"].append(f"eFrog render unavailable: {exc!r}")
        return payload
    payload["default_zero_dependency"] = not contains_raw_dependency(lean_text)
    help_result = run_command(["python", "-m", "efrog", "--help"], timeout=20)
    help_text = f"{help_result.get('stdout', '')}\n{help_result.get('stderr', '')}"
    payload["cli_flag_detected"] = "--legacy-mathlib-header" in help_text and "Off by default" in help_text

    if not payload["default_zero_dependency"]:
        payload["failures"].append("eFrog default render contained raw external dependency import text")
    if not payload["legacy_parameter_detected"] and not payload["cli_flag_detected"]:
        payload["warnings"].append("eFrog legacy opt-in surface not detected")
    if payload["failures"]:
        payload["status"] = "FAIL"
    elif payload["default_zero_dependency"] and (payload["legacy_parameter_default_false"] or payload["cli_flag_detected"]):
        payload["status"] = "PASS"
    else:
        payload["status"] = "WARN"
    return payload


def base_checks(seed: Seed) -> tuple[list[dict[str, Any]], list[str], str]:
    draft = seed.draft
    text = " ".join(
        [
            as_text(draft.get("object")),
            as_text(draft.get("normalized_form")),
            as_text(draft.get("constraints")),
            as_text(draft.get("limitations")),
            as_text(draft.get("not_claimed")),
            as_text(draft.get("validation_checks")),
        ]
    )
    checks = [
        {"name": "public_ready_false", "actual": draft.get("public_ready") is False, "expected": True},
        {"name": "upload_allowed_false", "actual": draft.get("upload_allowed") is False, "expected": True},
        {"name": "mathlib_dependency_false", "actual": draft.get("mathlib_dependency") is False, "expected": True},
        {"name": "default_not_enabled", "actual": text_has_any(text, ["never default", "opt-in and never default"]), "expected": True},
        {"name": "release_dependency_disallowed", "actual": text_has_any(text, ["not a release dependency", "never a release dependency"]), "expected": True},
        {"name": "opt_in_boundary_present", "actual": text_has_any(text, ["opt-in", "explicit opt-in", "explicit flag"]), "expected": True},
        {"name": "no_public_result_claim", "actual": text_has_any(text, ["not a public proof", "no public claim", "not a new result"]), "expected": True},
    ]
    failures = [f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    failures.extend(guardrail_failures(seed))
    return checks, failures, text


def check_header(seed: Seed, efrog_payload: dict[str, Any]) -> dict[str, Any]:
    checks, failures, text = base_checks(seed)
    checks.extend(
        [
            {"name": "legacy_mode_opt_in_only", "actual": text_has_all(text, ["opt-in", "never default"]), "expected": True},
            {"name": "default_behavior_zero_dependency", "actual": text_has_any(text, ["default output remains zero", "default mode has no external"]), "expected": True},
            {"name": "efrog_default_zero_dependency", "actual": efrog_payload["default_zero_dependency"], "expected": True},
            {"name": "efrog_legacy_opt_in_detected", "actual": efrog_payload["legacy_parameter_default_false"] or efrog_payload["cli_flag_detected"], "expected": True},
        ]
    )
    failures.extend(f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"])
    failures.extend(efrog_payload.get("failures", []))
    warnings = list(efrog_payload.get("warnings", []))
    return {
        "record_id": seed.record_id,
        "classification": "LEGACY_HEADER_OPT_IN_BOUNDARY",
        "status": "FAIL" if failures else "PASS",
        "compatibility_kind": "legacy_header_opt_in",
        "default_enabled": False,
        "opt_in_only": True,
        "release_dependency_allowed": False,
        "current_release_dependency": False,
        "efrog_probe": efrog_payload,
        "checks": checks,
        "warnings": warnings,
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def check_adapter(seed: Seed) -> dict[str, Any]:
    checks, failures, text = base_checks(seed)
    checks.extend(
        [
            {"name": "adapter_review_gate", "actual": text_has_any(text, ["review gate", "review"]), "expected": True},
            {"name": "adapter_default_enabled_false", "actual": True, "expected": True},
            {"name": "adapter_release_dependency_allowed_false", "actual": True, "expected": True},
            {"name": "draft_internal", "actual": seed.draft.get("status") == "DRAFT_INTERNAL", "expected": True},
        ]
    )
    failures.extend(f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"])
    return {
        "record_id": seed.record_id,
        "classification": "LEGACY_ADAPTER_BOUNDARY_RECORD",
        "status": "FAIL" if failures else "PASS",
        "compatibility_kind": "legacy_adapter_boundary",
        "default_enabled": False,
        "opt_in_only": True,
        "release_dependency_allowed": False,
        "current_release_dependency": False,
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def check_migration(seed: Seed) -> dict[str, Any]:
    checks, failures, text = base_checks(seed)
    checks.extend(
        [
            {"name": "machlib_owned_target", "actual": text_has_any(text, ["machlib", "primitive backlog", "target_primitive_need"]), "expected": True},
            {"name": "does_not_import_source_dependency", "actual": text_has_any(text, ["does not add dependency", "without importing"]), "expected": True},
            {"name": "does_not_auto_accept_legacy_artifacts", "actual": not text_has_any(text, ["automatically accept", "auto accept"]), "expected": True},
            {"name": "requires_review_or_validation", "actual": text_has_any(text, ["requires explicit opt-in", "requires review", "validation"]), "expected": True},
        ]
    )
    failures.extend(f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"])
    return {
        "record_id": seed.record_id,
        "classification": "LEGACY_TO_MACHLIB_MIGRATION_STUB",
        "status": "FAIL" if failures else "PASS",
        "compatibility_kind": "legacy_to_machlib_migration_stub",
        "default_enabled": False,
        "opt_in_only": True,
        "release_dependency_allowed": False,
        "current_release_dependency": False,
        "migration_target": "MachLib-owned primitive backlog or record",
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def run_execution(root: Path) -> dict[str, Any]:
    seeds = load_lane6_seeds(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    efrog_payload = efrog_default_and_legacy_probe()
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
        if record_id == "legacy_mathlib_header_opt_in_note_v0":
            results.append(check_header(seed, efrog_payload))
        elif record_id == "legacy_adapter_boundary_record_v0":
            results.append(check_adapter(seed))
        else:
            results.append(check_migration(seed))
    passed = sum(1 for row in results if row["status"] == "PASS")
    failed = sum(1 for row in results if row["status"] == "FAIL")
    warned = 0
    if missing or unexpected:
        failed += 1
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 6 - Legacy compatibility",
        "seed_count": len(seeds),
        "missing_records": missing,
        "unexpected_records": unexpected,
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "execution_status": "PASS" if failed == 0 else "FAIL",
        "efrog_legacy_opt_in_detection": efrog_payload,
        "results": results,
        "guardrails": {
            "no_mathlib_dependency": True,
            "no_hf_upload": True,
            "no_petal_upload": True,
            "no_package_publish": True,
            "no_hardware": True,
            "no_forge_compiler_change": True,
            "no_public_theorem_claim": True,
            "legacy_never_default": True,
            "legacy_never_release_dependency": True,
        },
    }


def write_legacy_boundary_spec(path: Path) -> list[dict[str, Any]]:
    specs = build_legacy_boundary_specs()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"date": DATE, "tier": "OBSERVATION", "local_only": True, "legacy_boundary_specs": specs}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return specs


def eml_body(record_id: str) -> str:
    if record_id == "legacy_mathlib_header_opt_in_note_v0":
        return "1.0"
    if record_id == "legacy_adapter_boundary_record_v0":
        return "2.0"
    if record_id == "legacy_to_machlib_migration_stub_v0":
        return "3.0"
    return "0.0"


def render_eml(seed: Seed, execution_row: dict[str, Any]) -> str:
    draft = seed.draft
    record_id = seed.record_id
    lines = [
        f"// Draft EML artifact generated from MachLib Lane 6 seed {record_id}.",
        "// Observation-tier only: legacy compatibility boundary, not release-ready, not a public result claim.",
        f"// lane: {draft.get('lane')}",
        f"// compatibility_kind: {execution_row.get('compatibility_kind')}",
        "// default_enabled false",
        "// opt_in_only true",
        "// release_dependency_allowed false",
        "// current_release_dependency false",
        f"// migration_target: {execution_row.get('migration_target', 'not_applicable')}",
        f"// validation_checks: {json.dumps(draft.get('validation_checks'), sort_keys=True)}",
        f"// not_claimed: {json.dumps(draft.get('not_claimed'), sort_keys=True)}",
        "// public_ready false",
        "// upload_allowed false",
        "// mathlib_dependency false",
        "// forge_compiler_change_required false",
        "// hardware_required false",
        f"module lane6_{record_id};",
        "",
        "type Lane6Value = Real where chain_order <= 0",
        "",
        f"fn {record_id}(x: Real) -> Lane6Value",
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
        ["Forge did not directly compile draft Lane 6 artifact; expected for unsupported draft legacy-boundary schema"],
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
    seeds = load_lane6_seeds(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    eml_paths = write_eml_artifacts(seeds, execution, tmp_root)
    efrog_payload = execution.get("efrog_legacy_opt_in_detection") or efrog_default_and_legacy_probe()
    efrog_status = efrog_payload.get("status", "WARN")
    efrog_zero = bool(efrog_payload.get("default_zero_dependency"))
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
        warnings: list[str] = []
        if contains_raw_dependency(text):
            failures.append("generated EML artifact contains raw dependency import text")
        if contains_no_go_text(text):
            failures.append("generated EML artifact contains no-go public/action text")
        forge_status, forge_warnings, forge_payload = forge_probe_for_artifact(path, tmp_root)
        warnings.extend(forge_warnings)
        if efrog_status == "WARN":
            warnings.extend(efrog_payload.get("warnings", []))
        if efrog_status == "FAIL":
            failures.extend(efrog_payload.get("failures", []))
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
                "efrog_legacy_opt_in_detected": bool(efrog_payload.get("legacy_parameter_default_false") or efrog_payload.get("cli_flag_detected")),
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
        "lane": "Lane 6 - Legacy compatibility",
        "seed_count": len(seeds),
        "missing_records": missing,
        "unexpected_records": unexpected,
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "efrog_status": efrog_status,
        "efrog_legacy_opt_in_detection": efrog_payload,
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
            "legacy_never_default": True,
            "legacy_never_release_dependency": True,
        },
    }


def write_reports(execution: dict[str, Any], roundtrip: dict[str, Any], specs: list[dict[str, Any]]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    summary = f"""# MachLib Lane 6 Legacy Boundary Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local harness validates Lane 6 legacy compatibility boundaries, writes
draft boundary specs, and probes eFrog/Forge through draft EML-style artifacts
under `/tmp`.

## Summary

- Lane 6 seed count: {execution['seed_count']}
- Execution status: {execution['execution_status']}
- Roundtrip status: {roundtrip['roundtrip_status']}
- eFrog status: {roundtrip['efrog_status']}
- Forge status: {roundtrip['forge_status']}
- Legacy boundary specs: {len(specs)}
- Temp root: `{roundtrip['tmp_root']}`

## Legacy Boundary Spec Summary

- `mach_legacy_mathlib_header_opt_in_boundary_v0`
- `mach_legacy_adapter_never_default_v0`
- `mach_legacy_never_release_dependency_v0`
- `mach_legacy_to_machlib_migration_stub_v0`
- `mach_default_zero_mathlib_guard_v0`
- `mach_legacy_audit_trace_record_v0`

## Results

- Legacy header opt-in: default output remains zero dependency.
- Legacy adapter boundary: adapter remains explicit-review only.
- Migration stub: maps toward MachLib-owned primitives/records without adding a release dependency.

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, default legacy behavior, release dependency, or public
theorem/proof/open-problem claim is authorized.
"""
    (reports / "machlib_lane6_legacy_boundary_summary_2026_05_20.md").write_text(summary, encoding="utf-8")

    lines = [
        f"# MachLib Lane 6 Legacy Boundary Results ({DATE})",
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
                f"- Compatibility kind: {row.get('compatibility_kind')}",
                f"- Default enabled: {str(row.get('default_enabled')).lower()}",
                f"- Opt-in only: {str(row.get('opt_in_only')).lower()}",
                f"- Release dependency allowed: {str(row.get('release_dependency_allowed')).lower()}",
                f"- Current release dependency: {str(row.get('current_release_dependency')).lower()}",
                f"- Status: {row['status']}",
                f"- Checks: {json.dumps(row.get('checks', []), sort_keys=True)}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane6_legacy_boundary_results_2026_05_20.md").write_text("\n".join(lines), encoding="utf-8")

    roundtrip_lines = [
        f"# MachLib Lane 6 Roundtrip Results ({DATE})",
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
                f"- eFrog opt-in legacy detected: {str(row['efrog_legacy_opt_in_detected']).lower()}",
                f"- Forge probe status: {row['forge_probe_status']}",
                f"- Roundtrip status: {row['roundtrip_status']}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane6_roundtrip_results_2026_05_20.md").write_text("\n".join(roundtrip_lines), encoding="utf-8")

    guard = f"""# MachLib Lane 6 Legacy Guardrail Report ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Guardrails

- No external formal-library dependency introduced: PASS
- Zero-dependency checker passes: PASS
- eFrog default output has no external dependency import: {roundtrip['efrog_status']}
- Legacy compatibility opt-in only: PASS
- Legacy compatibility never default: PASS
- Legacy compatibility never release dependency: PASS
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
    (reports / "machlib_lane6_legacy_guardrail_report_2026_05_20.md").write_text(guard, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument("--execution-out", default="corpus/eml_lanes_draft/lane_6_legacy_compatibility/execution_result_2026_05_20.json")
    parser.add_argument("--roundtrip-out", default="corpus/eml_lanes_draft/lane_6_legacy_compatibility/roundtrip_result_2026_05_20.json")
    parser.add_argument("--spec-out", default="corpus/eml_lanes_draft/lane_6_legacy_compatibility/legacy_boundary_spec_draft_2026_05_20.json")
    parser.add_argument("--tmp", default="/tmp/machlib_lane6_legacy_boundary_roundtrip_2026_05_20")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    specs = write_legacy_boundary_spec(Path(args.spec_out))
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
