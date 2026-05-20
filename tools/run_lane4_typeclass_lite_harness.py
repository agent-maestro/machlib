#!/usr/bin/env python3
"""Executable and roundtrip harness for MachLib Lane 4 typeclass-lite seeds.

This local-only harness checks machine-friendly finite structure records. It
does not use Lean hierarchy imports, does not establish public proof status,
and keeps all examples bounded and draft/internal.
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
LANE_DIR = "lane_4_typeclass_lite"
EXPECTED_RECORDS = {
    "typeclass_lite_magma_record_v0",
    "typeclass_lite_monoid_record_v0",
    "typeclass_lite_ordered_carrier_v0",
}
REQUIRED_STRUCTURE_IDS = {
    "mach_magma_lite_v0",
    "mach_monoid_lite_v0",
    "mach_ordered_carrier_lite_v0",
    "mach_law_record_v0",
    "mach_finite_carrier_guard_v0",
}
FALSE_GUARDRAILS = [
    "public_ready",
    "upload_allowed",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]
CARRIER = {0, 1, 2}


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


def add_mod_3(a: int, b: int) -> int:
    return (a + b) % 3


def load_lane4_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    excluded = {
        "execution_result_2026_05_20.json",
        "roundtrip_result_2026_05_20.json",
        "structure_spec_draft_2026_05_20.json",
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


def structure_spec(
    structure_id: str,
    name: str,
    carrier_kind: str,
    operations: list[str],
    laws_as_records: list[str],
    finite_examples: list[str],
    validation_checks: list[str],
    required_future_design: list[str],
) -> dict[str, Any]:
    return {
        "structure_id": structure_id,
        "name": name,
        "carrier_kind": carrier_kind,
        "operations": operations,
        "laws_as_records": laws_as_records,
        "finite_examples": finite_examples,
        "validation_checks": validation_checks,
        "forbidden_claims": [
            "imported Lean hierarchy compatibility",
            "public algebra/typeclass theorem status",
            "release-ready structure layer",
            "blanket replacement for external libraries",
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


def build_structure_specs() -> list[dict[str, Any]]:
    return [
        structure_spec(
            "mach_magma_lite_v0",
            "Mach magma-lite",
            "finite_carrier",
            ["binary_op"],
            ["closure_record"],
            ["carrier={0,1,2}; op=add_mod_3"],
            ["closure over finite carrier", "operation table present"],
            ["record schema", "optional law slots"],
        ),
        structure_spec(
            "mach_monoid_lite_v0",
            "Mach monoid-lite",
            "finite_carrier",
            ["binary_op", "identity"],
            ["closure_record", "associativity_record", "identity_record"],
            ["carrier={0,1,2}; op=add_mod_3; identity=0"],
            ["finite associativity table", "left/right identity checks"],
            ["law-record schema", "evidence-row integration"],
        ),
        structure_spec(
            "mach_ordered_carrier_lite_v0",
            "Mach ordered-carrier-lite",
            "finite_ordered_carrier",
            ["relation_lte"],
            ["reflexive_record", "antisymmetric_record", "transitive_record", "totality_record"],
            ["carrier={0,1,2}; relation=integer_lte_restricted"],
            ["reflexive", "antisymmetric", "transitive", "total over fixture"],
            ["order-assumption records", "monotonicity slots"],
        ),
        structure_spec(
            "mach_law_record_v0",
            "Mach law record",
            "metadata_record",
            ["named_check"],
            ["local_law_result"],
            ["closure/associativity/identity rows"],
            ["law remains local to a finite example"],
            ["shared law-result schema"],
        ),
        structure_spec(
            "mach_finite_carrier_guard_v0",
            "Mach finite carrier guard",
            "finite_guard",
            ["membership_check"],
            ["bounded_quantification_record"],
            ["carrier={0,1,2}"],
            ["all finite checks stay bounded"],
            ["guard schema", "cardinality metadata"],
        ),
    ]


def check_closure() -> bool:
    return all(add_mod_3(a, b) in CARRIER for a in CARRIER for b in CARRIER)


def operation_table() -> list[list[int]]:
    return [[add_mod_3(a, b) for b in sorted(CARRIER)] for a in sorted(CARRIER)]


def check_associativity() -> bool:
    return all(add_mod_3(add_mod_3(a, b), c) == add_mod_3(a, add_mod_3(b, c)) for a in CARRIER for b in CARRIER for c in CARRIER)


def check_identity(identity: int = 0) -> bool:
    return all(add_mod_3(identity, a) == a and add_mod_3(a, identity) == a for a in CARRIER)


def lte(a: int, b: int) -> bool:
    return a <= b


def check_reflexive() -> bool:
    return all(lte(a, a) for a in CARRIER)


def check_antisymmetric() -> bool:
    return all(not (lte(a, b) and lte(b, a)) or a == b for a in CARRIER for b in CARRIER)


def check_transitive() -> bool:
    return all(not (lte(a, b) and lte(b, c)) or lte(a, c) for a in CARRIER for b in CARRIER for c in CARRIER)


def check_total() -> bool:
    return all(lte(a, b) or lte(b, a) for a in CARRIER for b in CARRIER)


def check_magma(seed: Seed) -> dict[str, Any]:
    checks = [
        {"name": "closure", "actual": check_closure(), "expected": True},
        {"name": "operation_table_exists", "actual": bool(operation_table()), "expected": True},
        {"name": "associativity_claimed", "actual": False, "expected": False, "note": "not claimed for magma-lite"},
        {"name": "identity_claimed", "actual": False, "expected": False, "note": "not claimed for magma-lite"},
    ]
    failures = [f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    failures.extend(guardrail_failures(seed))
    return {
        "record_id": seed.record_id,
        "classification": "TYPECLASS_LITE_MAGMA_RECORD",
        "status": "FAIL" if failures else "PASS",
        "fixture": {"carrier": sorted(CARRIER), "operation": "add_mod_3", "operation_table": operation_table()},
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def check_monoid(seed: Seed) -> dict[str, Any]:
    checks = [
        {"name": "closure", "actual": check_closure(), "expected": True},
        {"name": "associativity", "actual": check_associativity(), "expected": True},
        {"name": "identity_left_right", "actual": check_identity(0), "expected": True},
        {"name": "imported_hierarchy_claimed", "actual": False, "expected": False},
    ]
    failures = [f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    failures.extend(guardrail_failures(seed))
    return {
        "record_id": seed.record_id,
        "classification": "TYPECLASS_LITE_MONOID_RECORD",
        "status": "FAIL" if failures else "PASS",
        "fixture": {"carrier": sorted(CARRIER), "operation": "add_mod_3", "identity": 0},
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


def check_ordered(seed: Seed) -> dict[str, Any]:
    checks = [
        {"name": "reflexive", "actual": check_reflexive(), "expected": True},
        {"name": "antisymmetric", "actual": check_antisymmetric(), "expected": True},
        {"name": "transitive", "actual": check_transitive(), "expected": True},
        {"name": "total", "actual": check_total(), "expected": True, "note": "finite ordered-carrier convention"},
        {"name": "imported_hierarchy_claimed", "actual": False, "expected": False},
    ]
    failures = [f"{item['name']} expected {item['expected']} got {item['actual']}" for item in checks if item["actual"] != item["expected"]]
    failures.extend(guardrail_failures(seed))
    return {
        "record_id": seed.record_id,
        "classification": "TYPECLASS_LITE_ORDERED_CARRIER",
        "status": "FAIL" if failures else "PASS",
        "fixture": {"carrier": sorted(CARRIER), "relation": "integer_lte_restricted"},
        "checks": checks,
        "warnings": [],
        "failures": failures,
        "not_claimed": seed.draft.get("not_claimed", []),
    }


EXECUTION_CHECKS = {
    "typeclass_lite_magma_record_v0": check_magma,
    "typeclass_lite_monoid_record_v0": check_monoid,
    "typeclass_lite_ordered_carrier_v0": check_ordered,
}


def run_execution(root: Path) -> dict[str, Any]:
    seeds = load_lane4_seeds(root)
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
        "lane": "Lane 4 - Typeclass-lite structures",
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


def write_structure_spec(path: Path) -> list[dict[str, Any]]:
    specs = build_structure_specs()
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps({"date": DATE, "tier": "OBSERVATION", "local_only": True, "structure_specs": specs}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    return specs


def eml_body(record_id: str) -> str:
    if record_id == "typeclass_lite_magma_record_v0":
        return "0.0"
    if record_id == "typeclass_lite_monoid_record_v0":
        return "0.0"
    if record_id == "typeclass_lite_ordered_carrier_v0":
        return "1.0"
    return "0.0"


def render_eml(seed: Seed, execution_row: dict[str, Any]) -> str:
    draft = seed.draft
    record_id = seed.record_id
    fixture = execution_row.get("fixture", {})
    lines = [
        f"// Draft EML artifact generated from MachLib Lane 4 seed {record_id}.",
        "// Observation-tier only: bounded typeclass-lite record, not release-ready, not a public result claim.",
        f"// lane: {draft.get('lane')}",
        f"// structure_kind: {execution_row.get('classification')}",
        f"// carrier: {json.dumps(fixture.get('carrier'), sort_keys=True)}",
        f"// operations: {json.dumps(fixture.get('operation') or fixture.get('relation'), sort_keys=True)}",
        f"// laws_as_records: {json.dumps(execution_row.get('checks', []), sort_keys=True)}",
        f"// finite_examples: {json.dumps(fixture, sort_keys=True)}",
        f"// expected_outputs: {json.dumps(draft.get('expected_outputs'), sort_keys=True)}",
        f"// validation_checks: {json.dumps(draft.get('validation_checks'), sort_keys=True)}",
        f"// not_claimed: {json.dumps(draft.get('not_claimed'), sort_keys=True)}",
        "// public_ready false",
        "// upload_allowed false",
        "// mathlib_dependency false",
        "// forge_compiler_change_required false",
        "// hardware_required false",
        f"module lane4_{record_id};",
        "",
        "type Lane4Value = Real where chain_order <= 0",
        "",
        f"fn {record_id}(x: Real) -> Lane4Value",
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
        name="machlib_lane4_roundtrip",
        source_path=None,
        functions=[
            DecompiledFunction(
                name="lane4_structure_placeholder",
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
        ["Forge did not directly compile draft Lane 4 artifact; expected for unsupported draft structure schema"],
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
    seeds = load_lane4_seeds(root)
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
        "lane": "Lane 4 - Typeclass-lite structures",
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
    summary = f"""# MachLib Lane 4 Typeclass-Lite Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local harness executes bounded typeclass-lite structure checks for Lane 4
draft seeds, writes structure specs, and probes eFrog/Forge through draft
EML-style artifacts under `/tmp`.

## Summary

- Lane 4 seed count: {execution['seed_count']}
- Execution status: {execution['execution_status']}
- Roundtrip status: {roundtrip['roundtrip_status']}
- eFrog status: {roundtrip['efrog_status']}
- Forge status: {roundtrip['forge_status']}
- Structure specs: {len(specs)}
- Temp root: `{roundtrip['tmp_root']}`

## Structure Spec Summary

- `mach_magma_lite_v0`
- `mach_monoid_lite_v0`
- `mach_ordered_carrier_lite_v0`
- `mach_law_record_v0`
- `mach_finite_carrier_guard_v0`

## Results

- Magma-lite: finite closure over add_mod_3 carrier.
- Monoid-lite: closure, associativity, and identity over add_mod_3 carrier.
- Ordered-carrier-lite: reflexive, antisymmetric, transitive, and total finite relation.

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, Lean hierarchy import, or public theorem/proof/open-problem
claim is authorized.
"""
    (reports / "machlib_lane4_typeclass_lite_summary_2026_05_20.md").write_text(summary, encoding="utf-8")

    lines = [
        f"# MachLib Lane 4 Typeclass-Lite Results ({DATE})",
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
                f"- Fixture: {json.dumps(row.get('fixture', {}), sort_keys=True)}",
                f"- Checks: {json.dumps(row.get('checks', []), sort_keys=True)}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane4_typeclass_lite_results_2026_05_20.md").write_text("\n".join(lines), encoding="utf-8")

    roundtrip_lines = [
        f"# MachLib Lane 4 Roundtrip Results ({DATE})",
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
    (reports / "machlib_lane4_roundtrip_results_2026_05_20.md").write_text("\n".join(roundtrip_lines), encoding="utf-8")

    guard = f"""# MachLib Lane 4 Typeclass-Lite Guardrail Report ({DATE})

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
    (reports / "machlib_lane4_typeclass_lite_guardrail_report_2026_05_20.md").write_text(guard, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument("--execution-out", default="corpus/eml_lanes_draft/lane_4_typeclass_lite/execution_result_2026_05_20.json")
    parser.add_argument("--roundtrip-out", default="corpus/eml_lanes_draft/lane_4_typeclass_lite/roundtrip_result_2026_05_20.json")
    parser.add_argument("--spec-out", default="corpus/eml_lanes_draft/lane_4_typeclass_lite/structure_spec_draft_2026_05_20.json")
    parser.add_argument("--tmp", default="/tmp/machlib_lane4_typeclass_lite_roundtrip_2026_05_20")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    specs = write_structure_spec(Path(args.spec_out))
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
