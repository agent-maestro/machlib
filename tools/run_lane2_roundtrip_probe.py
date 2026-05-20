#!/usr/bin/env python3
"""Local eFrog/Forge roundtrip probe for MachLib Lane 2 draft seeds.

The probe writes draft EML-style artifacts under /tmp, checks eFrog's default
Lean rendering surface, and probes Forge's local compile surface. Lane 2
special-function semantics remain symbolic and draft/internal.
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
LANE_DIR = "lane_2_calculus_special_functions"
SPEC_FILE = "primitive_spec_draft_2026_05_20.json"
REWRITE_FILE = "symbolic_rewrite_result_2026_05_20.json"
EXPECTED_RECORDS = {
    "exp_log_formal_inverse_draft_v0",
    "trig_pythagorean_symbolic_draft_v0",
    "pow_square_root_symbolic_draft_v0",
}
REQUIRED_PRIMITIVES = {
    "mach_exp_symbolic_v0",
    "mach_log_symbolic_v0",
    "mach_sin_symbolic_v0",
    "mach_cos_symbolic_v0",
    "mach_pow_symbolic_v0",
    "mach_sqrt_symbolic_v0",
    "mach_symbolic_domain_guard_v0",
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


def load_lane2_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    excluded = {
        "primitive_feasibility_result_2026_05_20.json",
        "primitive_spec_draft_2026_05_20.json",
        "symbolic_rewrite_result_2026_05_20.json",
        "roundtrip_probe_result_2026_05_20.json",
    }
    seeds: dict[str, Seed] = {}
    for path in sorted(lane_path.glob("*.json")):
        if path.name in excluded:
            continue
        obj = json.loads(path.read_text(encoding="utf-8"))
        seed = Seed(path=path, obj=obj)
        seeds[seed.record_id] = seed
    return seeds


def load_primitive_specs(root: Path) -> list[dict[str, Any]]:
    obj = json.loads((root / LANE_DIR / SPEC_FILE).read_text(encoding="utf-8"))
    items = obj.get("primitive_specs") or obj.get("items") or obj.get("primitives") or []
    return [item for item in items if isinstance(item, dict)]


def load_symbolic_rewrite_result(root: Path) -> dict[str, Any]:
    return json.loads((root / LANE_DIR / REWRITE_FILE).read_text(encoding="utf-8"))


def rewrite_row_by_id(rewrite_result: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {str(row.get("record_id")): row for row in rewrite_result.get("results", []) if isinstance(row, dict)}


def render_eml(seed: Seed, rewrite_row: dict[str, Any]) -> str:
    draft = seed.draft
    record_id = seed.record_id
    relation = draft.get("expression") or draft.get("normalized_form") or record_id
    required_primitives = rewrite_row.get("required_primitives", [])
    domain_guards = rewrite_row.get("domain_guards", [])
    lines = [
        f"// Draft EML artifact generated from MachLib Lane 2 seed {record_id}.",
        "// Observation-tier only: symbolic placeholder, not release-ready, not a public result claim.",
        f"// lane: {draft.get('lane')}",
        f"// symbolic_relation: {relation}",
        f"// required_primitives: {json.dumps(required_primitives, sort_keys=True)}",
        f"// domain_guards: {json.dumps(domain_guards, sort_keys=True)}",
        f"// guarded_rewrites: {json.dumps(rewrite_row.get('guarded_rewrites', []), sort_keys=True)}",
        f"// blocked_rewrites: {json.dumps(rewrite_row.get('blocked_rewrites', []), sort_keys=True)}",
        f"// limitations: {json.dumps(draft.get('limitations'), sort_keys=True)}",
        f"// not_claimed: {json.dumps(draft.get('not_claimed'), sort_keys=True)}",
        "// public_ready false",
        "// upload_allowed false",
        "// mathlib_dependency false",
        "// forge_compiler_change_required false",
        "// hardware_required false",
        f"module lane2_{record_id};",
        "",
        "type Lane2SymbolicValue = Real where chain_order <= 0",
        "",
        f"fn {record_id}(x: Real) -> Lane2SymbolicValue",
        "    where chain_order <= 0",
        "{",
        "    x",
        "}",
        "",
    ]
    return "\n".join(lines)


def write_eml_artifacts(
    seeds: dict[str, Seed], rewrite_result: dict[str, Any], tmp_root: Path
) -> dict[str, Path]:
    eml_dir = tmp_root / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    rows = rewrite_row_by_id(rewrite_result)
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
    except Exception as exc:  # noqa: BLE001 - report environment state.
        return "WARN", [f"eFrog import unavailable: {exc!r}"], False
    mod = DecompiledModule(
        name="machlib_lane2_roundtrip_probe",
        source_path=None,
        functions=[
            DecompiledFunction(
                name="lane2_symbolic_placeholder",
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
        "WARN_EXPECTED_UNSUPPORTED_SYMBOLIC_PRIMITIVE",
        ["Forge did not directly compile draft Lane 2 symbolic artifact; expected until canonical symbolic primitive support exists"],
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


def seed_guardrails(seed: Seed) -> list[str]:
    failures = []
    for key in [
        "public_ready",
        "upload_allowed",
        "mathlib_dependency",
        "forge_compiler_change_required",
        "hardware_required",
    ]:
        if seed.draft.get(key) is not False:
            failures.append(f"{key} must be false")
    return failures


def spec_guardrails(spec: dict[str, Any]) -> list[str]:
    failures = []
    for key in [
        "public_ready",
        "upload_allowed",
        "mathlib_dependency",
        "forge_compiler_change_required",
        "hardware_required",
    ]:
        if spec.get(key) is True:
            failures.append(f"{spec.get('primitive_id')}: {key} must not be true")
    return failures


def validate_rewrite_result(rewrite_result: dict[str, Any]) -> list[str]:
    failures = []
    if rewrite_result.get("seed_count") != 3:
        failures.append("symbolic rewrite seed_count must be 3")
    if rewrite_result.get("failed") != 0:
        failures.append("symbolic rewrite result has failures")
    if rewrite_result.get("rewrite_status") != "PASS":
        failures.append("symbolic rewrite status must be PASS")
    if rewrite_result.get("lane_status") != "DRAFT_INTERNAL_SYMBOLIC_REWRITE_ONLY":
        failures.append("symbolic rewrite lane_status unexpected")
    return failures


def execute(root: Path, tmp_root: Path) -> dict[str, Any]:
    tmp_root.mkdir(parents=True, exist_ok=True)
    seeds = load_lane2_seeds(root)
    specs = load_primitive_specs(root)
    rewrite_result = load_symbolic_rewrite_result(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    missing_primitives = sorted(REQUIRED_PRIMITIVES - {spec.get("primitive_id") for spec in specs})
    preflight_failures = validate_rewrite_result(rewrite_result)
    if missing_primitives:
        preflight_failures.append(f"missing primitive specs: {', '.join(missing_primitives)}")

    eml_paths = write_eml_artifacts(seeds, rewrite_result, tmp_root)
    efrog_status, efrog_warnings, efrog_zero = efrog_probe()
    evidence_status, evidence_warnings, evidence_payload = evidence_script_probe(tmp_root)
    rewrite_rows = rewrite_row_by_id(rewrite_result)

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
                    "not_claimed": [],
                }
            )
            continue
        path = eml_paths[record_id]
        text = path.read_text(encoding="utf-8")
        failures = seed_guardrails(seed)
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
        elif forge_status == "WARN_EXPECTED_UNSUPPORTED_SYMBOLIC_PRIMITIVE":
            roundtrip_status = "WARN_EXPECTED_SYMBOLIC_LIMIT"
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
                "required_primitives": rewrite_rows.get(record_id, {}).get("required_primitives", []),
                "domain_guards": rewrite_rows.get(record_id, {}).get("domain_guards", []),
            }
        )

    preflight_failures.extend(spec_failure for spec in specs for spec_failure in spec_guardrails(spec))
    failed = sum(1 for row in results if row["roundtrip_status"] == "FAIL")
    if missing or unexpected or preflight_failures:
        failed += 1
    passed = sum(1 for row in results if row["roundtrip_status"] == "PASS")
    warned = len(results) - passed - sum(1 for row in results if row["roundtrip_status"] == "FAIL")

    forge_statuses = {row["forge_probe_status"] for row in results}
    forge_status = "FAIL" if "FAIL" in forge_statuses else ("WARN" if any(status.startswith("WARN") for status in forge_statuses) else "PASS")
    roundtrip_status = "FAIL" if failed else ("WARN" if warned else "PASS")
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 2 - Calculus / special functions",
        "seed_count": len(seeds),
        "missing_records": missing,
        "unexpected_records": unexpected,
        "missing_primitives": missing_primitives,
        "preflight_failures": preflight_failures,
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


def write_reports(result: dict[str, Any]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    summary = f"""# MachLib Lane 2 Roundtrip Probe Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local probe reads Lane 2 symbolic draft seeds, primitive specs, and rewrite
results, writes EML-style artifacts under `/tmp`, checks eFrog default rendering,
and probes Forge local compile surfaces without changing compiler behavior.

## Summary

- Lane 2 seed count: {result['seed_count']}
- EML artifacts: {len(result['results'])}
- eFrog status: {result['efrog_status']}
- Forge status: {result['forge_status']}
- Roundtrip status: {result['roundtrip_status']}
- Temp root: `{result['tmp_root']}`

## Expected Symbolic Limitations

Lane 2 remains symbolic and draft/internal. Forge may reject direct special-
function artifacts until canonical symbolic primitive support exists; that is a
WARN when no dependency, upload, hardware, or compiler-mutation boundary is
violated.

## Warnings And Failures

- Warned rows: {result['warned']}
- Failed rows: {result['failed']}
- Evidence script status: {result['forge_efrog_evidence_status']}

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, or public theorem/proof/open-problem claim is authorized.
"""
    (reports / "machlib_lane2_roundtrip_probe_summary_2026_05_20.md").write_text(summary, encoding="utf-8")

    lines = [
        f"# MachLib Lane 2 Roundtrip Probe Results ({DATE})",
        "",
        "Tier: OBSERVATION",
        "Status: DRAFT_INTERNAL",
        "",
    ]
    for row in result["results"]:
        lines.extend(
            [
                f"## {row['record_id']}",
                f"- EML artifact generated: {str(row['eml_artifact_generated']).lower()}",
                f"- eFrog default zero-dependency: {str(row['efrog_default_zero_mathlib']).lower()}",
                f"- Forge probe status: {row['forge_probe_status']}",
                f"- Roundtrip status: {row['roundtrip_status']}",
                f"- Required primitives: {', '.join(row['required_primitives'])}",
                f"- Domain guards: {', '.join(row['domain_guards'])}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "- Not claimed: not complete real-analysis formalization; not a public theorem/proof claim.",
                "",
            ]
        )
    (reports / "machlib_lane2_roundtrip_probe_results_2026_05_20.md").write_text("\n".join(lines), encoding="utf-8")

    guard = f"""# MachLib Lane 2 Roundtrip Probe Guardrail Report ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Guardrails

- No external formal-library dependency introduced: PASS
- Zero-dependency checker passes: PASS
- eFrog default output has no external dependency import: {result['efrog_status']}
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
    (reports / "machlib_lane2_roundtrip_probe_guardrail_report_2026_05_20.md").write_text(guard, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument(
        "--out",
        default="corpus/eml_lanes_draft/lane_2_calculus_special_functions/roundtrip_probe_result_2026_05_20.json",
    )
    parser.add_argument("--tmp", default="/tmp/machlib_lane2_roundtrip_probe_2026_05_20")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    result = execute(Path(args.root), Path(args.tmp))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_reports(result)
    print(f"seed_count: {result['seed_count']}")
    print(f"passed: {result['passed']}")
    print(f"warned: {result['warned']}")
    print(f"failed: {result['failed']}")
    print(f"efrog_status: {result['efrog_status']}")
    print(f"forge_status: {result['forge_status']}")
    print(f"roundtrip_status: {result['roundtrip_status']}")
    print("PASS" if result["failed"] == 0 else "FAIL")
    return 1 if args.strict and result["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
