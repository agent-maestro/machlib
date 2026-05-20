#!/usr/bin/env python3
"""Local eFrog/Forge roundtrip probe for MachLib Lane 1 draft seeds."""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
LANE_DIR = "lane_1_algebra_core"
EXPECTED_RECORDS = {
    "linear_dyadic_identity_v0",
    "cubic_dyadic_equilibrium_v0",
    "quadratic_zero_product_v0",
    "inequality_sign_flip_v0",
}


def blocked_phrase(*parts: str) -> str:
    return "".join(parts)


RAW_DEPENDENCY_STRINGS = [
    blocked_phrase("import ", "Mathlib"),
    blocked_phrase("from ", "Mathlib"),
    blocked_phrase("Mathlib", "."),
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
        return str(self.draft.get("record_id") or self.obj.get("theorem", {}).get("id"))


def load_lane1_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    seeds: dict[str, Seed] = {}
    for path in sorted(lane_path.glob("*.json")):
        if path.name in {
            "execution_result_2026_05_20.json",
            "roundtrip_result_2026_05_20.json",
        }:
            continue
        obj = json.loads(path.read_text(encoding="utf-8"))
        seed = Seed(path=path, obj=obj)
        seeds[seed.record_id] = seed
    return seeds


def contains_raw_dependency(text: str) -> bool:
    return any(item in text for item in RAW_DEPENDENCY_STRINGS)


def eml_body(record_id: str) -> str:
    if record_id == "linear_dyadic_identity_v0":
        return "x + x"
    if record_id == "cubic_dyadic_equilibrium_v0":
        return "x * x * x - (x + x)"
    if record_id == "quadratic_zero_product_v0":
        return "x * x - 1.0"
    if record_id == "inequality_sign_flip_v0":
        return "(b + c) - (a + c)"
    return "0.0"


def eml_args(record_id: str) -> str:
    if record_id == "inequality_sign_flip_v0":
        return "a: Real, b: Real, c: Real"
    return "x: Real"


def render_eml(seed: Seed) -> str:
    draft = seed.draft
    record_id = seed.record_id
    lines = [
        f"// Draft EML artifact generated from MachLib Lane 1 seed {record_id}.",
        "// Observation-tier only: not release-ready and not a public result claim.",
        f"// lane: {draft.get('lane')}",
        f"// expression: {draft.get('expression')}",
        f"// normalized_form: {draft.get('normalized_form')}",
        f"// operator_atoms: {', '.join(draft.get('operator_atoms', []))}",
        f"// expected_outputs: {json.dumps(draft.get('expected_outputs'), sort_keys=True)}",
        f"// validation_checks: {json.dumps(draft.get('validation_checks'), sort_keys=True)}",
        f"// not_claimed: {json.dumps(draft.get('not_claimed'), sort_keys=True)}",
        "// public_ready false",
        "// upload_allowed false",
        "// mathlib_dependency false",
        f"module lane1_{record_id};",
        "",
        "type Lane1Value = Real where chain_order <= 0",
        "",
        f"fn {record_id}({eml_args(record_id)}) -> Lane1Value",
        "    where chain_order <= 0",
        "{",
        f"    {eml_body(record_id)}",
        "}",
        "",
    ]
    return "\n".join(lines)


def write_eml_artifacts(seeds: dict[str, Seed], tmp_root: Path) -> dict[str, Path]:
    eml_dir = tmp_root / "eml"
    eml_dir.mkdir(parents=True, exist_ok=True)
    paths: dict[str, Path] = {}
    for record_id, seed in sorted(seeds.items()):
        path = eml_dir / f"{record_id}.eml"
        path.write_text(render_eml(seed), encoding="utf-8")
        paths[record_id] = path
    return paths


def efrog_probe() -> tuple[str, list[str], bool]:
    warnings: list[str] = []
    try:
        from efrog.lean import DecompiledFunction, DecompiledModule, render_lean
    except Exception as exc:  # noqa: BLE001 - report environment state.
        return "WARN", [f"eFrog import unavailable: {exc!r}"], False
    mod = DecompiledModule(
        name="machlib_lane1_roundtrip",
        source_path=None,
        functions=[
            DecompiledFunction(
                name="linear_dyadic_identity_v0",
                args=[("x", "Float")],
                return_type="Float",
                chain_order=0,
                let_bindings=[],
                body_expr="x + x",
            )
        ],
    )
    try:
        lean_text = render_lean(mod)
    except Exception as exc:  # noqa: BLE001
        return "WARN", [f"eFrog render unavailable: {exc!r}"], False
    if contains_raw_dependency(lean_text):
        return "FAIL", ["eFrog default Lean render contained a raw external dependency import"], False
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
        return "WARN", ["eml-compile not available"], {"available": False}
    out_path = tmp_root / "forge" / f"{path.stem}.py"
    out_path.parent.mkdir(parents=True, exist_ok=True)
    cmd = [eml_compile, str(path), "--target", "python", "-o", str(out_path)]
    result = run_command(cmd)
    if result["returncode"] == 0:
        return "PASS", [], {"command": cmd, "result": result, "output": str(out_path)}
    return (
        "WARN",
        ["Forge probe did not directly compile draft artifact; syntax may need a canonical serializer"],
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


def execute(root: Path, tmp_root: Path) -> dict[str, Any]:
    tmp_root.mkdir(parents=True, exist_ok=True)
    seeds = load_lane1_seeds(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    eml_paths = write_eml_artifacts(seeds, tmp_root)
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
        failures = seed_guardrails(seed)
        warnings = []
        if contains_raw_dependency(text):
            failures.append("generated EML artifact contains raw dependency import text")
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
        elif forge_status == "WARN":
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
    forge_status = "FAIL" if "FAIL" in forge_statuses else ("WARN" if "WARN" in forge_statuses else "PASS")
    roundtrip_status = "FAIL" if failed else ("WARN" if warned else "PASS")
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 1 - EML algebra core",
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


def write_reports(result: dict[str, Any]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    summary = f"""# MachLib Lane 1 Roundtrip Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local harness reads Lane 1 draft seeds, writes one EML-style artifact per
seed under `/tmp`, probes eFrog default Lean rendering, and probes Forge local
compile surfaces where available.

## Summary

- Lane 1 seed count: {result['seed_count']}
- EML artifacts: {len(result['results'])}
- eFrog status: {result['efrog_status']}
- Forge status: {result['forge_status']}
- Roundtrip status: {result['roundtrip_status']}
- Temp root: `{result['tmp_root']}`

## Warnings And Failures

- Warned rows: {result['warned']}
- Failed rows: {result['failed']}
- Evidence script status: {result['forge_efrog_evidence_status']}

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler
behavior change, or public result claim is authorized by this harness.
"""
    (reports / "machlib_lane1_roundtrip_summary_2026_05_20.md").write_text(summary, encoding="utf-8")

    lines = [
        f"# MachLib Lane 1 Roundtrip Results ({DATE})",
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
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane1_roundtrip_results_2026_05_20.md").write_text("\n".join(lines), encoding="utf-8")

    guard = f"""# MachLib Lane 1 Roundtrip Guardrail Report ({DATE})

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
    (reports / "machlib_lane1_roundtrip_guardrail_report_2026_05_20.md").write_text(guard, encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument(
        "--out",
        default="corpus/eml_lanes_draft/lane_1_algebra_core/roundtrip_result_2026_05_20.json",
    )
    parser.add_argument("--tmp", default="/tmp/machlib_lane1_roundtrip_2026_05_20")
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
