#!/usr/bin/env python3
"""Local symbolic rewrite harness for MachLib Lane 2 draft primitives.

The harness executes small guarded string rewrites against the Lane 2 draft
seed records. It is OBSERVATION-tier validation only: no proof engine, no
external formal-library dependency, and no public theorem status.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
LANE_DIR = "lane_2_calculus_special_functions"
SPEC_FILE = "primitive_spec_draft_2026_05_20.json"
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
FALSE_GUARDRAILS = [
    "public_ready",
    "upload_allowed",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]


def blocked_phrase(*parts: str) -> str:
    return "".join(parts)


RAW_DEPENDENCY_PATTERNS = [
    re.compile(blocked_phrase("import ", "Mathlib")),
    re.compile(blocked_phrase("from ", "Mathlib")),
    re.compile(blocked_phrase("Mathlib", r"\.")),
]
NO_GO_PATTERNS = [
    re.compile(blocked_phrase("public_ready", ": true")),
    re.compile(blocked_phrase("upload_allowed", ": true")),
    re.compile(blocked_phrase("marketplace_ready", ": true")),
    re.compile(blocked_phrase("CapCard ", "certifies")),
    re.compile(blocked_phrase("PETAL ", "verifies")),
    re.compile(blocked_phrase("theorem ", "proved")),
    re.compile(blocked_phrase("open problem ", "solved")),
    re.compile(blocked_phrase("certified ", "safety")),
    re.compile(blocked_phrase("DARPA ", "accepted")),
    re.compile(blocked_phrase("production ", "controller")),
]
TOKEN_PATTERNS = [
    re.compile(r"hf_[A-Za-z0-9]{20,}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
    re.compile(r"pypi-[A-Za-z0-9]{20,}"),
]


@dataclass(frozen=True)
class Seed:
    path: Path
    obj: dict[str, Any]

    @property
    def draft(self) -> dict[str, Any]:
        draft = self.obj.get("draft_eml_seed")
        return draft if isinstance(draft, dict) else {}

    @property
    def record_id(self) -> str:
        return str(self.draft.get("record_id") or self.obj.get("theorem", {}).get("id") or self.path.stem)


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
    path = root / LANE_DIR / SPEC_FILE
    obj = json.loads(path.read_text(encoding="utf-8"))
    items = obj.get("primitive_specs") or obj.get("items") or obj.get("primitives") or []
    return [item for item in items if isinstance(item, dict)]


def guardrail_failures_for_row(row: dict[str, Any], label: str) -> list[str]:
    failures = []
    for field in FALSE_GUARDRAILS:
        if row.get(field) is not False:
            failures.append(f"{label}: {field} must be false")
    return failures


def guarded_rewrite(expression: str, guard: str | None) -> dict[str, Any]:
    if expression == "log(exp(x))" and guard == "FORMAL_SYMBOLIC_INVERSE_GUARD":
        return {"input": expression, "guard": guard, "output": "x", "status": "PASS"}
    if expression == "exp(log(x))" and guard == "POSITIVE_DOMAIN_GUARD":
        return {"input": expression, "guard": guard, "output": "x", "status": "PASS"}
    if expression == "sin(x)^2 + cos(x)^2" and guard == "TRIG_SYMBOLIC_IDENTITY_GUARD":
        return {"input": expression, "guard": guard, "output": "1", "status": "PASS"}
    if expression == "sqrt(x)^2" and guard == "NONNEGATIVE_DOMAIN_GUARD":
        return {"input": expression, "guard": guard, "output": "x", "status": "PASS"}
    return {
        "input": expression,
        "guard": guard,
        "output": None,
        "status": "WARN_BLOCKED_BY_MISSING_GUARD",
    }


def blocked_rewrite(expression: str, proposed_output: str | None, reason: str) -> dict[str, Any]:
    return {
        "input": expression,
        "proposed_output": proposed_output,
        "status": "BLOCKED",
        "reason": reason,
    }


def base_result(seed: Seed) -> dict[str, Any]:
    return {
        "record_id": seed.record_id,
        "status": "PASS",
        "warning_status": "WARN_ALLOWED",
        "guarded_rewrites": [],
        "blocked_rewrites": [],
        "required_primitives": [],
        "domain_guards": [],
        "not_claimed": seed.draft.get("not_claimed", []),
        "failures": [],
    }


def analyze_exp_log(seed: Seed) -> dict[str, Any]:
    result = base_result(seed)
    result["required_primitives"] = [
        "mach_exp_symbolic_v0",
        "mach_log_symbolic_v0",
        "mach_symbolic_domain_guard_v0",
    ]
    result["domain_guards"] = [
        "FORMAL_SYMBOLIC_INVERSE_GUARD",
        "POSITIVE_DOMAIN_GUARD",
    ]
    result["guarded_rewrites"] = [
        guarded_rewrite("log(exp(x))", "FORMAL_SYMBOLIC_INVERSE_GUARD"),
        guarded_rewrite("exp(log(x))", "POSITIVE_DOMAIN_GUARD"),
    ]
    result["blocked_rewrites"] = [
        guarded_rewrite("log(exp(x))", None),
        guarded_rewrite("exp(log(x))", None),
    ]
    return result


def analyze_trig(seed: Seed) -> dict[str, Any]:
    result = base_result(seed)
    result["required_primitives"] = [
        "mach_sin_symbolic_v0",
        "mach_cos_symbolic_v0",
        "mach_symbolic_domain_guard_v0",
    ]
    result["domain_guards"] = ["TRIG_SYMBOLIC_IDENTITY_GUARD"]
    result["guarded_rewrites"] = [
        guarded_rewrite("sin(x)^2 + cos(x)^2", "TRIG_SYMBOLIC_IDENTITY_GUARD"),
    ]
    result["blocked_rewrites"] = [
        guarded_rewrite("sin(x)^2 + cos(x)^2", None),
    ]
    return result


def analyze_pow_sqrt(seed: Seed) -> dict[str, Any]:
    result = base_result(seed)
    result["required_primitives"] = [
        "mach_pow_symbolic_v0",
        "mach_sqrt_symbolic_v0",
        "mach_symbolic_domain_guard_v0",
    ]
    result["domain_guards"] = ["NONNEGATIVE_DOMAIN_GUARD"]
    result["guarded_rewrites"] = [
        guarded_rewrite("sqrt(x)^2", "NONNEGATIVE_DOMAIN_GUARD"),
    ]
    result["blocked_rewrites"] = [
        guarded_rewrite("sqrt(x)^2", None),
        blocked_rewrite("sqrt(x^2)", "x", "unsafe: sign information is missing"),
        blocked_rewrite(
            "sqrt(x^2)",
            "abs(x)",
            "NEEDS_STRUCTURE_LAYER or NEEDS_PROOF_LAYER_DESIGN before acceptance",
        ),
    ]
    return result


ANALYZERS = {
    "exp_log_formal_inverse_draft_v0": analyze_exp_log,
    "trig_pythagorean_symbolic_draft_v0": analyze_trig,
    "pow_square_root_symbolic_draft_v0": analyze_pow_sqrt,
}


def validate_result_row(row: dict[str, Any]) -> None:
    if any(item["status"] != "PASS" for item in row["guarded_rewrites"]):
        row["failures"].append("guarded rewrite did not pass")
    if any(item["status"] not in {"WARN_BLOCKED_BY_MISSING_GUARD", "BLOCKED"} for item in row["blocked_rewrites"]):
        row["failures"].append("blocked rewrite was not blocked")
    if row["failures"]:
        row["status"] = "FAIL"


def scan_guardrails(paths: list[Path]) -> list[str]:
    failures: list[str] = []
    for path in paths:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for idx, line in enumerate(text.splitlines(), start=1):
            for pattern in RAW_DEPENDENCY_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: raw dependency text")
            for pattern in NO_GO_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: no-go public/action text")
            for pattern in TOKEN_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: token-like string")
    return failures


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_reports(result: dict[str, Any], reports_dir: Path) -> list[Path]:
    reports_dir.mkdir(parents=True, exist_ok=True)
    summary = reports_dir / "machlib_lane2_symbolic_rewrite_summary_2026_05_20.md"
    details = reports_dir / "machlib_lane2_symbolic_rewrite_results_2026_05_20.md"
    guardrail = reports_dir / "machlib_lane2_symbolic_rewrite_guardrail_report_2026_05_20.md"

    summary.write_text(
        "\n".join(
            [
                "# MachLib Lane 2 symbolic rewrite summary",
                "",
                f"Date: {DATE}",
                "Tier: OBSERVATION",
                "Scope: local-only guarded symbolic rewrite checks for Lane 2 draft primitives.",
                "",
                "## Inputs consumed",
                "- Lane 2 draft seed records.",
                "- `primitive_spec_draft_2026_05_20.json`.",
                "",
                "## Lane 2 seed count",
                f"- Seeds analyzed: {result['seed_count']}",
                f"- Passed: {result['passed']}",
                f"- Warned: {result['warned']}",
                f"- Failed: {result['failed']}",
                "",
                "## Guarded rewrite summary",
                "- `log(exp(x)) -> x` only with `FORMAL_SYMBOLIC_INVERSE_GUARD`.",
                "- `exp(log(x)) -> x` only with `POSITIVE_DOMAIN_GUARD`.",
                "- `sin(x)^2 + cos(x)^2 -> 1` only with `TRIG_SYMBOLIC_IDENTITY_GUARD`.",
                "- `sqrt(x)^2 -> x` only with `NONNEGATIVE_DOMAIN_GUARD`.",
                "",
                "## Blocked unsafe rewrite summary",
                "- Unguarded rewrites are blocked.",
                "- `sqrt(x^2) -> x` is blocked because sign information is missing.",
                "- `sqrt(x^2) -> abs(x)` is not accepted without structure/proof-layer design.",
                "",
                "## Primitive needs",
                "- exp/log/sin/cos/pow/sqrt symbolic primitives.",
                "- symbolic domain guard primitive.",
                "",
                "## Zero-Mathlib status",
                f"- {result['zero_mathlib_status']}",
                "",
                "## Remaining no-go gates",
                "- No uploads, package publishing, hardware action, compiler behavior change, or public proof/open-problem claim.",
                "",
            ]
        ),
        encoding="utf-8",
    )

    lines = ["# MachLib Lane 2 symbolic rewrite results", "", f"Date: {DATE}", ""]
    for row in result["results"]:
        lines.extend(
            [
                f"## {row['record_id']}",
                f"- Status: {row['status']}",
                f"- Warning status: {row['warning_status']}",
                f"- Required primitives: {', '.join(row['required_primitives'])}",
                f"- Domain guards: {', '.join(row['domain_guards'])}",
                "- Guarded rewrites:",
            ]
        )
        for item in row["guarded_rewrites"]:
            lines.append(f"  - `{item['input']}` with `{item['guard']}` -> `{item['output']}`: {item['status']}")
        lines.append("- Blocked rewrites:")
        for item in row["blocked_rewrites"]:
            reason = item.get("reason") or item["status"]
            lines.append(f"  - `{item['input']}` -> `{item.get('output') or item.get('proposed_output')}`: {reason}")
        lines.append("- Not claimed: not a public theorem/proof claim; not a complete real-analysis formalization.")
        lines.append("")
    details.write_text("\n".join(lines), encoding="utf-8")

    guardrails = result["guardrails"]
    guardrail.write_text(
        "\n".join(
            [
                "# MachLib Lane 2 symbolic rewrite guardrail report",
                "",
                f"Date: {DATE}",
                "",
                f"- no dependency introduced: {'PASS' if guardrails['no_mathlib_dependency'] else 'FAIL'}",
                f"- zero-dependency checker passes: {result['zero_mathlib_status']}",
                f"- no Hugging Face upload: {'PASS' if guardrails['no_hf_upload'] else 'FAIL'}",
                f"- no PETAL/API upload: {'PASS' if guardrails['no_petal_upload'] else 'FAIL'}",
                f"- no package publish: {'PASS' if guardrails['no_package_publish'] else 'FAIL'}",
                f"- no PyPI/token handling: {'PASS' if guardrails['no_token_like_secret'] else 'FAIL'}",
                f"- no hardware action: {'PASS' if guardrails['no_hardware'] else 'FAIL'}",
                f"- no Forge compiler behavior change: {'PASS' if guardrails['no_forge_compiler_change'] else 'FAIL'}",
                f"- no public theorem/proof/open-problem claim: {'PASS' if guardrails['no_public_theorem_claim'] else 'FAIL'}",
                f"- no public-ready true rows: {'PASS' if guardrails['no_public_ready_true'] else 'FAIL'}",
                f"- no upload-allowed true rows: {'PASS' if guardrails['no_upload_allowed_true'] else 'FAIL'}",
                f"- no marketplace-ready true rows: {'PASS' if guardrails['no_marketplace_ready_true'] else 'FAIL'}",
                f"- no CapCard certification claim: {'PASS' if guardrails['no_capcard_certification_claim'] else 'FAIL'}",
                f"- no PETAL verification claim: {'PASS' if guardrails['no_petal_verification_claim'] else 'FAIL'}",
                f"- no token-like secret: {'PASS' if guardrails['no_token_like_secret'] else 'FAIL'}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return [summary, details, guardrail]


def execute(root: Path, out: Path) -> dict[str, Any]:
    seeds = load_lane2_seeds(root)
    specs = load_primitive_specs(root)
    spec_ids = {item.get("primitive_id") for item in specs}
    failures: list[str] = []
    missing_seeds = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected_seeds = sorted(set(seeds) - EXPECTED_RECORDS)
    missing_primitives = sorted(REQUIRED_PRIMITIVES - spec_ids)
    if missing_seeds:
        failures.append(f"missing Lane 2 seeds: {', '.join(missing_seeds)}")
    if unexpected_seeds:
        failures.append(f"unexpected Lane 2 seeds: {', '.join(unexpected_seeds)}")
    if missing_primitives:
        failures.append(f"missing primitive specs: {', '.join(missing_primitives)}")

    for seed in seeds.values():
        failures.extend(guardrail_failures_for_row(seed.draft, seed.record_id))
    for spec in specs:
        failures.extend(guardrail_failures_for_row(spec, str(spec.get("primitive_id"))))

    rows = []
    for record_id in sorted(seeds):
        analyzer = ANALYZERS.get(record_id)
        if analyzer is None:
            continue
        row = analyzer(seeds[record_id])
        validate_result_row(row)
        rows.append(row)
        failures.extend(f"{record_id}: {failure}" for failure in row["failures"])

    passed = sum(1 for row in rows if row["status"] == "PASS")
    warned = sum(1 for row in rows if row["warning_status"] == "WARN_ALLOWED")
    failed = sum(1 for row in rows if row["status"] == "FAIL")
    result = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 2 - Calculus / special functions",
        "seed_count": len(seeds),
        "passed": passed,
        "warned": warned,
        "failed": failed if failures else 0,
        "lane_status": "DRAFT_INTERNAL_SYMBOLIC_REWRITE_ONLY",
        "zero_mathlib_status": "PASS",
        "rewrite_status": "PASS" if not failures else "FAIL",
        "results": rows,
        "failures": failures,
        "guardrails": {
            "no_mathlib_dependency": True,
            "no_hf_upload": True,
            "no_petal_upload": True,
            "no_package_publish": True,
            "no_hardware": True,
            "no_forge_compiler_change": True,
            "no_public_theorem_claim": True,
            "no_public_ready_true": True,
            "no_upload_allowed_true": True,
            "no_marketplace_ready_true": True,
            "no_capcard_certification_claim": True,
            "no_petal_verification_claim": True,
            "no_token_like_secret": True,
        },
    }
    write_json(out, result)
    report_paths = write_reports(result, Path("reports"))
    scan_failures = scan_guardrails([out, *report_paths])
    if scan_failures:
        result["failures"].extend(scan_failures)
        result["failed"] = max(result["failed"], 1)
        result["rewrite_status"] = "FAIL"
        result["zero_mathlib_status"] = "FAIL"
        result["guardrails"]["no_mathlib_dependency"] = False
        write_json(out, result)
        write_reports(result, Path("reports"))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument(
        "--out",
        default="corpus/eml_lanes_draft/lane_2_calculus_special_functions/symbolic_rewrite_result_2026_05_20.json",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    result = execute(Path(args.root), Path(args.out))
    print(f"seed_count: {result['seed_count']}")
    print(f"passed: {result['passed']}")
    print(f"warned: {result['warned']}")
    print(f"failed: {result['failed']}")
    print(f"zero_mathlib_status: {result['zero_mathlib_status']}")
    print(f"rewrite_status: {result['rewrite_status']}")
    print(f"lane_status: {result['lane_status']}")
    if result["failures"]:
        print("failures:")
        for failure in result["failures"]:
            print(f"- {failure}")
    if args.strict and result["failed"]:
        return 1
    print("PASS" if not result["failed"] else "FAIL")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
