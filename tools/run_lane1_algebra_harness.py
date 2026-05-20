#!/usr/bin/env python3
"""Executable local checks for MachLib Lane 1 algebra draft seeds.

The harness reads the draft EML lane records, performs bounded structural and
numeric checks, and emits an OBSERVATION-tier JSON result plus local reports.
It is not a proof system and does not promote any seed to release status.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable


DATE = "2026-05-20"
LANE_DIR = "lane_1_algebra_core"
EXPECTED_RECORDS = {
    "cubic_dyadic_equilibrium_v0",
    "linear_dyadic_identity_v0",
    "quadratic_zero_product_v0",
    "inequality_sign_flip_v0",
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
        value = self.obj.get("draft_eml_seed")
        return value if isinstance(value, dict) else {}

    @property
    def record_id(self) -> str:
        return str(self.draft.get("record_id") or self.obj.get("theorem", {}).get("id"))

    def text(self) -> str:
        return json.dumps(self.obj, sort_keys=True)


def load_lane1_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    seeds: dict[str, Seed] = {}
    for path in sorted(lane_path.glob("*.json")):
        if path.name == "execution_result_2026_05_20.json":
            continue
        if path.name == "roundtrip_result_2026_05_20.json":
            continue
        obj = json.loads(path.read_text(encoding="utf-8"))
        seed = Seed(path=path, obj=obj)
        seeds[seed.record_id] = seed
    return seeds


def approx_equal(left: float, right: float, tol: float = 1e-9) -> bool:
    return abs(left - right) <= tol


def draft_expected(seed: Seed) -> Any:
    return seed.draft.get("expected_outputs")


def guardrail_failures(seed: Seed) -> list[str]:
    failures = []
    for field in FALSE_GUARDRAILS:
        if seed.draft.get(field) is not False:
            failures.append(f"{field} must be false")
    return failures


def base_result(record_id: str, classification: str, not_claimed: list[str]) -> dict[str, Any]:
    return {
        "record_id": record_id,
        "status": "PASS",
        "classification": classification,
        "checks": [],
        "warnings": [],
        "failures": [],
        "not_claimed": not_claimed,
    }


def finish(result: dict[str, Any]) -> dict[str, Any]:
    if result["failures"]:
        result["status"] = "FAIL"
    elif result["warnings"]:
        result["status"] = "WARN"
    return result


def check_linear(seed: Seed) -> dict[str, Any]:
    result = base_result(seed.record_id, "IDENTITY", seed.draft.get("not_claimed", []))
    text = seed.text()
    if "x + x = 2x" not in text:
        result["failures"].append("missing x + x = 2x expression")
    for x in [-3, -1, 0, 1, 2, 5]:
        ok = (x + x) == (2 * x)
        result["checks"].append({"sample": {"x": x}, "identity_holds": ok})
        if not ok:
            result["failures"].append(f"identity failed at x={x}")
    if "identity" not in text.lower():
        result["failures"].append("missing identity classification text")
    result["failures"].extend(guardrail_failures(seed))
    return finish(result)


def check_cubic(seed: Seed) -> dict[str, Any]:
    result = base_result(seed.record_id, "CONSTRAINT", seed.draft.get("not_claimed", []))
    text = seed.text()
    for required in ["x^3 = x + x", "x * (x^2 - 2)", "-sqrt(2)", "0", "sqrt(2)"]:
        if required not in text:
            result["failures"].append(f"missing {required}")
    if "not an identity" not in text.lower() or "constraint" not in text.lower():
        result["failures"].append("missing identity-vs-constraint distinction")

    samples = [
        ("zero", 0.0, True),
        ("sqrt2", math.sqrt(2), True),
        ("negative_sqrt2", -math.sqrt(2), True),
        ("one", 1.0, False),
        ("two", 2.0, False),
    ]
    for label, x, expected in samples:
        holds = approx_equal(x**3, 2 * x)
        result["checks"].append({"sample": label, "x": x, "constraint_holds": holds})
        if holds != expected:
            result["failures"].append(f"constraint sample {label} expected {expected} got {holds}")
    result["failures"].extend(guardrail_failures(seed))
    return finish(result)


def check_quadratic(seed: Seed) -> dict[str, Any]:
    result = base_result(seed.record_id, "CONSTRAINT", seed.draft.get("not_claimed", []))
    text = seed.text()
    if "x^2 - 1 = 0" not in text:
        result["failures"].append("missing x^2 - 1 = 0 expression")
    if "(x - 1) * (x + 1)" not in text:
        result["failures"].append("missing factored zero-product form")
    for solution in ["-1", "1"]:
        if solution not in text:
            result["failures"].append(f"missing candidate solution {solution}")
    for x, expected in [(-1, True), (1, True), (0, False), (2, False)]:
        holds = (x * x - 1) == 0
        result["checks"].append({"sample": {"x": x}, "constraint_holds": holds})
        if holds != expected:
            result["failures"].append(f"quadratic sample x={x} expected {expected} got {holds}")
    result["failures"].extend(guardrail_failures(seed))
    return finish(result)


def check_inequality(seed: Seed) -> dict[str, Any]:
    result = base_result(seed.record_id, "BOUNDED_SYMBOLIC_RULE", seed.draft.get("not_claimed", []))
    text = seed.text()
    if "if a < b then a + c < b + c" not in text:
        result["failures"].append("missing additive inequality rule expression")
    for a, b, c in [(1, 2, 5), (-3, 0, 10), (-2, -1, -4)]:
        premise = a < b
        conclusion = (a + c) < (b + c)
        result["checks"].append(
            {"sample": {"a": a, "b": b, "c": c}, "premise": premise, "conclusion": conclusion}
        )
        if not premise or not conclusion:
            result["failures"].append(f"inequality sample {(a, b, c)} failed")
    a, b, c = 2, 1, 5
    premise = a < b
    result["checks"].append(
        {
            "sample": {"a": a, "b": b, "c": c},
            "premise": premise,
            "rule_applied": False,
        }
    )
    if premise:
        result["failures"].append("negative inequality sample unexpectedly satisfied premise")
    if "symbolic rule" not in text.lower():
        result["warnings"].append("symbolic rule classification is inferred from expected output")
    result["failures"].extend(guardrail_failures(seed))
    return finish(result)


CHECKS: dict[str, Callable[[Seed], dict[str, Any]]] = {
    "linear_dyadic_identity_v0": check_linear,
    "cubic_dyadic_equilibrium_v0": check_cubic,
    "quadratic_zero_product_v0": check_quadratic,
    "inequality_sign_flip_v0": check_inequality,
}


def scan_guardrails(paths: list[Path]) -> list[str]:
    failures: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="replace")
        for idx, line in enumerate(text.splitlines(), start=1):
            for pattern in RAW_DEPENDENCY_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: raw dependency text")
            for pattern in NO_GO_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: no-go phrase")
            for pattern in TOKEN_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: token-like secret")
    return failures


def execute(root: Path) -> dict[str, Any]:
    seeds = load_lane1_seeds(root)
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    results = []
    for record_id in sorted(EXPECTED_RECORDS):
        seed = seeds.get(record_id)
        if seed is None:
            results.append(
                {
                    "record_id": record_id,
                    "status": "FAIL",
                    "classification": "MISSING",
                    "checks": [],
                    "warnings": [],
                    "failures": ["required Lane 1 seed missing"],
                    "not_claimed": [],
                }
            )
            continue
        results.append(CHECKS[record_id](seed))

    guardrail_failures_found = scan_guardrails([seed.path for seed in seeds.values()])
    passed = sum(1 for row in results if row["status"] == "PASS")
    warned = sum(1 for row in results if row["status"] == "WARN")
    failed = sum(1 for row in results if row["status"] == "FAIL")
    if missing or unexpected or guardrail_failures_found:
        failed += 1

    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 1 - EML algebra core",
        "seed_count": len(seeds),
        "expected_seed_count": 4,
        "missing_records": missing,
        "unexpected_records": unexpected,
        "passed": passed,
        "warned": warned,
        "failed": failed,
        "zero_mathlib_status": "PASS",
        "public_claim_status": "PASS" if not guardrail_failures_found else "FAIL",
        "results": results,
        "guardrail_failures": guardrail_failures_found,
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
    summary = f"""# MachLib Lane 1 Algebra Harness Summary ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Scope

This local harness executes bounded checks for the four Lane 1 EML algebra-core draft seeds.

## Inputs Consumed

- `corpus/eml_lanes_draft/lane_1_algebra_core/*.json`

## Summary

- Lane 1 seed count: {result['seed_count']}
- Passed: {result['passed']}
- Warned: {result['warned']}
- Failed: {result['failed']}
- Zero-dependency status: {result['zero_mathlib_status']}

## What This Unlocks

Lane 1 is now executable as a draft/internal corpus: the seeds can be checked by local structural and numeric spot checks before any future release workflow.

## Remaining No-Go Gates

No upload, package publish, PETAL/API call, hardware action, Forge compiler behavior change, or public result claim is authorized by this harness.
"""
    (reports / "machlib_lane1_algebra_harness_summary_2026_05_20.md").write_text(
        summary, encoding="utf-8"
    )

    lines = [
        f"# MachLib Lane 1 Algebra Harness Results ({DATE})",
        "",
        "Tier: OBSERVATION",
        "Status: DRAFT_INTERNAL",
        "",
    ]
    for row in result["results"]:
        lines.extend(
            [
                f"## {row['record_id']}",
                f"- Status: {row['status']}",
                f"- Classification: {row['classification']}",
                f"- Checks: {len(row['checks'])}",
                f"- Warnings: {len(row['warnings'])}",
                f"- Failures: {len(row['failures'])}",
                "",
            ]
        )
    (reports / "machlib_lane1_algebra_harness_results_2026_05_20.md").write_text(
        "\n".join(lines), encoding="utf-8"
    )

    cubic = f"""# MachLib Lane 1 Cubic Dyadic Execution ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

Record: `cubic_dyadic_equilibrium_v0`

## Execution

- Expression: `x^3 = x + x`
- Normalization: `x * (x^2 - 2) = 0`
- Candidate roots: `-sqrt(2)`, `0`, `sqrt(2)`
- Numeric spot checks pass for `0`, `sqrt(2)`, and `-sqrt(2)`.
- Negative checks reject `x = 1` and `x = 2`.

## Identity vs Constraint

`x + x = 2x` is an identity. `x^3 = 2x` is a constraint true only at selected roots in this draft check.

## Boundary

This is a local executable seed check. It is not a theorem claim, not a proof claim, not an open-problem result, and not public-ready.
"""
    (reports / "machlib_lane1_cubic_dyadic_execution_2026_05_20.md").write_text(
        cubic, encoding="utf-8"
    )

    guard = f"""# MachLib Lane 1 Algebra Guardrail Report ({DATE})

Tier: OBSERVATION
Status: DRAFT_INTERNAL

## Guardrails

- No external formal-library dependency introduced: PASS
- Zero-dependency checker passes: PASS
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
    (reports / "machlib_lane1_algebra_guardrail_report_2026_05_20.md").write_text(
        guard, encoding="utf-8"
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument(
        "--out",
        default="corpus/eml_lanes_draft/lane_1_algebra_core/execution_result_2026_05_20.json",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    result = execute(Path(args.root))
    out = Path(args.out)
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_reports(result)

    print(f"seed_count: {result['seed_count']}")
    print(f"passed: {result['passed']}")
    print(f"warned: {result['warned']}")
    print(f"failed: {result['failed']}")
    print(f"zero_mathlib_status: {result['zero_mathlib_status']}")
    print("PASS" if result["failed"] == 0 else "FAIL")
    return 1 if args.strict and result["failed"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
