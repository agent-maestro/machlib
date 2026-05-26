#!/usr/bin/env python3
"""Tiny exact rational-root search for MachLib factorization certificates v16."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


DATE = "2026-05-25"
DATE_TAG = "2026_05_25"
PACKET_ID = "machlib_rational_root_search_v16_2026_05_25"
V15_TOOL = Path(__file__).with_name("validate_machlib_factorization_certificates_v15.py")


BOUNDARY_FALSE_KEYS = [
    "general_root_count_theorem_proved",
    "root_count_induction_target_proved",
    "analytic_identity_theorem_proved",
    "forge_compiler_behavior_changed",
    "efrog_behavior_changed",
    "public_theorem_claim",
    "marketplace_ready",
    "public_ready",
    "production_marketplace_modified",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "package_publish_performed",
    "certified_safety_claim",
    "production_controller_claim",
]


def load_v15():
    spec = importlib.util.spec_from_file_location("machlib_factorization_v15", V15_TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


v15 = load_v15()


def parse_coeffs(values: list[Any]) -> list[Fraction]:
    return [v15.parse_fraction(value) for value in values]


def encode_coeffs(values: list[Fraction]) -> list[int | str]:
    return [v15.encode_fraction(value) for value in values]


def derivative_divide_by_linear(coeffs: list[Fraction], root: Fraction) -> list[Fraction] | None:
    """Divide low-to-high coeffs by (x-root), returning quotient low-to-high."""
    coeffs = v15.normalize(coeffs)
    if len(coeffs) <= 1:
        return None
    high = list(reversed(coeffs))
    quotient_high: list[Fraction] = [high[0]]
    for coeff in high[1:-1]:
        quotient_high.append(coeff + quotient_high[-1] * root)
    remainder = high[-1] + quotient_high[-1] * root
    if remainder != 0:
        return None
    return v15.normalize(list(reversed(quotient_high)))


def candidate_roots(limit: int, denominator_limit: int) -> list[Fraction]:
    roots: list[Fraction] = [Fraction(0, 1)]
    for denominator in range(1, denominator_limit + 1):
        for numerator in range(-limit, limit + 1):
            candidate = Fraction(numerator, denominator)
            if candidate not in roots:
                roots.append(candidate)
    return roots


def search_factorization(
    coeffs: list[Fraction],
    *,
    root_limit: int,
    denominator_limit: int,
) -> dict[str, Any]:
    remaining = v15.normalize(coeffs)
    roots: list[Fraction] = []
    candidates = candidate_roots(root_limit, denominator_limit)
    changed = True
    while changed and len(remaining) > 1:
        changed = False
        for root in candidates:
            if v15.evaluate(remaining, root) == 0:
                quotient = derivative_divide_by_linear(remaining, root)
                if quotient is None:
                    continue
                roots.append(root)
                remaining = quotient
                changed = True
                break
    constant = remaining[0] if len(remaining) == 1 else None
    status = "CERTIFICATE_GENERATED" if constant is not None and constant != 0 else "BLOCKED"
    blocker = None
    if status == "BLOCKED":
        blocker = (
            "NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND"
            if len(remaining) > 1
            else "ZERO_OR_EMPTY_CONSTANT_BLOCKER"
        )
    return {
        "status": status,
        "constant": constant,
        "linear_roots": roots,
        "remaining_coeffs": remaining,
        "blocker": blocker,
    }


def default_cases() -> list[dict[str, Any]]:
    return [
        {
            "case_id": "quadratic_two_integer_roots_v16",
            "description": "x^2 - 5x + 6",
            "coeffs": [6, -5, 1],
            "expect": "CERTIFICATE_GENERATED",
        },
        {
            "case_id": "cubic_three_integer_roots_v16",
            "description": "x^3 - 6x^2 + 11x - 6",
            "coeffs": [-6, 11, -6, 1],
            "expect": "CERTIFICATE_GENERATED",
        },
        {
            "case_id": "irreducible_over_rational_window_v16",
            "description": "x^2 + 1",
            "coeffs": [1, 0, 1],
            "expect": "BLOCKED",
        },
        {
            "case_id": "repeated_cubic_root_v16",
            "description": "(x-2)^3",
            "coeffs": [-8, 12, -6, 1],
            "expect": "CERTIFICATE_GENERATED",
        },
        {
            "case_id": "scaled_pair_v16",
            "description": "2(x-1)(x-4)",
            "coeffs": [8, -10, 2],
            "expect": "CERTIFICATE_GENERATED",
        },
        {
            "case_id": "fractional_roots_v16",
            "description": "3(x-1/2)(x+1)",
            "coeffs": ["-3/2", "3/2", 3],
            "expect": "CERTIFICATE_GENERATED",
        },
        {
            "case_id": "constant_only_v16",
            "description": "7",
            "coeffs": [7],
            "expect": "CERTIFICATE_GENERATED",
        },
    ]


def certificate_from_search(case: dict[str, Any], result: dict[str, Any]) -> dict[str, Any] | None:
    if result["status"] != "CERTIFICATE_GENERATED":
        return None
    coeffs = parse_coeffs(case["coeffs"])
    constant = result["constant"]
    roots = result["linear_roots"]
    return {
        "certificate_id": case["case_id"].replace("_v16", "_certificate_v16"),
        "description": case["description"],
        "coeffs": encode_coeffs(v15.normalize(coeffs)),
        "constant": v15.encode_fraction(constant),
        "linear_roots": encode_coeffs(roots),
        "expected_product_coeffs": encode_coeffs(v15.normalize(coeffs)),
        "expected_dedup_roots": encode_coeffs(v15.unique_roots(roots)),
        "normalized": True,
        "source": "machlib_rational_root_search_v16",
    }


def run_cases(cases: list[dict[str, Any]], root_limit: int, denominator_limit: int) -> dict[str, Any]:
    case_results: list[dict[str, Any]] = []
    certificates: list[dict[str, Any]] = []
    for case in cases:
        coeffs = parse_coeffs(case["coeffs"])
        result = search_factorization(
            coeffs,
            root_limit=root_limit,
            denominator_limit=denominator_limit,
        )
        certificate = certificate_from_search(case, result)
        validation = None
        if certificate is not None:
            validation_result = v15.validate_certificate(certificate)
            validation = validation_result.__dict__
            if validation_result.status == "PASS":
                certificates.append(certificate)
        expected = case.get("expect")
        case_status = result["status"]
        expectation_met = expected is None or expected == case_status
        case_results.append(
            {
                "case_id": case["case_id"],
                "description": case["description"],
                "status": case_status,
                "expectation_met": expectation_met,
                "input_coeffs": encode_coeffs(coeffs),
                "constant": None if result["constant"] is None else v15.encode_fraction(result["constant"]),
                "linear_roots": encode_coeffs(result["linear_roots"]),
                "remaining_coeffs": encode_coeffs(result["remaining_coeffs"]),
                "blocker": result["blocker"],
                "certificate_id": None if certificate is None else certificate["certificate_id"],
                "validation": validation,
            }
        )
    pass_cases = sum(1 for row in case_results if row["status"] == "CERTIFICATE_GENERATED")
    blocked_cases = sum(1 for row in case_results if row["status"] == "BLOCKED")
    validation_failures = [
        row for row in case_results
        if row["validation"] is not None and row["validation"]["status"] != "PASS"
    ]
    expectation_failures = [row for row in case_results if not row["expectation_met"]]
    status = (
        "MACHLIB_RATIONAL_ROOT_SEARCH_V16_READY"
        if not validation_failures and not expectation_failures
        else "MACHLIB_RATIONAL_ROOT_SEARCH_V16_FAIL"
    )
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": status,
        "search_class": "bounded_rational_linear_factor_search",
        "root_limit": root_limit,
        "denominator_limit": denominator_limit,
        "case_count": len(case_results),
        "certificate_generated_count": pass_cases,
        "blocked_count": blocked_cases,
        "validation_failure_count": len(validation_failures),
        "expectation_failure_count": len(expectation_failures),
        "certificates": certificates,
        "case_results": case_results,
        "arbitrary_factorization_discovery": False,
        "complete_rational_root_search_claim": False,
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "boundary": {key: False for key in BOUNDARY_FALSE_KEYS},
    }


def report(payload: dict[str, Any]) -> str:
    lines = [
        "# MachLib Rational Root Search v16",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Scope",
        "",
        "This is a bounded exact rational-root search over a small candidate",
        "window. It emits v15-compatible factorization certificates when a",
        "complete linear factorization is found, and exact blockers otherwise.",
        "",
        "## Results",
        "",
        f"- Cases: {payload['case_count']}",
        f"- Certificates generated: {payload['certificate_generated_count']}",
        f"- Blocked: {payload['blocked_count']}",
        "",
        "| case | status | roots | remaining | blocker |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["case_results"]:
        lines.append(
            f"| `{row['case_id']}` | {row['status']} | "
            f"`{row['linear_roots']}` | `{row['remaining_coeffs']}` | "
            f"{row['blocker'] or ''} |"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- Bounded rational search only.",
            "- No arbitrary factorization discovery claim.",
            "- No general root-count theorem claim.",
            "- No Forge compiler or eFrog behavior change.",
            "- No public theorem/proof/open-problem claim.",
        ]
    )
    return "\n".join(lines) + "\n"


def evidence_card(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "card_id": "machlib_rational_root_search_evidence_card_v16_2026_05_25",
        "title": "MachLib bounded rational-root search",
        "status": payload["status"],
        "visibility": "internal",
        "summary": "Bounded exact rational-root search emits v15 factorization certificates or exact blockers.",
        "case_count": payload["case_count"],
        "certificate_generated_count": payload["certificate_generated_count"],
        "blocked_count": payload["blocked_count"],
        "arbitrary_factorization_discovery": False,
        "complete_rational_root_search_claim": False,
        "root_count_induction_target_proved": False,
        "public_ready": False,
        "marketplace_ready": False,
        "production_marketplace_modified": False,
    }


def load_cases(path: Path | None) -> list[dict[str, Any]]:
    if path is None:
        return default_cases()
    data = json.loads(path.read_text())
    if isinstance(data, dict):
        return list(data.get("cases", []))
    if isinstance(data, list):
        return data
    raise ValueError("case file must be a list or object with cases")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases")
    parser.add_argument("--root-limit", type=int, default=6)
    parser.add_argument("--denominator-limit", type=int, default=4)
    parser.add_argument(
        "--out-json",
        default=f"product_readiness/{PACKET_ID}.json",
    )
    parser.add_argument(
        "--out-certificates",
        default=f"product_readiness/machlib_rational_root_certificates_v16_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-report",
        default=f"reports/{PACKET_ID}.md",
    )
    parser.add_argument(
        "--out-card",
        default=f"product_readiness/machlib_rational_root_search_evidence_card_v16_{DATE_TAG}.json",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    payload = run_cases(load_cases(Path(args.cases) if args.cases else None), args.root_limit, args.denominator_limit)
    if args.strict:
        if payload["status"] != "MACHLIB_RATIONAL_ROOT_SEARCH_V16_READY":
            raise SystemExit("rational-root search failed")
        if payload["certificate_generated_count"] < 5:
            raise SystemExit("expected at least five generated certificates")
        if payload["blocked_count"] < 1:
            raise SystemExit("expected at least one exact blocker")
        for key, value in payload["boundary"].items():
            if value is not False:
                raise SystemExit(f"boundary.{key} must be false")

    out_json = Path(args.out_json)
    out_certificates = Path(args.out_certificates)
    out_report = Path(args.out_report)
    out_card = Path(args.out_card)
    for path in [out_json, out_certificates, out_report, out_card]:
        path.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    out_certificates.write_text(
        json.dumps(
            {
                "date": DATE,
                "source": PACKET_ID,
                "certificates": payload["certificates"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    out_report.write_text(report(payload), encoding="utf-8")
    out_card.write_text(json.dumps(evidence_card(payload), indent=2) + "\n", encoding="utf-8")
    print(f"WROTE {out_json}")
    print(f"WROTE {out_certificates}")
    print(f"WROTE {out_report}")
    print(f"WROTE {out_card}")
    print(payload["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
