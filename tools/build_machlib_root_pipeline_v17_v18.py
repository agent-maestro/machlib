#!/usr/bin/env python3
"""Build MachLib residual root packets v17 and quadratic classifier v18."""

from __future__ import annotations

import argparse
import importlib.util
import json
import math
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


DATE = "2026-05-25"
DATE_TAG = "2026_05_25"
PACKET_ID = "machlib_polynomial_root_pipeline_v17_v18_2026_05_25"
V16_TOOL = Path(__file__).with_name("run_machlib_rational_root_search_v16.py")


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


def load_v16():
    spec = importlib.util.spec_from_file_location("machlib_rational_root_search_v16", V16_TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


v16 = load_v16()
v15 = v16.v15


def is_fraction_square(value: Fraction) -> bool:
    if value < 0:
        return False
    numerator_root = math.isqrt(value.numerator)
    denominator_root = math.isqrt(value.denominator)
    return numerator_root * numerator_root == value.numerator and denominator_root * denominator_root == value.denominator


def sqrt_fraction(value: Fraction) -> Fraction:
    if not is_fraction_square(value):
        raise ValueError("fraction is not a square")
    return Fraction(math.isqrt(value.numerator), math.isqrt(value.denominator))


def classify_quadratic(coeffs: list[Fraction]) -> dict[str, Any]:
    coeffs = v15.normalize(coeffs)
    if len(coeffs) != 3:
        return {
            "classification": "NOT_QUADRATIC",
            "degree": max(len(coeffs) - 1, 0),
            "discriminant": None,
            "rational_roots": [],
            "blocker": "RESIDUAL_NOT_DEGREE_TWO",
        }
    c, b, a = coeffs
    if a == 0:
        return {
            "classification": "NOT_NORMALIZED_QUADRATIC",
            "degree": max(len(coeffs) - 1, 0),
            "discriminant": None,
            "rational_roots": [],
            "blocker": "LEADING_COEFFICIENT_ZERO",
        }
    discriminant = b * b - 4 * a * c
    if discriminant < 0:
        return {
            "classification": "NEGATIVE_DISCRIMINANT_NO_REAL_ROOTS_IN_QUADRATIC_STUB",
            "degree": 2,
            "discriminant": v15.encode_fraction(discriminant),
            "rational_roots": [],
            "blocker": "NEGATIVE_DISCRIMINANT",
        }
    if is_fraction_square(discriminant):
        root_disc = sqrt_fraction(discriminant)
        roots = [(-b - root_disc) / (2 * a), (-b + root_disc) / (2 * a)]
        dedup = v15.unique_roots(roots)
        return {
            "classification": "RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE",
            "degree": 2,
            "discriminant": v15.encode_fraction(discriminant),
            "rational_roots": v16.encode_coeffs(dedup),
            "blocker": None,
        }
    return {
        "classification": "IRRATIONAL_ROOTS_BLOCKED_IN_RATIONAL_LAYER",
        "degree": 2,
        "discriminant": v15.encode_fraction(discriminant),
        "rational_roots": [],
        "blocker": "DISCRIMINANT_NOT_RATIONAL_SQUARE",
    }


def residual_packet(case: dict[str, Any], case_result: dict[str, Any]) -> dict[str, Any]:
    remaining = v16.parse_coeffs(case_result["remaining_coeffs"])
    classification = classify_quadratic(remaining)
    return {
        "case_id": case_result["case_id"],
        "description": case_result["description"],
        "input_coeffs": case_result["input_coeffs"],
        "factored_roots": case_result["linear_roots"],
        "remaining_coeffs": case_result["remaining_coeffs"],
        "search_status": case_result["status"],
        "search_blocker": case_result["blocker"],
        "residual_degree": max(len(remaining) - 1, 0),
        "quadratic_classification": classification,
        "root_count_induction_target_proved": False,
        "arbitrary_factorization_discovery": False,
        "complete_rational_root_search_claim": False,
    }


def pipeline_cases() -> list[dict[str, Any]]:
    return v16.default_cases() + [
        {
            "case_id": "quadratic_irrational_roots_v18",
            "description": "x^2 - 2",
            "coeffs": [-2, 0, 1],
            "expect": "BLOCKED",
        },
        {
            "case_id": "quadratic_large_rational_root_outside_window_v18",
            "description": "(x-10)(x+1) with root limit 6",
            "coeffs": [-10, 9, 1],
            "expect": "BLOCKED",
        },
        {
            "case_id": "quadratic_rational_square_outside_window_v18",
            "description": "(x-7)(x-8) with root limit 6",
            "coeffs": [56, -15, 1],
            "expect": "BLOCKED",
        },
    ]


def build_payload(root_limit: int, denominator_limit: int) -> dict[str, Any]:
    cases = pipeline_cases()
    search = v16.run_cases(cases, root_limit, denominator_limit)
    residuals = [residual_packet(case, row) for case, row in zip(cases, search["case_results"], strict=True)]
    quadratic_rows = [
        row for row in residuals
        if row["quadratic_classification"]["classification"] != "NOT_QUADRATIC"
    ]
    status = "MACHLIB_POLYNOMIAL_ROOT_PIPELINE_V17_V18_READY"
    if search["status"] != "MACHLIB_RATIONAL_ROOT_SEARCH_V16_READY":
        status = "MACHLIB_POLYNOMIAL_ROOT_PIPELINE_V17_V18_FAIL"
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": status,
        "root_limit": root_limit,
        "denominator_limit": denominator_limit,
        "v16_search_status": search["status"],
        "case_count": search["case_count"],
        "certificate_generated_count": search["certificate_generated_count"],
        "blocked_count": search["blocked_count"],
        "residual_packet_count": len(residuals),
        "quadratic_classification_count": len(quadratic_rows),
        "search": search,
        "residual_packets": residuals,
        "quadratic_classifications": quadratic_rows,
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "arbitrary_factorization_discovery": False,
        "complete_rational_root_search_claim": False,
        "quadratic_closed_form_theorem_claim": False,
        "boundary": {key: False for key in BOUNDARY_FALSE_KEYS},
    }


def report(payload: dict[str, Any]) -> str:
    lines = [
        "# MachLib Polynomial Root Pipeline v17/v18",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Scope",
        "",
        "v17 adds residual packets for every bounded rational-root search case.",
        "v18 adds a small quadratic classifier for residual degree-two cases.",
        "This is still a bounded exact arithmetic pipeline, not arbitrary root discovery.",
        "",
        "## Summary",
        "",
        f"- Cases: {payload['case_count']}",
        f"- Certificates generated: {payload['certificate_generated_count']}",
        f"- Blocked: {payload['blocked_count']}",
        f"- Residual packets: {payload['residual_packet_count']}",
        f"- Quadratic classifications: {payload['quadratic_classification_count']}",
        "",
        "| case | search | residual | quadratic classification | blocker |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in payload["residual_packets"]:
        q = row["quadratic_classification"]
        lines.append(
            f"| `{row['case_id']}` | {row['search_status']} | "
            f"`{row['remaining_coeffs']}` | {q['classification']} | "
            f"{row['search_blocker'] or q['blocker'] or ''} |"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- Bounded rational search only.",
            "- Quadratic classifier only classifies residuals; it does not prove a general root-count theorem.",
            "- No arbitrary factorization discovery claim.",
            "- No Forge compiler or eFrog behavior change.",
            "- No public theorem/proof/open-problem claim.",
        ]
    )
    return "\n".join(lines) + "\n"


def card(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "card_id": "machlib_polynomial_root_pipeline_evidence_card_v18_2026_05_25",
        "title": "MachLib polynomial root pipeline",
        "status": payload["status"],
        "visibility": "internal",
        "summary": "Coefficient input flows through bounded rational search, residual packets, and quadratic residual classification.",
        "case_count": payload["case_count"],
        "certificate_generated_count": payload["certificate_generated_count"],
        "blocked_count": payload["blocked_count"],
        "residual_packet_count": payload["residual_packet_count"],
        "quadratic_classification_count": payload["quadratic_classification_count"],
        "public_ready": False,
        "marketplace_ready": False,
        "root_count_induction_target_proved": False,
        "production_marketplace_modified": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root-limit", type=int, default=6)
    parser.add_argument("--denominator-limit", type=int, default=4)
    parser.add_argument(
        "--out-json",
        default=f"product_readiness/{PACKET_ID}.json",
    )
    parser.add_argument(
        "--out-residuals",
        default=f"product_readiness/machlib_residual_root_packets_v17_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-quadratics",
        default=f"product_readiness/machlib_quadratic_classifier_v18_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-card",
        default=f"product_readiness/machlib_polynomial_root_pipeline_evidence_card_v18_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-report",
        default=f"reports/{PACKET_ID}.md",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    payload = build_payload(args.root_limit, args.denominator_limit)
    if args.strict:
        if payload["status"] != "MACHLIB_POLYNOMIAL_ROOT_PIPELINE_V17_V18_READY":
            raise SystemExit("root pipeline failed")
        if payload["residual_packet_count"] < 9:
            raise SystemExit("expected at least nine residual packets")
        if payload["quadratic_classification_count"] < 3:
            raise SystemExit("expected at least three quadratic classifications")
        for key, value in payload["boundary"].items():
            if value is not False:
                raise SystemExit(f"boundary.{key} must be false")

    paths = {
        "json": Path(args.out_json),
        "residuals": Path(args.out_residuals),
        "quadratics": Path(args.out_quadratics),
        "card": Path(args.out_card),
        "report": Path(args.out_report),
    }
    for path in paths.values():
        path.parent.mkdir(parents=True, exist_ok=True)
    paths["json"].write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    paths["residuals"].write_text(
        json.dumps(
            {
                "date": DATE,
                "source": PACKET_ID,
                "residual_packets": payload["residual_packets"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    paths["quadratics"].write_text(
        json.dumps(
            {
                "date": DATE,
                "source": PACKET_ID,
                "quadratic_classifications": payload["quadratic_classifications"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    paths["card"].write_text(json.dumps(card(payload), indent=2) + "\n", encoding="utf-8")
    paths["report"].write_text(report(payload), encoding="utf-8")
    for path in paths.values():
        print(f"WROTE {path}")
    print(payload["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
