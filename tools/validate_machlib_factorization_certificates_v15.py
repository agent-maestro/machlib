#!/usr/bin/env python3
"""Validate MachLib factorization certificates for factored root packets v15."""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any


DATE = "2026-05-25"
DATE_TAG = "2026_05_25"
PACKET_ID = "machlib_factorization_certificate_import_v15_2026_05_25"


BOUNDARY_FALSE_KEYS = [
    "general_root_count_theorem_proved",
    "root_count_induction_target_proved",
    "arbitrary_root_discovery_claim",
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


def parse_fraction(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise ValueError("boolean is not a coefficient")
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, float):
        return Fraction(str(value))
    if isinstance(value, str):
        return Fraction(value)
    raise ValueError(f"unsupported coefficient value: {value!r}")


def encode_fraction(value: Fraction) -> int | str:
    if value.denominator == 1:
        return value.numerator
    return f"{value.numerator}/{value.denominator}"


def normalize(coeffs: list[Fraction]) -> list[Fraction]:
    trimmed = list(coeffs)
    while trimmed and trimmed[-1] == 0:
        trimmed.pop()
    return trimmed


def mul_coeff(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    if not left or not right:
        return []
    out = [Fraction(0, 1)] * (len(left) + len(right) - 1)
    for i, a in enumerate(left):
        for j, b in enumerate(right):
            out[i + j] += a * b
    return out


def linear_factor(root: Fraction) -> list[Fraction]:
    return [-root, Fraction(1, 1)]


def unique_roots(roots: list[Fraction]) -> list[Fraction]:
    out: list[Fraction] = []
    for root in roots:
        if root not in out:
            out.append(root)
    return out


def evaluate(coeffs: list[Fraction], x: Fraction) -> Fraction:
    total = Fraction(0, 1)
    power = Fraction(1, 1)
    for coeff in coeffs:
        total += coeff * power
        power *= x
    return total


@dataclass
class ValidationResult:
    certificate_id: str
    status: str
    computed_coeffs: list[int | str]
    computed_roots: list[int | str]
    degree_bound: int
    expected_root_count: int
    failures: list[str]
    warnings: list[str]


def validate_certificate(cert: dict[str, Any]) -> ValidationResult:
    failures: list[str] = []
    warnings: list[str] = []
    cid = str(cert.get("certificate_id", "UNKNOWN_CERTIFICATE"))

    constant = parse_fraction(cert.get("constant", 0))
    roots = [parse_fraction(x) for x in cert.get("linear_roots", [])]
    expected_coeffs = [parse_fraction(x) for x in cert.get("expected_product_coeffs", [])]
    coeffs = [parse_fraction(x) for x in cert.get("coeffs", expected_coeffs)]
    expected_roots = [parse_fraction(x) for x in cert.get("expected_dedup_roots", unique_roots(roots))]

    if constant == 0:
        failures.append("constant must be nonzero")

    computed = [constant]
    for root in roots:
        computed = mul_coeff(computed, linear_factor(root))
    computed = normalize(computed)

    if computed != normalize(expected_coeffs):
        failures.append("expected_product_coeffs mismatch")
    if computed != normalize(coeffs):
        failures.append("coeffs mismatch")

    dedup = unique_roots(roots)
    if dedup != expected_roots:
        failures.append("expected_dedup_roots mismatch")

    for root in dedup:
        if evaluate(computed, root) != 0:
            failures.append(f"root {encode_fraction(root)} does not evaluate to zero")

    degree_bound = max(len(computed) - 1, 0)
    if len(dedup) > degree_bound:
        failures.append("deduplicated root count exceeds degree bound")
    if len(dedup) < len(roots):
        warnings.append("repeated roots deduplicated")

    if cert.get("normalized") is not True:
        failures.append("normalized must be true")
    if computed and computed[-1] == 0:
        failures.append("computed coefficient list has trailing zero")

    status = "PASS" if not failures else "FAIL"
    return ValidationResult(
        certificate_id=cid,
        status=status,
        computed_coeffs=[encode_fraction(x) for x in computed],
        computed_roots=[encode_fraction(x) for x in dedup],
        degree_bound=degree_bound,
        expected_root_count=len(dedup),
        failures=failures,
        warnings=warnings,
    )


def default_certificates() -> list[dict[str, Any]]:
    return [
        {
            "certificate_id": "linear_pair_distinct_v15",
            "description": "(x-1)(x-3)",
            "coeffs": [3, -4, 1],
            "constant": 1,
            "linear_roots": [1, 3],
            "expected_product_coeffs": [3, -4, 1],
            "expected_dedup_roots": [1, 3],
            "normalized": True,
        },
        {
            "certificate_id": "repeated_cubic_v15",
            "description": "(x-2)^3",
            "coeffs": [-8, 12, -6, 1],
            "constant": 1,
            "linear_roots": [2, 2, 2],
            "expected_product_coeffs": [-8, 12, -6, 1],
            "expected_dedup_roots": [2],
            "normalized": True,
        },
        {
            "certificate_id": "scaled_pair_v15",
            "description": "2(x-1)(x-4)",
            "coeffs": [8, -10, 2],
            "constant": 2,
            "linear_roots": [1, 4],
            "expected_product_coeffs": [8, -10, 2],
            "expected_dedup_roots": [1, 4],
            "normalized": True,
        },
        {
            "certificate_id": "constant_only_v15",
            "description": "7",
            "coeffs": [7],
            "constant": 7,
            "linear_roots": [],
            "expected_product_coeffs": [7],
            "expected_dedup_roots": [],
            "normalized": True,
        },
        {
            "certificate_id": "staged_triple_linear_v15",
            "description": "(x-1)(x-2)(x-5)",
            "coeffs": [-10, 17, -8, 1],
            "constant": 1,
            "linear_roots": [1, 2, 5],
            "expected_product_coeffs": [-10, 17, -8, 1],
            "expected_dedup_roots": [1, 2, 5],
            "normalized": True,
        },
        {
            "certificate_id": "fractional_roots_v15",
            "description": "3(x-1/2)(x+1)",
            "coeffs": ["-3/2", "3/2", 3],
            "constant": 3,
            "linear_roots": ["1/2", -1],
            "expected_product_coeffs": ["-3/2", "3/2", 3],
            "expected_dedup_roots": ["1/2", -1],
            "normalized": True,
        },
        {
            "certificate_id": "linear_known_quadratic_shape_v15",
            "description": "(x-3)(x-1)(x-2), treated as linear times known quadratic",
            "coeffs": [-6, 11, -6, 1],
            "constant": 1,
            "linear_roots": [3, 1, 2],
            "expected_product_coeffs": [-6, 11, -6, 1],
            "expected_dedup_roots": [3, 1, 2],
            "normalized": True,
        },
    ]


def load_certificates(path: Path | None) -> list[dict[str, Any]]:
    if path is None:
        return default_certificates()
    data = json.loads(path.read_text())
    if isinstance(data, dict):
        return list(data.get("certificates", []))
    if isinstance(data, list):
        return data
    raise ValueError("certificate file must be a list or object with certificates")


def build_outputs(certificates: list[dict[str, Any]]) -> dict[str, Any]:
    results = [validate_certificate(cert) for cert in certificates]
    pass_count = sum(1 for row in results if row.status == "PASS")
    fail_count = len(results) - pass_count
    warnings = sum(len(row.warnings) for row in results)
    payload = {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_FACTORIZATION_CERTIFICATE_IMPORT_V15_READY"
        if fail_count == 0
        else "MACHLIB_FACTORIZATION_CERTIFICATE_IMPORT_V15_FAIL",
        "certificate_count": len(results),
        "pass_count": pass_count,
        "fail_count": fail_count,
        "warning_count": warnings,
        "supported_certificate_class": "nonzero_constant_times_explicit_linear_factors",
        "arbitrary_factorization_discovery": False,
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "results": [row.__dict__ for row in results],
        "boundary": {key: False for key in BOUNDARY_FALSE_KEYS},
    }
    return payload


def report(payload: dict[str, Any]) -> str:
    lines = [
        "# MachLib Factorization Certificate Import v15",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Scope",
        "",
        "This validates explicit factorization certificates for nonzero constants",
        "times linear factors. It does not discover factorizations and does not",
        "prove the arbitrary root-count target.",
        "",
        "## Results",
        "",
        f"- Certificates: {payload['certificate_count']}",
        f"- PASS: {payload['pass_count']}",
        f"- FAIL: {payload['fail_count']}",
        f"- WARNINGS: {payload['warning_count']}",
        "",
        "| certificate | status | degree | dedup roots | notes |",
        "| --- | --- | ---: | ---: | --- |",
    ]
    for row in payload["results"]:
        notes = "; ".join(row["warnings"] + row["failures"]) or "ok"
        lines.append(
            f"| `{row['certificate_id']}` | {row['status']} | "
            f"{row['degree_bound']} | {row['expected_root_count']} | {notes} |"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- No arbitrary root discovery claim.",
            "- No `RootCountInductionTarget` proof claim.",
            "- No Forge compiler or eFrog behavior change.",
            "- No public theorem/proof/open-problem claim.",
            "- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.",
        ]
    )
    return "\n".join(lines) + "\n"


def evidence_card(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "card_id": "machlib_factored_root_evidence_card_v15_2026_05_25",
        "title": "MachLib factored root packet import",
        "status": payload["status"],
        "visibility": "internal",
        "summary": (
            "Validated explicit factorization certificates for nonzero constants "
            "times linear factors and produced deduplicated finite-root packet evidence."
        ),
        "certificate_count": payload["certificate_count"],
        "pass_count": payload["pass_count"],
        "fail_count": payload["fail_count"],
        "root_count_induction_target_proved": False,
        "arbitrary_factorization_discovery": False,
        "public_ready": False,
        "marketplace_ready": False,
        "production_marketplace_modified": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--certificates")
    parser.add_argument(
        "--out-examples",
        default=f"product_readiness/machlib_factorization_certificate_examples_v15_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-json",
        default=f"product_readiness/{PACKET_ID}.json",
    )
    parser.add_argument(
        "--out-report",
        default=f"reports/{PACKET_ID}.md",
    )
    parser.add_argument(
        "--out-card",
        default=f"product_readiness/machlib_factored_root_evidence_card_v15_{DATE_TAG}.json",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    certificates = load_certificates(Path(args.certificates) if args.certificates else None)
    payload = build_outputs(certificates)

    if args.strict:
        if payload["fail_count"] != 0:
            raise SystemExit("factorization certificate validation failed")
        if payload["certificate_count"] < 7:
            raise SystemExit("expected at least seven certificates")
        for key, value in payload["boundary"].items():
            if value is not False:
                raise SystemExit(f"boundary.{key} must be false")

    examples_path = Path(args.out_examples)
    json_path = Path(args.out_json)
    report_path = Path(args.out_report)
    card_path = Path(args.out_card)
    for path in [examples_path, json_path, report_path, card_path]:
        path.parent.mkdir(parents=True, exist_ok=True)

    examples_path.write_text(
        json.dumps({"date": DATE, "certificates": certificates}, indent=2) + "\n",
        encoding="utf-8",
    )
    json_path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    report_path.write_text(report(payload), encoding="utf-8")
    card_path.write_text(json.dumps(evidence_card(payload), indent=2) + "\n", encoding="utf-8")
    print(f"WROTE {examples_path}")
    print(f"WROTE {json_path}")
    print(f"WROTE {report_path}")
    print(f"WROTE {card_path}")
    print(payload["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
