#!/usr/bin/env python3
"""Build MachLib exact product-degree normalizer packet v8 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_exact_product_degree_normalizer_packet_v8_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


NORMALIZER_RESULTS = [
    "normalizeCoeff_nil",
    "normalizeCoeff_singleton_zero",
    "normalizeCoeff_singleton_nonzero",
    "normalizeCoeff_of_LastNonzero",
    "degreeBound_normalizeCoeff_eq_of_LastNonzero",
    "normalizeCoeff_linearCoeff",
    "scaledLinearCoeff_evalSound",
    "linearLinearCoeff_evalSound",
    "linearQuadraticCoeff_evalSound",
]


EXAMPLE_CLASSES = {
    "quadratic_times_linear": [
        "example_v8_quadratic_linear_1",
        "example_v8_quadratic_linear_2",
        "example_v8_quadratic_linear_3",
        "example_v8_quadratic_linear_4",
        "example_v8_quadratic_linear_5",
    ],
    "quadratic_times_quadratic": [
        "example_v8_quadratic_quadratic_1",
        "example_v8_quadratic_quadratic_2",
        "example_v8_quadratic_quadratic_3",
        "example_v8_quadratic_quadratic_4",
        "example_v8_quadratic_quadratic_5",
    ],
    "repeated_roots": [
        "example_v8_repeated_root_1",
        "example_v8_repeated_root_2",
        "example_v8_repeated_root_3",
        "example_v8_repeated_root_4",
        "example_v8_repeated_root_5",
    ],
    "constant_scale_products": [
        "example_v8_scaled_product_1",
        "example_v8_scaled_product_2",
        "example_v8_scaled_product_3",
        "example_v8_scaled_product_4",
        "example_v8_scaled_product_5",
    ],
    "trailing_zero_cleanup": [
        "example_v8_cleanup_1",
        "example_v8_cleanup_2",
        "example_v8_cleanup_3",
        "example_v8_cleanup_4",
        "example_v8_cleanup_5",
    ],
}


ROOT_PACKET_EXAMPLES = [
    {
        "id": "linear_linear",
        "shape": "(x-r)(x-s)",
        "lean_name": "example_v8_root_packet_linear_linear",
        "evidence_class": "CHECKED_DEGREE_BOUND_PACKET",
    },
    {
        "id": "repeated_linear",
        "shape": "(x-r)^2",
        "lean_name": "example_v8_root_packet_repeated_linear",
        "evidence_class": "CHECKED_DEGREE_BOUND_PACKET",
    },
    {
        "id": "staged_triple",
        "shape": "(x-r)(x-s)(x-t)",
        "lean_name": "example_v8_root_packet_staged_triple",
        "evidence_class": "CHECKED_STAGED_DEGREE_BOUND_PACKET",
    },
    {
        "id": "constant_times_linear",
        "shape": "constant * (x-r)",
        "lean_name": "example_v8_root_packet_scaled_linear",
        "evidence_class": "CHECKED_DEGREE_BOUND_PACKET",
    },
    {
        "id": "linear_times_quadratic_with_certificate",
        "shape": "(x-r) * monic_quadratic(a,b)",
        "lean_name": "example_v8_root_packet_linear_quadratic_with_certificate",
        "evidence_class": "CHECKED_CERTIFICATE_INTERFACE",
    },
]


BLOCKED_NEXT = [
    "prove full product degree growth for arbitrary normalized nonzero convolution products",
    "prove normalized leading-coefficient preservation for mulCoeff without specializing product shapes",
    "derive root-list union cardinality strong enough for the general induction theorem",
    "replace certificate interfaces for quadratic root packets with complete checked root enumerators",
    "assemble RootCountInductionTarget after product-degree arithmetic is general",
]


def payload() -> dict:
    example_count = sum(len(v) for v in EXAMPLE_CLASSES.values())
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_EXACT_PRODUCT_DEGREE_NORMALIZER_PACKET_V8_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "normalizer_layer": {
            "normalize_coeff": "normalizeCoeff",
            "normalized_product_output": "normalizedProductCoeff",
            "already_normalized_degree_preservation": "degreeBound_normalizeCoeff_eq_of_LastNonzero",
            "checked_result_count": len(NORMALIZER_RESULTS),
            "checked_results": NORMALIZER_RESULTS,
        },
        "targeted_example_class_count": len(EXAMPLE_CLASSES),
        "targeted_example_count": example_count,
        "targeted_examples": EXAMPLE_CLASSES,
        "root_packet_example_count": len(ROOT_PACKET_EXAMPLES),
        "root_packet_examples": ROOT_PACKET_EXAMPLES,
        "degree_theorem_feasibility_split": {
            "already_normalized_normalizer_preservation": "CHECKED",
            "linear_times_quadratic_eval_soundness": "CHECKED_SPECIALIZED",
            "linear_times_arbitrary_normalized_polynomial": "NOT_YET_PROVED",
            "arbitrary_normalized_product_degree_growth": "NOT_YET_PROVED",
        },
        "blocked_next": BLOCKED_NEXT,
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "analytic_identity_theorem_proved": False,
        "public_theorem_claim": False,
        "marketplace_ready": False,
        "public_ready": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "package_publish_performed": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
    }


def report(data: dict) -> str:
    lines = [
        "# MachLib Exact Product Degree Normalizer Packet v8",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What Changed",
        "",
        "v8 adds a small coefficient normalizer and names the normalized product output.",
        "It then expands the checked product-degree example suite across five targeted",
        "classes: quadratic-linear, quadratic-quadratic, repeated roots, constant-scale",
        "products, and cleanup cases.",
        "",
        "## Normalizer Layer",
        "",
    ]
    for name in data["normalizer_layer"]["checked_results"]:
        lines.append(f"- `{name}`")
    lines.extend(["", "## Targeted Example Classes", ""])
    for class_name, examples in data["targeted_examples"].items():
        lines.append(f"- `{class_name}`: {len(examples)} checked examples")
    lines.extend(["", "## Root Packet Examples", ""])
    for item in data["root_packet_examples"]:
        lines.append(f"- `{item['lean_name']}`: {item['shape']} ({item['evidence_class']})")
    lines.extend(["", "## Still Blocked", ""])
    for item in data["blocked_next"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This packet does not prove the general polynomial root-count theorem.",
            "- It does not prove arbitrary normalized product degree growth.",
            "- Certificate interfaces remain explicit where full root enumeration is not available.",
            "- No public theorem/proof/open-problem claim is made.",
            "- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-json", default=f"product_readiness/{PACKET_ID}.json")
    parser.add_argument("--out-report", default=f"reports/{PACKET_ID}.md")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    data = payload()
    if args.strict:
        if data["bridge_axiom_count"] != 0:
            raise SystemExit("expected no bridge axioms")
        if data["targeted_example_count"] < 25:
            raise SystemExit("expected at least 25 targeted examples")
        if data["root_packet_example_count"] < 5:
            raise SystemExit("expected at least 5 root packet examples")
        for class_name, examples in data["targeted_examples"].items():
            if len(examples) < 5:
                raise SystemExit(f"{class_name} needs at least 5 examples")
        for key in [
            "general_root_count_theorem_proved",
            "analytic_identity_theorem_proved",
            "public_theorem_claim",
            "marketplace_ready",
            "public_ready",
            "production_marketplace_modified",
            "petal_api_upload_performed",
            "huggingface_upload_performed",
            "package_publish_performed",
            "certified_safety_claim",
            "production_controller_claim",
        ]:
            if data[key] is not False:
                raise SystemExit(f"{key} must be false")

    out_json = Path(args.out_json)
    out_report = Path(args.out_report)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_report.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    out_report.write_text(report(data), encoding="utf-8")
    print(f"WROTE {out_json}")
    print(f"WROTE {out_report}")
    print(data["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
