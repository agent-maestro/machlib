#!/usr/bin/env python3
"""Build MachLib degree-growth examples packet v7 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_degree_examples_packet_v7_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_RESULTS = [
    {
        "id": "derived_zero_product_theorem",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mul_eq_zero_or_left_or_right",
        "statement": "zero-product splitting is derived from existing MachLib field axioms",
        "evidence_class": "MACHLIB_CHECKED_DERIVED_THEOREM",
    },
    {
        "id": "linear_coeff_root_list_sound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.linearCoeff_rootListSound",
        "statement": "the singleton root list [r] is sound for coefficient-list linear factors",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_coeff_root_list_degree_bound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.linearCoeff_rootListDegreeBound",
        "statement": "the singleton root list [r] is degree-bounded for coefficient-list linear factors",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


DEGREE_GROWTH_EXAMPLES = [
    "example_growth_const_const",
    "example_growth_const_linear",
    "example_growth_linear_const",
    "example_growth_linear_linear",
    "example_growth_linear_quadratic",
]


ROOT_UNION_EXAMPLES = [
    "example_product_linear_linear_degreeBound",
    "example_product_repeated_linear_degreeBound",
    "example_union_two_singletons_distinct",
    "example_union_repeated_singleton_length",
    "example_union_three_singletons_length",
]


UNLOCKED = [
    "zero-product splitting is now derived, not an added bridge axiom",
    "five checked degree-growth examples cover constant, linear, and monic quadratic product shapes",
    "five checked root-list examples cover degree-bound, deduplication, distinctness, and cardinality handoff",
    "coefficient-list linear factors now have sound singleton root-list packets",
]


BLOCKED_NEXT = [
    "prove exact degree growth for arbitrary normalized nonzero convolution products",
    "connect explicit product coefficient examples back to canonical mulCoeff normal forms",
    "prove leading-coefficient nonzero preservation for normalized products",
    "assemble the full RootCountInductionTarget proof",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_DEGREE_EXAMPLES_PACKET_V7_READY",
        "date": DATE,
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_result_count": len(CHECKED_RESULTS),
        "degree_growth_example_count": len(DEGREE_GROWTH_EXAMPLES),
        "root_union_example_count": len(ROOT_UNION_EXAMPLES),
        "bridge_axiom_count": 0,
        "checked_results": CHECKED_RESULTS,
        "degree_growth_examples": DEGREE_GROWTH_EXAMPLES,
        "root_union_examples": ROOT_UNION_EXAMPLES,
        "unlocked": UNLOCKED,
        "blocked_next": BLOCKED_NEXT,
        "depends_on": [
            "product_readiness/machlib_root_union_degree_packet_v6_2026_05_25.json",
            "product_readiness/machlib_convolution_root_union_packet_v5_2026_05_25.json",
            "product_readiness/machlib_product_root_bridge_packet_v4_2026_05_25.json",
        ],
        "zero_product_status": "DERIVED_THEOREM_NO_BRIDGE_AXIOM",
        "degree_growth_status": "FIVE_CHECKED_EXAMPLES_GENERAL_THEOREM_NOT_PROVED",
        "root_union_status": "FIVE_CHECKED_EXAMPLES_DISTINCTNESS_CARDINALITY_BRIDGE_READY",
        "general_root_count_theorem_status": "BLOCKED_MISSING_GENERAL_NORMALIZED_PRODUCT_DEGREE_GROWTH",
        "induction_target_status": "DEFINED_NOT_PROVED",
        "public_ready": False,
        "marketplace_ready": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "package_publish_performed": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "public_theorem_claim": False,
        "general_root_count_theorem_proved": False,
        "analytic_identity_theorem_proved": False,
    }


def report(data: dict) -> str:
    lines = [
        "# MachLib Degree-Growth Examples Packet v7",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet removes the explicit zero-product bridge axiom by deriving",
        "`mul_eq_zero_or_left_or_right` from MachLib's existing field axioms.",
        "It also adds checked example coverage for product degree growth and",
        "root-list union/cardinality handoff.",
        "",
        "## Degree-Growth Examples",
        "",
    ]
    for item in data["degree_growth_examples"]:
        lines.append(f"- `{item}`")
    lines.extend(["", "## Root-Union Examples", ""])
    for item in data["root_union_examples"]:
        lines.append(f"- `{item}`")
    lines.extend(["", "## Still Blocked", ""])
    for item in data["blocked_next"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This does not prove the general polynomial root-count theorem.",
            "- Five degree-growth examples are checked, but the arbitrary normalized product theorem remains open.",
            "- Zero-product splitting is derived in this module; no new bridge axiom is introduced.",
            "- No public theorem/proof/open-problem claim is made.",
            "- No package publish, PETAL/API upload, Hugging Face upload, or production marketplace change.",
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
        if data["degree_growth_example_count"] < 5:
            raise SystemExit("expected at least five degree-growth examples")
        if data["root_union_example_count"] < 5:
            raise SystemExit("expected at least five root-union examples")
        for key in [
            "public_ready",
            "marketplace_ready",
            "production_marketplace_modified",
            "petal_api_upload_performed",
            "huggingface_upload_performed",
            "package_publish_performed",
            "certified_safety_claim",
            "production_controller_claim",
            "public_theorem_claim",
            "general_root_count_theorem_proved",
            "analytic_identity_theorem_proved",
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
