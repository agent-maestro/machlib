#!/usr/bin/env python3
"""Build MachLib root-union/cardinality/degree bridge packet v6 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_root_union_degree_packet_v6_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


PRIMITIVES = [
    {
        "name": "ProductDegreeBoundCert",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.ProductDegreeBoundCert",
        "status": "DEFINED",
        "purpose": "upper-bound direction for product degree arithmetic",
    },
    {
        "name": "ProductDegreeGrowthCert",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.ProductDegreeGrowthCert",
        "status": "DEFINED",
        "purpose": "growth/equality direction needed to bound product root-list cardinality",
    },
]


CHECKED_RESULTS = [
    {
        "id": "root_list_distinct_insert_unique_root",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.RootListDistinct_insertUniqueRoot",
        "statement": "unique insertion preserves duplicate-free root lists",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "root_list_distinct_union_unique_roots",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.RootListDistinct_unionUniqueRoots",
        "statement": "unique union preserves duplicate-free factor root lists",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "length_insert_unique_root_le_succ",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.length_insertUniqueRoot_le_succ",
        "statement": "unique insertion increases root-list length by at most one",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "length_insert_unique_root_eq_of_mem",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.length_insertUniqueRoot_eq_of_mem",
        "statement": "inserting an existing root leaves root-list length unchanged",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "length_union_unique_roots_le_add",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.length_unionUniqueRoots_le_add",
        "statement": "unique union length is bounded by sum of factor-list lengths",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "product_root_list_distinct_union",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRootListDistinct_union",
        "statement": "product root-list union is duplicate-free when factor lists are duplicate-free",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "product_root_list_length_union_le_add",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRootListLength_union_le_add",
        "statement": "product root-list union cardinality is bounded by sum of factor-list cardinalities",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "product_root_list_degree_bound_union_of_cert",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRootListDegreeBound_union_of_cert",
        "statement": "bounded factor root lists produce a bounded product root list under a product degree-growth certificate",
        "evidence_class": "MACHLIB_CHECKED_WITH_DEGREE_GROWTH_CERTIFICATE",
    },
]


UNLOCKED = [
    "root-list duplicate preservation is checked for product unions",
    "root-list union cardinality is checked against the sum of factor-list lengths",
    "product root-list degree bounds now have an explicit certificate interface",
    "the exact missing degree bridge is identified as product degree growth/equality, not merely an upper bound",
]


BLOCKED_NEXT = [
    "construct ProductDegreeGrowthCert for normalized nonzero convolution products",
    "prove exact degree arithmetic for nonzero normalized products",
    "connect LastNonzero normalization to nonzero product leading coefficient evidence",
    "derive zero-product splitting from MachLib's field substrate instead of the bridge axiom",
    "assemble the full RootCountInductionTarget proof",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_ROOT_UNION_DEGREE_PACKET_V6_READY",
        "date": DATE,
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "primitive_count": len(PRIMITIVES),
        "checked_result_count": len(CHECKED_RESULTS),
        "bridge_axiom_count": 1,
        "primitives": PRIMITIVES,
        "checked_results": CHECKED_RESULTS,
        "unlocked": UNLOCKED,
        "blocked_next": BLOCKED_NEXT,
        "depends_on": [
            "product_readiness/machlib_convolution_root_union_packet_v5_2026_05_25.json",
            "product_readiness/machlib_product_root_bridge_packet_v4_2026_05_25.json",
        ],
        "root_list_distinctness_status": "CHECKED_FOR_UNIQUE_UNION",
        "root_list_cardinality_status": "CHECKED_UNION_LENGTH_LE_FACTOR_LENGTH_SUM",
        "product_degree_growth_status": "CERTIFICATE_INTERFACE_DEFINED_NOT_CONSTRUCTED",
        "general_root_count_theorem_status": "BLOCKED_MISSING_PRODUCT_DEGREE_GROWTH_CERTIFICATE",
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
        "# MachLib Root-Union + Degree Packet v6",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet closes the root-list union side of the product induction",
        "bridge: duplicate preservation, union cardinality, and the product",
        "root-list degree-bound handoff are now checked. It also clarifies",
        "that the remaining product-degree bridge must be a growth/equality",
        "certificate, not only an upper-bound theorem.",
        "",
        "## Checked Results",
        "",
    ]
    for item in data["checked_results"]:
        lines.append(f"- `{item['id']}` — {item['statement']} ({item['evidence_class']})")
    lines.extend(["", "## Unlocked", ""])
    for item in data["unlocked"]:
        lines.append(f"- {item}")
    lines.extend(["", "## Still Blocked", ""])
    for item in data["blocked_next"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This does not prove the general polynomial root-count theorem.",
            "- Product degree growth/equality is defined as a certificate interface, not constructed generally.",
            "- The existing zero-product bridge axiom remains explicit.",
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
        if data["checked_result_count"] < 8:
            raise SystemExit("expected at least eight checked results")
        if data["bridge_axiom_count"] != 1:
            raise SystemExit("expected exactly one explicit bridge axiom")
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
