#!/usr/bin/env python3
"""Build MachLib convolution/root-union packet v5 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_convolution_root_union_packet_v5_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


PRIMITIVES = [
    {
        "name": "addCoeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.addCoeff",
        "status": "DEFINED",
        "purpose": "pointwise coefficient-list addition with missing coefficients treated as zero",
    },
    {
        "name": "scalarMulCoeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.scalarMulCoeff",
        "status": "DEFINED",
        "purpose": "scalar multiplication over coefficient lists",
    },
    {
        "name": "shiftCoeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.shiftCoeff",
        "status": "DEFINED",
        "purpose": "multiply a coefficient list by x through a one-place shift",
    },
    {
        "name": "mulCoeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mulCoeff",
        "status": "DEFINED",
        "purpose": "recursive coefficient-list convolution",
    },
    {
        "name": "insertUniqueRoot",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.insertUniqueRoot",
        "status": "DEFINED",
        "purpose": "list-level duplicate control for root packets",
    },
    {
        "name": "unionUniqueRoots",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.unionUniqueRoots",
        "status": "DEFINED",
        "purpose": "root-list union used by product root-list soundness",
    },
    {
        "name": "ProductDegreeBoundTarget",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.ProductDegreeBoundTarget",
        "status": "DEFINED_NOT_PROVED",
        "purpose": "exact degree arithmetic target for product induction",
    },
]


CHECKED_RESULTS = [
    {
        "id": "eval_add_coeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_addCoeff",
        "statement": "coefficient-list addition evaluates to pointwise addition",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "eval_scalar_mul_coeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_scalarMulCoeff",
        "statement": "coefficient scalar multiplication evaluates to scalar multiplication",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "eval_shift_coeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_shiftCoeff",
        "statement": "coefficient shift evaluates as multiplication by x",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "eval_mul_coeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_mulCoeff",
        "statement": "recursive convolution evaluates as product of operand evaluations",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "mul_coeff_eval_sound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mulCoeff_evalSound",
        "statement": "mulCoeff produces a semantic product certificate",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "mem_insert_unique_root_of_mem",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mem_insertUniqueRoot_of_mem",
        "statement": "existing root membership survives unique insertion",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "mem_insert_unique_root_self",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mem_insertUniqueRoot_self",
        "statement": "inserted root is present after unique insertion",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "mem_union_unique_roots_left",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mem_unionUniqueRoots_left",
        "statement": "left root-list membership survives unique union",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "mem_union_unique_roots_right",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mem_unionUniqueRoots_right",
        "statement": "right root-list membership survives unique union",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "product_root_list_sound_union",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRootListSound_union",
        "statement": "product root-list soundness transfers to union of factor root lists",
        "evidence_class": "MACHLIB_CHECKED_WITH_BRIDGE_AXIOM",
    },
    {
        "id": "mul_coeff_root_list_sound_union",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mulCoeffRootListSound_union",
        "statement": "convolution product root-list soundness transfers to union of factor root lists",
        "evidence_class": "MACHLIB_CHECKED_WITH_BRIDGE_AXIOM",
    },
    {
        "id": "product_degree_bound_nil_left",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productDegreeBound_nil_left",
        "statement": "product degree arithmetic base case for empty left operand",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


UNLOCKED = [
    "coefficient-list convolution now has checked evaluation soundness",
    "mulCoeff can feed the existing product-root splitting bridge",
    "root-list union/dedup primitives now preserve factor-list membership",
    "product root-list soundness can be built from sound factor root lists",
    "degree arithmetic has a named target plus a checked empty-left base case",
]


BLOCKED_NEXT = [
    "prove full ProductDegreeBoundTarget for normalized convolution products",
    "prove RootListDistinct preservation for unionUniqueRoots",
    "prove root-list cardinality bound for product unions",
    "replace mul_eq_zero_or_left_or_right bridge axiom with a derived integral-domain theorem",
    "connect normalized product degree arithmetic to full RootCountInductionTarget",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_CONVOLUTION_ROOT_UNION_PACKET_V5_READY",
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
            "product_readiness/machlib_product_root_bridge_packet_v4_2026_05_25.json",
            "product_readiness/machlib_normalized_polynomial_root_count_packet_v3_2026_05_25.json",
        ],
        "degree_arithmetic_status": "BASE_CASE_CHECKED_GENERAL_TARGET_DEFINED_NOT_PROVED",
        "root_list_union_status": "SOUNDNESS_CHECKED_DISTINCTNESS_CARDINALITY_NOT_PROVED",
        "general_root_count_theorem_status": "BLOCKED_MISSING_DEGREE_ARITHMETIC_AND_DISTINCT_UNION_CARDINALITY",
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
        "# MachLib Convolution + Root-Union Packet v5",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet turns the previous product-root bridge into a concrete",
        "coefficient-list product path. It adds recursive convolution, proves",
        "that convolution evaluates as product evaluation, and adds root-list",
        "union machinery for product-root packets.",
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
            "- Degree arithmetic is named and has a checked base case, but the general theorem is not proved.",
            "- Root-list union soundness is checked; distinctness/cardinality preservation remains open.",
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
        if data["primitive_count"] < 7:
            raise SystemExit("expected at least seven primitives")
        if data["checked_result_count"] < 12:
            raise SystemExit("expected at least twelve checked results")
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
