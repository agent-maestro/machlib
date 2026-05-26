#!/usr/bin/env python3
"""Build MachLib product-root bridge packet v4 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_product_root_bridge_packet_v4_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


PRIMITIVES = [
    {
        "name": "linearCoeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.linearCoeff",
        "status": "DEFINED",
        "purpose": "coefficient-list representation of x - r",
    },
    {
        "name": "MulEvalSound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.MulEvalSound",
        "status": "DEFINED",
        "purpose": "semantic certificate that a coefficient list evaluates as product p*q",
    },
    {
        "name": "mul_eq_zero_or_left_or_right",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.mul_eq_zero_or_left_or_right",
        "status": "DERIVED_THEOREM",
        "purpose": "derived real zero-product theorem used by product-root splitting",
    },
]


CHECKED_RESULTS = [
    {
        "id": "degree_bound_linear_coeff",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.degreeBound_linearCoeff",
        "statement": "linearCoeff r has degree bound one",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_coeff_last_nonzero",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.linearCoeff_lastNonzero",
        "statement": "linearCoeff r is normalized because its last coefficient is one",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "eval_linear_coeff_eq_linear_factor",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_linearCoeff_eq_linearFactor",
        "statement": "coefficient-list linear factor evaluates like the AST linear factor",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_coeff_root_iff_linear_factor_root",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.linearCoeff_root_iff_linearFactor_root",
        "statement": "normalized and AST linear-factor roots are equivalent",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "product_root_split",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRoot_split",
        "statement": "a root of a semantically certified product is a root of one factor",
        "evidence_class": "MACHLIB_CHECKED_WITH_DERIVED_ZERO_PRODUCT_THEOREM",
    },
    {
        "id": "product_root_right_of_left_nonroot",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRoot_right_of_left_nonroot",
        "statement": "if the left factor is nonzero at x, product root implies right root",
        "evidence_class": "MACHLIB_CHECKED_WITH_DERIVED_ZERO_PRODUCT_THEOREM",
    },
    {
        "id": "product_root_left_of_right_nonroot",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.productRoot_left_of_right_nonroot",
        "statement": "if the right factor is nonzero at x, product root implies left root",
        "evidence_class": "MACHLIB_CHECKED_WITH_DERIVED_ZERO_PRODUCT_THEOREM",
    },
]


UNLOCKED = [
    "linear coefficient-list representation now matches the existing AST linear-factor packet",
    "semantic product certificate gives a safe place to attach future convolution normalizers",
    "product-root splitting is available under an explicit real integral-domain derived theorem",
    "root-count induction can now target factor/product splitting instead of only base cases",
]


BLOCKED_NEXT = [
    "keep the derived zero-product theorem as a regression while product induction expands",
    "implement coefficient-list convolution plus MulEvalSound proofs for concrete products",
    "root-list union/deduplication across product factors",
    "degree arithmetic for convolution products",
    "linear-factor packet for normalized coefficient lists with singleton root list",
    "full induction proof for RootCountInductionTarget",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_PRODUCT_ROOT_BRIDGE_PACKET_V4_READY",
        "date": DATE,
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "primitive_count": len(PRIMITIVES),
        "checked_result_count": len(CHECKED_RESULTS),
        "bridge_axiom_count": 0,
        "primitives": PRIMITIVES,
        "checked_results": CHECKED_RESULTS,
        "unlocked": UNLOCKED,
        "blocked_next": BLOCKED_NEXT,
        "derived_zero_product_theorems": [
            {
                "lean_name": "MachLib.NormalizedPolynomialRootCount.mul_eq_zero_or_left_or_right",
                "reason": "Derived from MachLib's existing field axioms: inverse, multiplication associativity/commutativity, and zero multiplication.",
            }
        ],
        "general_root_count_theorem_status": "BLOCKED_MISSING_CONVOLUTION_ROOT_LIST_INDUCTION",
        "induction_target_status": "DEFINED_NOT_PROVED",
        "depends_on": [
            "MachLib.NormalizedPolynomialRootCount",
            "product_readiness/machlib_normalized_polynomial_root_count_packet_v3_2026_05_25.json",
        ],
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
        "# MachLib Product-Root Bridge Packet v4",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet bridges the normalized coefficient-list root-count route",
        "to two missing pieces: a linear coefficient-list representation and",
        "product-root splitting. Product splitting now depends on a derived",
        "theorem for the real zero-product property.",
        "",
        "## Derived Theorem",
        "",
        "The derived theorem is `mul_eq_zero_or_left_or_right`: if `a * b = 0`,",
        "then `a = 0` or `b = 0`. It is derived in MachLib from the existing",
        "field axioms rather than added as a new axiom.",
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
            "- This is product-root bridge evidence, not the general degree/root-count theorem.",
            "- `RootCountInductionTarget` remains defined but not proved.",
            "- It does not prove analytic identity behavior.",
            "- It is not public-ready and not marketplace-ready.",
            "- No package publish, PETAL/API upload, or Hugging Face upload.",
            "- No safety-certification or controller-status claim.",
            "- No public theorem/proof/open-problem claim.",
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
        if data["primitive_count"] < 3:
            raise SystemExit("expected at least three bridge primitives")
        if data["checked_result_count"] < 7:
            raise SystemExit("expected at least seven checked bridge results")
        if data["bridge_axiom_count"] != 0:
            raise SystemExit("expected no bridge axioms")
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
