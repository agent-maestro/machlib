#!/usr/bin/env python3
"""Build MachLib normalized polynomial root-count packet v3 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_normalized_polynomial_root_count_packet_v3_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


PRIMITIVES = [
    {
        "name": "CoeffPoly",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.CoeffPoly",
        "status": "DEFINED",
        "purpose": "low-to-high coefficient-list normal form target",
    },
    {
        "name": "eval",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval",
        "status": "DEFINED",
        "purpose": "Horner-style coefficient-list evaluator",
    },
    {
        "name": "LastNonzero",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.LastNonzero",
        "status": "DEFINED",
        "purpose": "minimal normalized-list predicate for nonzero polynomial degree",
    },
    {
        "name": "degreeBound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.degreeBound",
        "status": "DEFINED",
        "purpose": "syntactic degree upper bound for coefficient lists",
    },
    {
        "name": "NormalizedFiniteRootPacket",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.NormalizedFiniteRootPacket",
        "status": "DEFINED",
        "purpose": "finite root-list packet for normalized coefficient polynomials",
    },
    {
        "name": "RootCountInductionTarget",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.RootCountInductionTarget",
        "status": "DEFINED_NOT_PROVED",
        "purpose": "exact target property for future degree/root-count induction",
    },
]


CHECKED_RESULTS = [
    {
        "id": "eval_nil",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_nil",
        "statement": "the empty coefficient list evaluates to zero",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "eval_singleton",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.eval_singleton",
        "statement": "the singleton coefficient list [c] evaluates to c",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "degree_bound_singleton",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.degreeBound_singleton",
        "statement": "the singleton coefficient list has degree bound zero",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "singleton_last_nonzero",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.singleton_lastNonzero",
        "statement": "a nonzero singleton coefficient list is normalized",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "nonzero_constant_no_root",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.nonzeroConstant_no_root",
        "statement": "a nonzero constant coefficient polynomial has no roots",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "nonzero_constant_empty_root_list_sound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.nonzeroConstant_emptyRootListSound",
        "statement": "the empty root list is sound for a nonzero constant polynomial",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "nonzero_constant_empty_root_list_degree_bound",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.nonzeroConstant_emptyRootListDegreeBound",
        "statement": "the empty root list is bounded by degree zero",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "nonzero_constant_finite_root_packet",
        "lean_name": "MachLib.NormalizedPolynomialRootCount.nonzeroConstantFiniteRootPacket",
        "statement": "checked normalized finite-root packet for a nonzero constant",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


UNLOCKED = [
    "normal-form coefficient-list substrate independent of expression AST shape",
    "checked nonzero-constant root-count base case",
    "finite root-packet structure ready for induction targets",
    "explicit target property for future degree/root-count induction",
]


BLOCKED_NEXT = [
    "linear coefficient-list packet equivalent to the AST linear-factor packet",
    "coefficient-list multiplication and degree-bound arithmetic",
    "root-list union/deduplication for product polynomials",
    "integral-domain bridge: product zero implies a factor zero",
    "normalized degree exactness for LastNonzero coefficient lists",
    "induction proof for the full RootCountInductionTarget",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_NORMALIZED_POLYNOMIAL_ROOT_COUNT_PACKET_V3_READY",
        "date": DATE,
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "primitive_count": len(PRIMITIVES),
        "checked_result_count": len(CHECKED_RESULTS),
        "primitives": PRIMITIVES,
        "checked_results": CHECKED_RESULTS,
        "unlocked": UNLOCKED,
        "blocked_next": BLOCKED_NEXT,
        "base_case_result": "NONZERO_CONSTANT_HAS_EMPTY_ROOT_PACKET",
        "induction_target_status": "DEFINED_NOT_PROVED",
        "general_root_count_theorem_status": "BLOCKED_MISSING_LINEAR_NORMAL_FORM_AND_PRODUCT_INDUCTION",
        "depends_on": [
            "MachLib.PolynomialRootCount",
            "product_readiness/machlib_polynomial_root_count_packet_v2_2026_05_25.json",
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
        "# MachLib Normalized Polynomial Root-Count Packet v3",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet starts the normalized coefficient-list route toward a",
        "future degree/root-count induction. It is separate from the expression",
        "AST used by earlier finite-zero packets, because induction needs a",
        "normal-form object with a stable degree measure.",
        "",
        "## Checked Base Case",
        "",
        "The checked base case is intentionally small: a nonzero constant",
        "coefficient-list polynomial has no roots, so its complete finite root",
        "packet has the empty root list and degree bound zero.",
        "",
        "## Primitives",
        "",
    ]
    for item in data["primitives"]:
        lines.append(f"- `{item['name']}`: {item['purpose']}")
    lines.extend(["", "## Checked Results", ""])
    for item in data["checked_results"]:
        lines.append(f"- `{item['id']}` — {item['statement']}")
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
            "- This defines and checks the normalized base-case packet, not the",
            "  general degree/root-count theorem.",
            "- `RootCountInductionTarget` is defined but not proved.",
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
        if data["primitive_count"] < 6:
            raise SystemExit("expected at least six normalized primitives")
        if data["checked_result_count"] < 8:
            raise SystemExit("expected at least eight checked results")
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
