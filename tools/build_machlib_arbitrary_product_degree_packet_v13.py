#!/usr/bin/env python3
"""Build MachLib arbitrary product degree packet v13 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_arbitrary_product_degree_packet_v13_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_RESULTS = [
    "MulCoeffLastNonzeroTarget",
    "degreeBound_scalarMulCoeff",
    "addCoeff_left_lower_degree_lastNonzero",
    "degreeBound_addCoeff_left_lower_degree",
    "mulCoeff_lastNonzero_and_raw_growth",
    "mulCoeff_lastNonzero",
    "degreeBound_mulCoeff_raw_growth",
    "normalizedProductCoeff_lastNonzero",
    "mulCoeffLastNonzeroTarget_checked",
    "normalizedProductCoeffDegreeGrowth",
    "normalizedMulCoeffDegreeGrowthTarget_checked",
    "normalizedProductFiniteRootPacket",
    "ProductPacketAssemblyTarget",
    "productPacketAssemblyTarget_checked",
]


STILL_OPEN = [
    "full arbitrary root enumeration for every normalized coefficient list",
    "RootCountInductionTarget construction for arbitrary coefficients",
    "algorithmic root-list extraction rather than composition from known packets",
    "higher-level Forge/eFrog emission of product/root certificates",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_ARBITRARY_PRODUCT_DEGREE_PACKET_V13_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_result_count": len(CHECKED_RESULTS),
        "checked_results": CHECKED_RESULTS,
        "arbitrary_raw_product_last_nonzero_status": "CHECKED",
        "arbitrary_raw_product_degree_growth_status": "CHECKED",
        "arbitrary_normalized_product_last_nonzero_status": "CHECKED",
        "arbitrary_normalized_product_degree_growth_status": "CHECKED",
        "product_packet_assembly_status": "CHECKED_FOR_KNOWN_FINITE_ROOT_PACKETS",
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "root_count_induction_target_assembled": False,
        "still_open": STILL_OPEN,
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "root_count_induction_target_proved": False,
        "analytic_identity_theorem_proved": False,
        "forge_compiler_behavior_changed": False,
        "efrog_behavior_changed": False,
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
        "# MachLib Arbitrary Product Degree Packet v13",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Checked",
        "",
        "v13 proves the arbitrary normalized product-degree bridge for",
        "`mulCoeff` and `normalizedProductCoeff`: normalized nonzero inputs",
        "produce a normalized nonzero product with enough degree budget for",
        "root-list union. It also adds a generic product packet constructor for",
        "known finite-root packets.",
        "",
    ]
    for name in data["checked_results"]:
        lines.append(f"- `{name}`")
    lines.extend(["", "## Still Open", ""])
    for item in data["still_open"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This is the arbitrary product degree-growth bridge, not a full root enumeration theorem.",
            "- `RootCountInductionTarget` remains defined but not proved.",
            "- Product packets can now compose known finite-root packets without a manual product-degree certificate.",
            "- No Forge compiler or eFrog behavior was changed.",
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
        if data["checked_result_count"] < 14:
            raise SystemExit("expected at least fourteen checked results")
        for key in [
            "root_count_induction_target_assembled",
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
