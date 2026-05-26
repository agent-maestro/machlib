#!/usr/bin/env python3
"""Build MachLib linear-product degree packet v11 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_linear_product_degree_packet_v11_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_RESULTS = [
    "addCoeff_nil_right",
    "addCoeff_zero_singleton_right_of_LastNonzero",
    "mulCoeff_one_left_of_LastNonzero",
    "addCoeff_scalar_cons_self_lastNonzero",
    "degreeBound_addCoeff_scalar_cons_self",
    "mulCoeff_linearCoeff_shape",
    "linearMulCoeffLastNonzero",
    "linearMulCoeffLastNonzeroTarget_checked",
    "linearMulCoeffDegreeGrowth",
    "linearMulCoeffDegreeGrowthTarget_checked",
]


STILL_OPEN = [
    "right-linear product degree growth: normalizedProductCoeff p (linearCoeff r)",
    "arbitrary normalized product degree growth: normalizedProductCoeff p q",
    "general leading-coefficient preservation for normalized convolution products",
    "full RootCountInductionTarget assembly",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_LINEAR_PRODUCT_DEGREE_PACKET_V11_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_result_count": len(CHECKED_RESULTS),
        "checked_results": CHECKED_RESULTS,
        "linear_times_arbitrary_last_nonzero_status": "CHECKED",
        "linear_times_arbitrary_degree_growth_status": "CHECKED",
        "normalized_product_eval_soundness_status": "CHECKED_IN_V10",
        "arbitrary_normalized_product_degree_growth_status": "NOT_YET_PROVED",
        "still_open": STILL_OPEN,
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "arbitrary_normalized_product_degree_growth_proved": False,
        "right_linear_product_degree_growth_proved": False,
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
        "# MachLib Linear Product Degree Packet v11",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Checked",
        "",
        "v11 proves the first true arbitrary-family product-degree bridge:",
        "multiplication on the left by `linearCoeff r` preserves normalized",
        "leading-coefficient evidence and gives exact degree growth for any",
        "normalized nonempty coefficient list `p`.",
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
            "- This proves the left-linear arbitrary normalized product bridge, not the full arbitrary product theorem.",
            "- The general root-count theorem is still not proved.",
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
        if data["checked_result_count"] < 10:
            raise SystemExit("expected at least ten checked results")
        for key in [
            "general_root_count_theorem_proved",
            "arbitrary_normalized_product_degree_growth_proved",
            "right_linear_product_degree_growth_proved",
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
