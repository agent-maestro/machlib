#!/usr/bin/env python3
"""Build MachLib right-linear product degree packet v12 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_right_linear_degree_packet_v12_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_RESULTS = [
    "shiftCoeff_lastNonzero",
    "degreeBound_shiftCoeff_of_LastNonzero",
    "degreeBound_shiftCoeff_of_positive",
    "addCoeff_two_left_shift_lastNonzero",
    "degreeBound_addCoeff_two_left_shift",
    "degreeBound_mulCoeff_right_linear",
    "rightLinearMulCoeffRawLastNonzero",
    "rightLinearMulCoeffLastNonzero",
    "rightLinearMulCoeffDegreeGrowth",
    "rightLinearMulCoeffDegreeGrowthTarget_checked",
]


STILL_OPEN = [
    "general shorter-left addend versus shifted-tail leading preservation",
    "arbitrary normalized product leading-coefficient preservation",
    "arbitrary normalized product degree growth",
    "full RootCountInductionTarget assembly",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_RIGHT_LINEAR_DEGREE_PACKET_V12_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_result_count": len(CHECKED_RESULTS),
        "checked_results": CHECKED_RESULTS,
        "right_linear_last_nonzero_status": "CHECKED",
        "right_linear_degree_growth_status": "CHECKED",
        "left_linear_degree_growth_status": "CHECKED_IN_V11",
        "arbitrary_normalized_product_degree_growth_status": "NOT_YET_PROVED",
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "still_open": STILL_OPEN,
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "arbitrary_normalized_product_degree_growth_proved": False,
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
        "# MachLib Right-Linear Degree Packet v12",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Checked",
        "",
        "v12 proves the right-linear mirror of the v11 left-linear bridge:",
        "arbitrary normalized coefficient lists multiplied on the right by",
        "`linearCoeff r` preserve leading-coefficient evidence and satisfy exact",
        "normalized degree growth.",
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
            "- This proves the right-linear arbitrary normalized product bridge, not the full arbitrary product theorem.",
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
