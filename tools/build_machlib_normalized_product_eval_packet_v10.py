#!/usr/bin/env python3
"""Build MachLib normalized-product evaluation packet v10 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_normalized_product_eval_packet_v10_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_RESULTS = [
    "eval_eq_zero_of_normalizeCoeff_eq_nil",
    "normalizeCoeff_evalSound",
    "normalizeCoeffEvalSoundTarget_checked",
    "scalarMulCoeff_lastNonzero",
    "normalizedProductCoeff_evalSound",
    "normalizedProductFiniteRootPacketWithDegreeGrowthCert",
]


TARGETS = [
    "LinearMulCoeffLastNonzeroTarget",
    "LinearMulCoeffDegreeGrowthTarget",
    "NormalizedMulCoeffDegreeGrowthTarget",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_NORMALIZED_PRODUCT_EVAL_PACKET_V10_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_result_count": len(CHECKED_RESULTS),
        "checked_results": CHECKED_RESULTS,
        "target_count": len(TARGETS),
        "targets_named_not_proved": TARGETS,
        "normalizer_eval_soundness_status": "CHECKED",
        "normalized_product_eval_soundness_status": "CHECKED",
        "scalar_last_nonzero_preservation_status": "CHECKED_FOR_NONZERO_SCALAR",
        "normalized_product_packet_constructor_status": "CHECKED_WITH_LEADING_AND_DEGREE_GROWTH_CERTIFICATES",
        "forge_efrog_compatibility_report": "reports/machlib_forge_efrog_polynomial_packet_compatibility_2026_05_25.md",
        "next_exact_bridge": [
            "prove LinearMulCoeffLastNonzeroTarget",
            "prove LinearMulCoeffDegreeGrowthTarget",
            "then generalize to NormalizedMulCoeffDegreeGrowthTarget",
        ],
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "linear_times_arbitrary_degree_growth_proved": False,
        "arbitrary_normalized_product_degree_growth_proved": False,
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
        "# MachLib Normalized Product Evaluation Packet v10",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Checked",
        "",
    ]
    for name in data["checked_results"]:
        lines.append(f"- `{name}`")
    lines.extend(["", "## Named But Not Proved", ""])
    for name in data["targets_named_not_proved"]:
        lines.append(f"- `{name}`")
    lines.extend(
        [
            "",
            "## Forge / eFrog Compatibility",
            "",
            f"See `{data['forge_efrog_compatibility_report']}`. No Forge compiler or eFrog behavior was changed.",
            "",
            "## Boundary",
            "",
            "- Normalizer evaluation soundness is checked.",
            "- Normalized product evaluation soundness is checked.",
            "- Arbitrary normalized product degree growth is not proved.",
            "- Linear-times-arbitrary normalized product degree growth is not proved.",
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
        if data["checked_result_count"] < 6:
            raise SystemExit("expected at least six checked results")
        for key in [
            "general_root_count_theorem_proved",
            "linear_times_arbitrary_degree_growth_proved",
            "arbitrary_normalized_product_degree_growth_proved",
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
