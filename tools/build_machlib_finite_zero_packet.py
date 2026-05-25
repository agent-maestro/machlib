#!/usr/bin/env python3
"""Build MachLib finite zero packet v1."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_finite_zero_packet_v1_2026_05_25"
LEAN_PATH = "foundations/MachLib/FiniteZeroPacket.lean"


SAMPLES = [
    {
        "sample_id": "zero_poly_everywhere",
        "polynomial": "0",
        "root_witness": "x",
        "lean_name": "MachLib.FiniteZeroPacket.sample_zero_poly_root",
        "statement": "eval zero x = 0",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "sample_id": "linear_factor_at_named_root",
        "polynomial": "x - r",
        "root_witness": "r",
        "lean_name": "MachLib.FiniteZeroPacket.sample_linear_factor_root",
        "statement": "eval (x - r) r = 0",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "sample_id": "factor_product_left_root",
        "polynomial": "(x - r) * q(x)",
        "root_witness": "r",
        "lean_name": "MachLib.FiniteZeroPacket.sample_factor_product_left_root",
        "statement": "eval ((x - r) * q) r = 0",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "sample_id": "repeated_factor_at_named_root",
        "polynomial": "(x - r) * (x - r)",
        "root_witness": "r",
        "lean_name": "MachLib.FiniteZeroPacket.sample_repeated_factor_root",
        "statement": "eval ((x - r) * (x - r)) r = 0",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "sample_id": "two_factor_right_root",
        "polynomial": "(x - r) * (x - s)",
        "root_witness": "s",
        "lean_name": "MachLib.FiniteZeroPacket.sample_two_factor_right_root",
        "statement": "eval ((x - r) * (x - s)) s = 0",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_FINITE_ZERO_PACKET_V1_READY",
        "date": DATE,
        "lean_module": "MachLib.FiniteZeroPacket",
        "lean_path": LEAN_PATH,
        "sample_count": len(SAMPLES),
        "samples": SAMPLES,
        "depends_on": [
            "MachLib.PolynomialEvidence",
            "product_readiness/machlib_polynomial_evidence_v1_2026_05_25.json",
        ],
        "next_research_gate": "POLYNOMIAL_DEGREE_ROOT_COUNT_FEASIBILITY",
        "analytic_identity_theorem_status": "BLOCKED_NEEDS_ANALYTIC_SUBSTRATE",
        "public_ready": False,
        "marketplace_ready": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "package_publish_performed": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "public_theorem_claim": False,
    }


def report(data: dict) -> str:
    lines = [
        "# MachLib Finite Zero Packet v1",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Purpose",
        "",
        "This packet gives five finite polynomial/root evidence samples over the",
        "tiny `MachLib.PolynomialEvidence` AST.",
        "",
        "It is not an analytic identity theorem and does not claim infinite-zero",
        "or analytic-continuation behavior.",
        "",
        "## Samples",
        "",
    ]
    for sample in data["samples"]:
        lines.extend(
            [
                f"- `{sample['sample_id']}`",
                f"  - polynomial: `{sample['polynomial']}`",
                f"  - root witness: `{sample['root_witness']}`",
                f"  - Lean: `{sample['lean_name']}`",
                f"  - statement: `{sample['statement']}`",
            ]
        )
    lines.extend(
        [
            "",
            "## Next Research Gate",
            "",
            "`POLYNOMIAL_DEGREE_ROOT_COUNT_FEASIBILITY`: define what degree,",
            "multiplicity, finite roots, and root-count bounds would require in",
            "MachLib before moving toward analytic zero-set claims.",
            "",
            "## Boundary",
            "",
            "- Internal evidence only.",
            "- Not public-ready.",
            "- Not marketplace-ready.",
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
    if args.strict and data["sample_count"] < 5:
        raise SystemExit("expected at least 5 finite-zero samples")
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
    print("MACHLIB_FINITE_ZERO_PACKET_V1_READY")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
