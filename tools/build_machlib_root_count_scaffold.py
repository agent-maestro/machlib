#!/usr/bin/env python3
"""Build MachLib polynomial root-count scaffold v1 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_polynomial_root_count_scaffold_v1_2026_05_25"
LEAN_PATH = "foundations/MachLib/PolynomialRootCount.lean"


PRIMITIVES = [
    {
        "name": "Root",
        "lean_name": "MachLib.PolynomialRootCount.Root",
        "purpose": "classify an input as a zero of a polynomial evaluator",
        "status": "DEFINED",
    },
    {
        "name": "NonzeroWitness",
        "lean_name": "MachLib.PolynomialRootCount.NonzeroWitness",
        "purpose": "represent nonzero-polynomial evidence by one nonzero evaluation witness",
        "status": "DEFINED",
    },
    {
        "name": "DistinctRootPair",
        "lean_name": "MachLib.PolynomialRootCount.DistinctRootPair",
        "purpose": "state the first finite root-count obstruction shape",
        "status": "DEFINED",
    },
    {
        "name": "degreeUpper",
        "lean_name": "MachLib.PolynomialRootCount.degreeUpper",
        "purpose": "compute a syntactic degree upper bound over the tiny polynomial AST",
        "status": "DEFINED",
    },
]


CHECKED_FOOTHOLDS = [
    {
        "id": "degree_upper_linear_factor",
        "lean_name": "MachLib.PolynomialRootCount.degreeUpper_linearFactor",
        "statement": "degreeUpper (x - r) = 1",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_factor_root_unique",
        "lean_name": "MachLib.PolynomialRootCount.linearFactor_root_unique",
        "statement": "if eval (x - r) at x is zero, then x = r",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_factor_no_distinct_root_pair",
        "lean_name": "MachLib.PolynomialRootCount.linearFactor_no_distinct_root_pair",
        "statement": "a linear factor cannot have two distinct roots",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


BLOCKED_NEXT = [
    "general degree arithmetic for normalized polynomials",
    "finite root-set representation beyond distinct pairs",
    "root-list uniqueness and cardinality bounds",
    "nonzero polynomial predicate tied to degree",
    "multiplicity accounting",
    "induction showing a degree-n nonzero polynomial has at most n distinct roots",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_POLYNOMIAL_ROOT_COUNT_SCAFFOLD_V1_READY",
        "date": DATE,
        "lean_module": "MachLib.PolynomialRootCount",
        "lean_path": LEAN_PATH,
        "primitive_count": len(PRIMITIVES),
        "checked_foothold_count": len(CHECKED_FOOTHOLDS),
        "primitives": PRIMITIVES,
        "checked_footholds": CHECKED_FOOTHOLDS,
        "tiny_root_count_result": "LINEAR_FACTOR_HAS_NO_DISTINCT_ROOT_PAIR",
        "general_root_count_theorem_status": "BLOCKED_MISSING_POLYNOMIAL_NORMAL_FORM_AND_FINITE_ROOT_SET",
        "blocked_next": BLOCKED_NEXT,
        "depends_on": [
            "MachLib.PolynomialEvidence",
            "MachLib.FiniteZeroPacket",
            "product_readiness/machlib_finite_zero_packet_v1_2026_05_25.json",
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
        "# MachLib Polynomial Root-Count Scaffold v1",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet defines the first root-count primitives over the tiny",
        "`MachLib.PolynomialEvidence` AST and proves one degree-1 foothold:",
        "a linear factor cannot have a pair of distinct roots.",
        "",
        "## Primitives",
        "",
    ]
    for item in data["primitives"]:
        lines.extend(
            [
                f"- `{item['name']}`",
                f"  - Lean: `{item['lean_name']}`",
                f"  - purpose: {item['purpose']}",
            ]
        )
    lines.extend(["", "## Checked Footholds", ""])
    for item in data["checked_footholds"]:
        lines.extend(
            [
                f"- `{item['id']}`",
                f"  - Lean: `{item['lean_name']}`",
                f"  - statement: {item['statement']}",
            ]
        )
    lines.extend(
        [
            "",
            "## Still Blocked",
            "",
        ]
    )
    for item in data["blocked_next"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This is a tiny checked root-count foothold, not the general theorem.",
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
        if data["primitive_count"] < 4:
            raise SystemExit("expected at least four root-count primitives")
        if data["checked_foothold_count"] < 3:
            raise SystemExit("expected at least three checked footholds")
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
