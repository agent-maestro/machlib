#!/usr/bin/env python3
"""Build MachLib polynomial root-count packet v2 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_polynomial_root_count_packet_v2_2026_05_25"
LEAN_PATH = "foundations/MachLib/PolynomialRootCount.lean"


PRIMITIVES = [
    {
        "name": "Root",
        "lean_name": "MachLib.PolynomialRootCount.Root",
        "status": "DEFINED",
        "purpose": "classify an input as a zero of a polynomial evaluator",
    },
    {
        "name": "NonzeroWitness",
        "lean_name": "MachLib.PolynomialRootCount.NonzeroWitness",
        "status": "DEFINED",
        "purpose": "represent nonzero-polynomial evidence by one nonzero evaluation witness",
    },
    {
        "name": "DistinctRootPair",
        "lean_name": "MachLib.PolynomialRootCount.DistinctRootPair",
        "status": "DEFINED",
        "purpose": "state the first finite root-count obstruction shape",
    },
    {
        "name": "degreeUpper",
        "lean_name": "MachLib.PolynomialRootCount.degreeUpper",
        "status": "DEFINED",
        "purpose": "compute a syntactic degree upper bound over the tiny polynomial AST",
    },
    {
        "name": "RootListSound",
        "lean_name": "MachLib.PolynomialRootCount.RootListSound",
        "status": "DEFINED",
        "purpose": "require every actual root to appear in a finite root list",
    },
    {
        "name": "RootListDistinct",
        "lean_name": "MachLib.PolynomialRootCount.RootListDistinct",
        "status": "DEFINED",
        "purpose": "track duplicate-free root lists without importing a finite-set library",
    },
    {
        "name": "RootListDegreeBound",
        "lean_name": "MachLib.PolynomialRootCount.RootListDegreeBound",
        "status": "DEFINED",
        "purpose": "state that a finite root list length is bounded by syntactic degree",
    },
    {
        "name": "FiniteRootPacket",
        "lean_name": "MachLib.PolynomialRootCount.FiniteRootPacket",
        "status": "DEFINED",
        "purpose": "bundle polynomial, roots, soundness, distinctness, and degree bound",
    },
]


CHECKED_RESULTS = [
    {
        "id": "degree_upper_linear_factor",
        "lean_name": "MachLib.PolynomialRootCount.degreeUpper_linearFactor",
        "statement": "degreeUpper (x - r) = 1",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "degree_upper_factor_mul",
        "lean_name": "MachLib.PolynomialRootCount.degreeUpper_factorMul",
        "statement": "degreeUpper ((x - r) * q) = 1 + degreeUpper q",
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
    {
        "id": "linear_factor_root_list_sound",
        "lean_name": "MachLib.PolynomialRootCount.linearFactor_rootListSound",
        "statement": "the singleton list [r] contains every root of x - r",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "singleton_root_list_distinct",
        "lean_name": "MachLib.PolynomialRootCount.singleton_rootListDistinct",
        "statement": "the singleton root list [r] has no duplicate roots",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_factor_root_list_degree_bound",
        "lean_name": "MachLib.PolynomialRootCount.linearFactor_rootListDegreeBound",
        "statement": "the singleton root list [r] has length bounded by degreeUpper (x - r)",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_factor_finite_root_packet",
        "lean_name": "MachLib.PolynomialRootCount.linearFactorFiniteRootPacket",
        "statement": "a checked finite-root packet exists for x - r",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


BLOCKED_NEXT = [
    "normalized coefficient-list representation for arbitrary polynomial syntax",
    "proof that normalized degree agrees with evaluator semantics",
    "finite root-set representation beyond list membership",
    "root-list union/deduplication across products",
    "multiplicity accounting",
    "induction showing a degree-n nonzero polynomial has at most n distinct roots",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_POLYNOMIAL_ROOT_COUNT_PACKET_V2_READY",
        "date": DATE,
        "lean_module": "MachLib.PolynomialRootCount",
        "lean_path": LEAN_PATH,
        "primitive_count": len(PRIMITIVES),
        "checked_result_count": len(CHECKED_RESULTS),
        "primitives": PRIMITIVES,
        "checked_results": CHECKED_RESULTS,
        "tiny_root_count_result": "LINEAR_FACTOR_FINITE_ROOT_PACKET_CHECKED",
        "general_root_count_theorem_status": "BLOCKED_MISSING_NORMALIZED_DEGREE_INDUCTION",
        "blocked_next": BLOCKED_NEXT,
        "depends_on": [
            "MachLib.PolynomialEvidence",
            "MachLib.FiniteZeroPacket",
            "product_readiness/machlib_polynomial_root_count_scaffold_v1_2026_05_25.json",
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
        "# MachLib Polynomial Root-Count Packet v2",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Adds",
        "",
        "This packet upgrades the v1 scaffold from a distinct-root-pair",
        "obstruction into a finite root-list packet for the first degree-one",
        "case. The checked Lean result is still deliberately small:",
        "`(x - r)` has a singleton root list `[r]`, that list is distinct,",
        "and its length is bounded by the syntactic degree upper bound.",
        "",
        "## New Primitive Layer",
        "",
    ]
    for item in data["primitives"]:
        lines.append(f"- `{item['name']}`: {item['purpose']}")
    lines.extend(["", "## Checked Results", ""])
    for item in data["checked_results"]:
        lines.append(f"- `{item['id']}` — {item['statement']}")
    lines.extend(["", "## Still Blocked", ""])
    for item in data["blocked_next"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This is a checked finite-root packet for a linear factor, not a",
            "  general degree/root-count theorem.",
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
        if data["primitive_count"] < 8:
            raise SystemExit("expected at least eight root-count primitives")
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
