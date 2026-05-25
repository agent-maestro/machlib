#!/usr/bin/env python3
"""Build MachLib polynomial evidence v1 packets."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_polynomial_evidence_v1_2026_05_25"
LEAN_PATH = "foundations/MachLib/PolynomialEvidence.lean"


FACTS = [
    {
        "id": "poly_eval_zero",
        "lean_name": "MachLib.PolynomialEvidence.Poly.eval_zero",
        "statement": "eval zero x = 0",
        "meaning": "The explicit zero polynomial evaluates to zero at every input.",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "poly_eval_var",
        "lean_name": "MachLib.PolynomialEvidence.Poly.eval_var",
        "statement": "eval var x = x",
        "meaning": "The variable polynomial evaluates to the supplied input.",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "linear_factor_root",
        "lean_name": "MachLib.PolynomialEvidence.Poly.eval_linearFactor_at_root",
        "statement": "eval (x - r) at r = 0",
        "meaning": "A linear factor vanishes at its named root.",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "factor_mul_root",
        "lean_name": "MachLib.PolynomialEvidence.Poly.eval_factorMul_at_root",
        "statement": "eval ((x - r) * q) at r = 0",
        "meaning": "Any polynomial multiplied by a vanishing factor vanishes at that root.",
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "repeated_factor_root",
        "lean_name": "MachLib.PolynomialEvidence.Poly.eval_repeatedFactor_at_root",
        "statement": "eval ((x - r) * (x - r)) at r = 0",
        "meaning": "A repeated linear factor also vanishes at its named root.",
        "evidence_class": "MACHLIB_CHECKED",
    },
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "status": "MACHLIB_POLYNOMIAL_EVIDENCE_V1_READY",
        "date": DATE,
        "lean_module": "MachLib.PolynomialEvidence",
        "lean_path": LEAN_PATH,
        "fact_count": len(FACTS),
        "facts": FACTS,
        "analytic_identity_theorem_status": "BLOCKED_NEEDS_ANALYTIC_SUBSTRATE",
        "explorer_panel": {
            "label": "MachLib finite root evidence",
            "visibility": "internal_prototype",
            "summary": "Finite polynomial/root facts are checked; analytic identity theorem remains blocked.",
        },
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
        "# MachLib Polynomial Evidence v1",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Purpose",
        "",
        "This packet turns the finite-root foothold from the analytic identity",
        "feasibility pass into a reusable MachLib substrate: a tiny polynomial AST,",
        "an evaluator, and checked root facts.",
        "",
        "It does not claim analytic continuation, infinite zero-set behavior, or a",
        "proved analytic identity theorem.",
        "",
        "## Checked Facts",
        "",
    ]
    for fact in data["facts"]:
        lines.extend(
            [
                f"- `{fact['id']}`",
                f"  - Lean: `{fact['lean_name']}`",
                f"  - statement: `{fact['statement']}`",
                f"  - meaning: {fact['meaning']}",
            ]
        )
    lines.extend(
        [
            "",
            "## Explorer Use",
            "",
            "The Explorer may show this as an internal/prototype evidence card:",
            "finite polynomial/root evidence is checked, while the analytic identity",
            "theorem remains blocked until the analytic substrate exists.",
            "",
            "## Boundary",
            "",
            "- Internal/prototype evidence only.",
            "- Not public-ready.",
            "- Not marketplace-ready.",
            "- No package publish, PETAL/API upload, or Hugging Face upload.",
            "- No safety-certification or controller-status claim.",
            "- No public theorem/proof/open-problem claim.",
        ]
    )
    return "\n".join(lines) + "\n"


def explorer_card(data: dict) -> dict:
    return {
        "card_id": "machlib_polynomial_evidence_internal_card_2026_05_25",
        "status": "INTERNAL_PROTOTYPE",
        "title": "MachLib finite root evidence",
        "summary": data["explorer_panel"]["summary"],
        "fact_count": data["fact_count"],
        "facts": data["facts"],
        "analytic_identity_theorem_status": data["analytic_identity_theorem_status"],
        "boundaries": {
            "public_ready": False,
            "marketplace_ready": False,
            "public_theorem_claim": False,
            "package_publish_performed": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-json", default=f"product_readiness/{PACKET_ID}.json")
    parser.add_argument("--out-report", default=f"reports/{PACKET_ID}.md")
    parser.add_argument("--out-explorer-card", default="product_readiness/machlib_polynomial_evidence_explorer_card_2026_05_25.json")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    data = payload()
    if args.strict and data["fact_count"] < 5:
        raise SystemExit("expected at least 5 polynomial evidence facts")
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
    out_card = Path(args.out_explorer_card)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_report.parent.mkdir(parents=True, exist_ok=True)
    out_card.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    out_report.write_text(report(data), encoding="utf-8")
    out_card.write_text(json.dumps(explorer_card(data), indent=2) + "\n", encoding="utf-8")
    print(f"WROTE {out_json}")
    print(f"WROTE {out_report}")
    print(f"WROTE {out_card}")
    print("MACHLIB_POLYNOMIAL_EVIDENCE_V1_READY")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
