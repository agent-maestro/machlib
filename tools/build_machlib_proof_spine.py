#!/usr/bin/env python3
"""Build the MachLib proof-spine v1 evidence packet."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
SPINE_ID = "machlib_proof_spine_v1_2026_05_25"
LEAN_PATH = "foundations/MachLib/ProofSpine.lean"


OBLIGATIONS = [
    {
        "id": "eml_exp_branch_checked",
        "family": "eml_primitive",
        "lean_name": "MachLib.ProofSpine.eml_exp_branch_checked",
        "statement": "eml x 1 = exp x",
        "source_surface": ["Explorer EML primitive bridge", "Forge lowering contract"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "eml_log_branch_checked",
        "family": "eml_primitive",
        "lean_name": "MachLib.ProofSpine.eml_log_branch_checked",
        "statement": "eml 0 y = 1 - log y",
        "source_surface": ["Explorer EML primitive bridge", "Forge lowering contract"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "exp_zero_checked",
        "family": "normalization",
        "lean_name": "MachLib.ProofSpine.exp_zero_checked",
        "statement": "exp 0 = 1",
        "source_surface": ["EML IR lowering", "SuperBEST rewrite hygiene"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "exp_sub_checked",
        "family": "exp_rewrite",
        "lean_name": "MachLib.ProofSpine.exp_sub_checked",
        "statement": "exp (x - y) = exp x / exp y",
        "source_surface": ["EML IR lowering", "Forge obligation shape"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "sin_cos_pythagorean_checked",
        "family": "trig_identity",
        "lean_name": "MachLib.ProofSpine.sin_cos_pythagorean_checked",
        "statement": "sin x * sin x + cos x * cos x = 1",
        "source_surface": ["Explorer identity table", "Forge rotation witnesses"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "cos_sin_pythagorean_swapped_checked",
        "family": "trig_identity",
        "lean_name": "MachLib.ProofSpine.cos_sin_pythagorean_swapped_checked",
        "statement": "cos x * cos x + sin x * sin x = 1",
        "source_surface": ["Forge matrix witnesses", "Explorer row notes"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "cosh_sinh_pythagorean_checked",
        "family": "hyperbolic_identity",
        "lean_name": "MachLib.ProofSpine.cosh_sinh_pythagorean_checked",
        "statement": "cosh x * cosh x - sinh x * sinh x = 1",
        "source_surface": ["PETAL curriculum", "EML hyperbolic bridge"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "cosh_exp_decomposition_checked",
        "family": "hyperbolic_to_exp",
        "lean_name": "MachLib.ProofSpine.cosh_exp_decomposition_checked",
        "statement": "cosh x = (exp x + exp (-x)) / (1 + 1)",
        "source_surface": ["PETAL curriculum", "EML IR lowering"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "nonneg_product_guard_checked",
        "family": "guard_contract",
        "lean_name": "MachLib.ProofSpine.nonneg_product_guard_checked",
        "statement": "0 <= a -> 0 <= b -> 0 <= a * b",
        "source_surface": ["Forge guard obligations", "Monogate OS guard vocabulary"],
        "evidence_class": "MACHLIB_CHECKED",
    },
    {
        "id": "saturate_lower_guard_checked",
        "family": "guard_contract",
        "lean_name": "MachLib.ProofSpine.saturate_lower_guard_checked",
        "statement": "0 <= max 0 (min x 1)",
        "source_surface": ["Forge clamp obligations", "CapCard evidence cards"],
        "evidence_class": "MACHLIB_CHECKED",
    },
]


def build_payload() -> dict:
    return {
        "spine_id": SPINE_ID,
        "status": "MACHLIB_PROOF_SPINE_V1_READY",
        "date": DATE,
        "lean_module": "MachLib.ProofSpine",
        "lean_path": LEAN_PATH,
        "obligation_count": len(OBLIGATIONS),
        "checked_count": len(OBLIGATIONS),
        "blocked_count": 0,
        "obligations": OBLIGATIONS,
        "capcard_use": "internal_evidence_reference",
        "explorer_use": "prototype_identity_evidence",
        "forge_use": "lowering_contract_examples",
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


def build_report(payload: dict) -> str:
    lines = [
        "# MachLib Proof Spine v1",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Purpose",
        "",
        "This packet makes the Lean verification role concrete: ten small",
        "EML / Forge / Explorer / CapCard-facing obligations now have named",
        "MachLib artifacts in `MachLib.ProofSpine`.",
        "",
        "This is not a broad theorem-library claim and not a public theorem",
        "promotion. It is an internal evidence spine for checked artifacts.",
        "",
        "## Obligations",
        "",
    ]
    for item in payload["obligations"]:
        surfaces = ", ".join(item["source_surface"])
        lines.extend(
            [
                f"- `{item['id']}`",
                f"  - family: `{item['family']}`",
                f"  - statement: `{item['statement']}`",
                f"  - Lean: `{item['lean_name']}`",
                f"  - surfaces: {surfaces}",
            ]
        )
    lines.extend(
        [
            "",
            "## Boundaries",
            "",
            "- Internal evidence reference only.",
            "- Not marketplace-ready.",
            "- No package publish.",
            "- No PETAL/API or Hugging Face upload.",
            "- No safety-certification or controller-status claim.",
            "- No public theorem/proof/open-problem claim.",
        ]
    )
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-json", default=f"product_readiness/{SPINE_ID}.json")
    parser.add_argument("--out-report", default=f"reports/{SPINE_ID}.md")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    payload = build_payload()
    if args.strict and payload["obligation_count"] < 10:
        raise SystemExit("expected at least 10 proof-spine obligations")
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
        if payload[key] is not False:
            raise SystemExit(f"{key} must be false")

    out_json = Path(args.out_json)
    out_report = Path(args.out_report)
    out_json.parent.mkdir(parents=True, exist_ok=True)
    out_report.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    out_report.write_text(build_report(payload), encoding="utf-8")
    print(f"WROTE {out_json}")
    print(f"WROTE {out_report}")
    print("MACHLIB_PROOF_SPINE_V1_READY")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
