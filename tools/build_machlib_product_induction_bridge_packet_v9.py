#!/usr/bin/env python3
"""Build MachLib product-induction bridge packet v9 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
PACKET_ID = "machlib_product_induction_bridge_packet_v9_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_BRIDGES = [
    {
        "lean_name": "stagedTripleLinearCoeff_evalSound",
        "status": "CHECKED",
        "meaning": "explicit staged triple-linear coefficient list evaluates as product",
    },
    {
        "lean_name": "linearLinearFiniteRootPacket",
        "status": "CHECKED_PACKET_CONSTRUCTOR",
        "meaning": "full finite-root packet for (x-r)(x-s)",
    },
    {
        "lean_name": "repeatedLinearFiniteRootPacket",
        "status": "CHECKED_PACKET_CONSTRUCTOR",
        "meaning": "full finite-root packet for (x-r)^2",
    },
    {
        "lean_name": "scaledLinearFiniteRootPacket",
        "status": "CHECKED_PACKET_CONSTRUCTOR",
        "meaning": "full finite-root packet for nonzero constant times linear",
    },
    {
        "lean_name": "stagedTripleLinearFiniteRootPacket",
        "status": "CHECKED_PACKET_CONSTRUCTOR",
        "meaning": "full finite-root packet for staged (x-r)(x-s)(x-t)",
    },
    {
        "lean_name": "linearQuadraticFiniteRootPacketWithCertificate",
        "status": "CHECKED_CERTIFICATE_CONSUMER",
        "meaning": "linear times quadratic can consume a full quadratic packet when available",
    },
    {
        "lean_name": "mulCoeffFiniteRootPacketWithDegreeGrowthCert",
        "status": "CHECKED_GENERIC_BRIDGE",
        "meaning": "generic convolution root packet constructor once normalized product degree-growth facts are supplied",
    },
]


TARGETS_NAMED = [
    {
        "lean_name": "NormalizedMulCoeffDegreeGrowthTarget",
        "status": "TARGET_NAMED_NOT_PROVED",
        "meaning": "arbitrary normalized nonzero product has degree budget equal to factor-degree sum",
    },
    {
        "lean_name": "NormalizeCoeffEvalSoundTarget",
        "status": "TARGET_NAMED_NOT_PROVED",
        "meaning": "trailing-zero normalization preserves coefficient-list evaluation",
    },
]


STILL_BLOCKED = [
    "prove NormalizeCoeffEvalSoundTarget so normalizedProductCoeff inherits mulCoeff root soundness",
    "prove LastNonzero (mulCoeff p q) for normalized nonzero p and q",
    "prove ProductDegreeGrowthCert (normalizedProductCoeff p q) p q for arbitrary normalized nonzero p and q",
    "derive the full root-count induction theorem from the generic product packet bridge",
    "replace the linear-quadratic certificate consumer with a complete quadratic root enumerator",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_PRODUCT_INDUCTION_BRIDGE_PACKET_V9_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_bridge_count": len(CHECKED_BRIDGES),
        "checked_bridges": CHECKED_BRIDGES,
        "target_count": len(TARGETS_NAMED),
        "targets_named": TARGETS_NAMED,
        "root_enumeration_status": "FULL_FOR_LINEAR_LINEAR_REPEATED_SCALED_AND_STAGED_TRIPLE; CERTIFICATE_CONSUMER_FOR_LINEAR_QUADRATIC",
        "mulCoeff_generic_packet_status": "CHECKED_WITH_NORMALIZATION_AND_DEGREE_GROWTH_CERTIFICATES",
        "normalized_product_degree_growth_status": "TARGET_NAMED_NOT_PROVED",
        "normalize_eval_soundness_status": "TARGET_NAMED_NOT_PROVED",
        "still_blocked": STILL_BLOCKED,
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "arbitrary_normalized_product_degree_growth_proved": False,
        "normalize_eval_soundness_proved": False,
        "analytic_identity_theorem_proved": False,
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
        "# MachLib Product-Induction Bridge Packet v9",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## What This Unlocks",
        "",
        "v9 replaces several certificate-only root examples with checked finite-root",
        "packet constructors. Linear-linear, repeated-linear, nonzero constant-scaled",
        "linear, and staged triple-linear products now have full packet constructors.",
        "",
        "It also adds a generic `mulCoeff` packet bridge: if a caller supplies the",
        "two still-hard product-degree facts for the concrete convolution output,",
        "MachLib can assemble the finite-root packet by checked root splitting,",
        "deduplication, and cardinality arithmetic.",
        "",
        "## Checked Bridges",
        "",
    ]
    for item in data["checked_bridges"]:
        lines.append(f"- `{item['lean_name']}`: {item['status']} - {item['meaning']}")
    lines.extend(["", "## Named Targets", ""])
    for item in data["targets_named"]:
        lines.append(f"- `{item['lean_name']}`: {item['status']} - {item['meaning']}")
    lines.extend(["", "## Still Blocked", ""])
    for item in data["still_blocked"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This packet does not prove arbitrary normalized product degree growth.",
            "- This packet does not prove the general polynomial root-count theorem.",
            "- It names the exact remaining theorem targets and supplies checked packet bridges around them.",
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
        if data["checked_bridge_count"] < 7:
            raise SystemExit("expected at least seven checked bridges")
        if data["bridge_axiom_count"] != 0:
            raise SystemExit("expected no bridge axioms")
        for key in [
            "general_root_count_theorem_proved",
            "arbitrary_normalized_product_degree_growth_proved",
            "normalize_eval_soundness_proved",
            "analytic_identity_theorem_proved",
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
