#!/usr/bin/env python3
"""Build MachLib factored root packet v14 evidence."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


DATE = "2026-05-25"
DATE_TAG = "2026_05_25"
PACKET_ID = "machlib_factored_root_packet_v14_2026_05_25"
LEAN_PATH = "foundations/MachLib/NormalizedPolynomialRootCount.lean"


CHECKED_RESULTS = [
    "RootEnumeratorSound",
    "rootEnumeratorSound_of_packet",
    "RootCountForKnownPacketTarget",
    "rootCountForKnownPacketTarget_checked",
    "linearFiniteRootPacket",
    "foldNormalizedProductPacket",
    "factoredLinearProductPacket",
    "repeatedLinearProductPacket",
    "RootCountForLinearFactorProductsTarget",
    "rootCountForLinearFactorProductsTarget_checked",
    "RootCountForRepeatedLinearProductsTarget",
    "rootCountForRepeatedLinearProductsTarget_checked",
    "RootCountForFactoredTarget",
    "rootCountForFactoredTarget_checked",
    "RootCountForArbitraryCoeffTarget",
]


FORGE_EFROG_CERTIFICATE_SHAPE = {
    "coeffs": ["Real"],
    "normalization": {
        "kind": "normalized_coeff_list",
        "last_nonzero_required": True,
    },
    "factorization": [
        {"kind": "constant", "value": "c", "nonzero_certificate": "c != 0"},
        {"kind": "linear", "root": "r"},
    ],
    "root_packet_expected": ["deduplicated roots"],
    "evidence_obligations": [
        "RootListSound",
        "RootListDistinct",
        "RootListDegreeBound",
    ],
    "boundary": {
        "forge_compiler_behavior_changed": False,
        "efrog_behavior_changed": False,
        "arbitrary_root_discovery_claim": False,
    },
}


STILL_OPEN = [
    "arbitrary root discovery for normalized coefficient lists",
    "factorization search or certificate import from Forge/eFrog",
    "RootCountInductionTarget proof for arbitrary coefficients",
    "public Explorer/CapCard surfacing of these internal packets",
]


def payload() -> dict:
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_FACTORED_ROOT_PACKET_V14_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "lean_path": LEAN_PATH,
        "checked_result_count": len(CHECKED_RESULTS),
        "checked_results": CHECKED_RESULTS,
        "known_packet_target_status": "CHECKED",
        "linear_factor_product_target_status": "CHECKED",
        "repeated_linear_product_target_status": "CHECKED",
        "factored_packet_composition_target_status": "CHECKED",
        "arbitrary_coeff_target_status": "DEFINED_NOT_PROVED",
        "forge_efrog_certificate_shape": FORGE_EFROG_CERTIFICATE_SHAPE,
        "still_open": STILL_OPEN,
        "bridge_axiom_count": 0,
        "general_root_count_theorem_proved": False,
        "root_count_induction_target_proved": False,
        "arbitrary_root_discovery_claim": False,
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
        "# MachLib Factored Root Packet v14",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{data['status']}`",
        "",
        "## Checked",
        "",
        "v14 adds the first root-enumerator layer above individual examples.",
        "Known finite-root packets can now be composed into factored products;",
        "constant times explicit linear factors can be packetized; repeated",
        "linear roots use the existing unique-union machinery instead of",
        "claiming duplicate roots.",
        "",
    ]
    for name in data["checked_results"]:
        lines.append(f"- `{name}`")
    lines.extend(
        [
            "",
            "## Forge/eFrog Certificate Shape",
            "",
            "Future emitters should provide normalized coefficients, explicit",
            "factorization evidence, and the expected deduplicated root packet.",
            "This task does not change Forge or eFrog behavior.",
            "",
            "```json",
            json.dumps(data["forge_efrog_certificate_shape"], indent=2),
            "```",
            "",
            "## Still Open",
            "",
        ]
    )
    for item in data["still_open"]:
        lines.append(f"- {item}")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This checks factored and known-packet root-count paths, not arbitrary root discovery.",
            "- `RootCountInductionTarget` remains defined but not proved.",
            "- No Forge compiler or eFrog behavior was changed.",
            "- No public theorem/proof/open-problem claim is made.",
            "- No package publish, PETAL/API upload, Hugging Face upload, or marketplace modification.",
        ]
    )
    return "\n".join(lines) + "\n"


def compatibility_report(data: dict) -> str:
    return "\n".join(
        [
            "# MachLib Forge/eFrog Factored Root Packet Contract",
            "",
            f"Date: {DATE}",
            "",
            "This is a report-only compatibility contract. It does not change Forge",
            "or eFrog behavior.",
            "",
            "## Proposed Shape",
            "",
            "```json",
            json.dumps(data["forge_efrog_certificate_shape"], indent=2),
            "```",
            "",
            "## Required Evidence",
            "",
            "- normalized coefficient list",
            "- nonzero constant certificate when a constant scale is present",
            "- explicit linear-factor root list or imported factorization evidence",
            "- deduplicated expected root list",
            "- `RootListSound`, `RootListDistinct`, and `RootListDegreeBound` obligations",
            "",
            "## Non-Claims",
            "",
            "- no arbitrary factorization discovery",
            "- no arbitrary root-count theorem",
            "- no Forge compiler behavior change",
            "- no eFrog behavior change",
            "- no public theorem/proof/open-problem claim",
        ]
    ) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-json", default=f"product_readiness/{PACKET_ID}.json")
    parser.add_argument("--out-report", default=f"reports/{PACKET_ID}.md")
    parser.add_argument(
        "--out-compat-report",
        default=f"reports/machlib_forge_efrog_factored_root_contract_v14_{DATE_TAG}.md",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    data = payload()
    if args.strict:
        if data["checked_result_count"] < 15:
            raise SystemExit("expected at least fifteen checked results")
        for key in [
            "general_root_count_theorem_proved",
            "root_count_induction_target_proved",
            "arbitrary_root_discovery_claim",
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
    out_compat_report = Path(args.out_compat_report)
    for path in [out_json, out_report, out_compat_report]:
        path.parent.mkdir(parents=True, exist_ok=True)
    out_json.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    out_report.write_text(report(data), encoding="utf-8")
    out_compat_report.write_text(compatibility_report(data), encoding="utf-8")
    print(f"WROTE {out_json}")
    print(f"WROTE {out_report}")
    print(f"WROTE {out_compat_report}")
    print(data["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
