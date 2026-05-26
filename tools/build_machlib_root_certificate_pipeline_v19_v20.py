#!/usr/bin/env python3
"""Convert safe quadratic residual classifications into MachLib evidence cards."""

from __future__ import annotations

import argparse
import importlib.util
import json
import sys
from pathlib import Path
from typing import Any


DATE = "2026-05-25"
DATE_TAG = "2026_05_25"
PACKET_ID = "machlib_root_certificate_pipeline_v19_v20_2026_05_25"
V17_TOOL = Path(__file__).with_name("build_machlib_root_pipeline_v17_v18.py")
DEFAULT_V18_PACKET = Path(
    f"product_readiness/machlib_polynomial_root_pipeline_v17_v18_{DATE_TAG}.json"
)


BOUNDARY_FALSE_KEYS = [
    "general_root_count_theorem_proved",
    "root_count_induction_target_proved",
    "analytic_identity_theorem_proved",
    "arbitrary_root_discovery_claim",
    "quadratic_closed_form_theorem_claim",
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
]


def load_v17():
    spec = importlib.util.spec_from_file_location("machlib_root_pipeline_v17_v18", V17_TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


v17 = load_v17()
v15 = v17.v15
v16 = v17.v16


def load_pipeline(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text())


def build_quadratic_import_certificate(row: dict[str, Any]) -> dict[str, Any] | None:
    classification = row["quadratic_classification"]
    if classification["classification"] != "RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE":
        return None

    coeffs = v16.parse_coeffs(row["input_coeffs"])
    if not coeffs:
        return None

    roots = v16.parse_coeffs(row["factored_roots"]) + v16.parse_coeffs(classification["rational_roots"])
    leading_constant = coeffs[-1]
    return {
        "certificate_id": row["case_id"].replace("_v18", "_quadratic_import_v19"),
        "description": f"{row['description']} converted from v18 quadratic residual classification",
        "coeffs": v16.encode_coeffs(v15.normalize(coeffs)),
        "constant": v15.encode_fraction(leading_constant),
        "linear_roots": v16.encode_coeffs(roots),
        "expected_product_coeffs": v16.encode_coeffs(v15.normalize(coeffs)),
        "expected_dedup_roots": v16.encode_coeffs(v15.unique_roots(roots)),
        "normalized": True,
        "source": "machlib_quadratic_residual_classifier_v18",
        "conversion": "RATIONAL_DISCRIMINANT_SQUARE_TO_V15_CERTIFICATE",
    }


def evidence_row(row: dict[str, Any]) -> dict[str, Any]:
    classification = row["quadratic_classification"]["classification"]
    if row["search_status"] == "CERTIFICATE_GENERATED":
        status = "V16_CERTIFICATE_AVAILABLE"
    elif classification == "RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE":
        status = "V19_CERTIFICATE_CONVERTIBLE"
    elif classification in {
        "NEGATIVE_DISCRIMINANT_NO_REAL_ROOTS_IN_QUADRATIC_STUB",
        "IRRATIONAL_ROOTS_BLOCKED_IN_RATIONAL_LAYER",
    }:
        status = "V18_CLASSIFIED_BLOCKER"
    else:
        status = "BOUNDED_SEARCH_BLOCKER"
    return {
        "case_id": row["case_id"],
        "status": status,
        "input_coeffs": row["input_coeffs"],
        "found_roots": row["factored_roots"],
        "remaining_coeffs": row["remaining_coeffs"],
        "residual_degree": row["residual_degree"],
        "quadratic_classification": classification,
        "search_blocker": row["search_blocker"],
        "root_count_induction_target_proved": False,
        "public_theorem_claim": False,
    }


def build_payload(pipeline: dict[str, Any]) -> dict[str, Any]:
    imported: list[dict[str, Any]] = []
    validations: list[dict[str, Any]] = []
    conversion_blockers: list[dict[str, Any]] = []

    for row in pipeline["residual_packets"]:
        certificate = build_quadratic_import_certificate(row)
        if certificate is None:
            conversion_blockers.append(
                {
                    "case_id": row["case_id"],
                    "classification": row["quadratic_classification"]["classification"],
                    "reason": row["quadratic_classification"].get("blocker") or row.get("search_blocker"),
                }
            )
            continue
        validation = v15.validate_certificate(certificate).__dict__
        validations.append(validation)
        if validation["status"] == "PASS":
            imported.append(certificate)

    failed_validations = [row for row in validations if row["status"] != "PASS"]
    evidence_rows = [evidence_row(row) for row in pipeline["residual_packets"]]
    status = (
        "MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_READY"
        if imported and not failed_validations
        else "MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_BLOCKED"
    )
    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": status,
        "source_pipeline": pipeline["packet_id"],
        "source_pipeline_status": pipeline["status"],
        "case_count": pipeline["case_count"],
        "v16_certificate_generated_count": pipeline["certificate_generated_count"],
        "v18_quadratic_classification_count": pipeline["quadratic_classification_count"],
        "v19_imported_certificate_count": len(imported),
        "v19_validation_failure_count": len(failed_validations),
        "v19_imported_certificates": imported,
        "v19_validations": validations,
        "v19_conversion_blockers": conversion_blockers,
        "v20_evidence_rows": evidence_rows,
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "forge_efrog_compatibility_status": "REPORT_ONLY_NO_BEHAVIOR_CHANGE",
        "boundary": {key: False for key in BOUNDARY_FALSE_KEYS},
    }


def certificate_import_report(payload: dict[str, Any]) -> str:
    lines = [
        "# MachLib Quadratic Certificate Import v19",
        "",
        f"Date: {DATE}",
        "",
        f"Status: `{payload['status']}`",
        "",
        "## Summary",
        "",
        "v19 converts only residual quadratic rows with rational-square",
        "discriminants into v15-compatible factorization certificates.",
        "",
        f"- Source cases: {payload['case_count']}",
        f"- v18 quadratic classifications: {payload['v18_quadratic_classification_count']}",
        f"- v19 imported certificates: {payload['v19_imported_certificate_count']}",
        f"- v19 validation failures: {payload['v19_validation_failure_count']}",
        "",
        "| certificate | status | roots |",
        "| --- | --- | --- |",
    ]
    validations = {row["certificate_id"]: row for row in payload["v19_validations"]}
    for cert in payload["v19_imported_certificates"]:
        status = validations[cert["certificate_id"]]["status"]
        lines.append(f"| `{cert['certificate_id']}` | {status} | `{cert['linear_roots']}` |")
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- This is certificate conversion for rational-square quadratic residuals only.",
            "- It does not claim arbitrary root discovery.",
            "- It does not prove the general root-count theorem.",
            "- It does not change Forge or eFrog behavior.",
        ]
    )
    return "\n".join(lines) + "\n"


def evidence_card(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "card_id": "machlib_degree_root_evidence_card_v20_2026_05_25",
        "title": "MachLib degree/root evidence pipeline",
        "status": payload["status"],
        "visibility": "internal",
        "summary": "Bounded rational search, residual classification, and safe quadratic certificate conversion.",
        "source_pipeline": payload["source_pipeline"],
        "case_count": payload["case_count"],
        "v16_certificate_generated_count": payload["v16_certificate_generated_count"],
        "v18_quadratic_classification_count": payload["v18_quadratic_classification_count"],
        "v19_imported_certificate_count": payload["v19_imported_certificate_count"],
        "evidence_rows": payload["v20_evidence_rows"],
        "root_count_induction_target_proved": False,
        "public_ready": False,
        "marketplace_ready": False,
        "production_marketplace_modified": False,
    }


def evidence_card_report(card: dict[str, Any]) -> str:
    lines = [
        "# MachLib Degree/Root Evidence Card v20",
        "",
        f"Status: `{card['status']}`",
        "",
        "This internal card is shaped for Explorer/CapCard consumption. It",
        "summarizes coefficient inputs, found roots, residuals, blockers, and",
        "safe certificate conversion status.",
        "",
        "| case | status | roots | residual | classification |",
        "| --- | --- | --- | --- | --- |",
    ]
    for row in card["evidence_rows"]:
        lines.append(
            f"| `{row['case_id']}` | {row['status']} | `{row['found_roots']}` | "
            f"`{row['remaining_coeffs']}` | {row['quadratic_classification']} |"
        )
    lines.extend(
        [
            "",
            "## Boundary",
            "",
            "- Internal evidence card only.",
            "- No public-ready or marketplace-ready claim.",
            "- No public theorem/proof/open-problem claim.",
        ]
    )
    return "\n".join(lines) + "\n"


def compatibility_packet() -> dict[str, Any]:
    return {
        "packet_id": "machlib_forge_efrog_polynomial_certificate_compatibility_v20_2026_05_25",
        "date": DATE,
        "status": "REPORT_ONLY_NO_BEHAVIOR_CHANGE",
        "future_certificate_shape": {
            "coeffs": "low_to_high_normalized_coefficients",
            "constant": "leading_coefficient_for_linear_factor_product",
            "linear_roots": "ordered_exact_roots_when_known",
            "expected_product_coeffs": "normalized_coefficients_for_validation",
            "expected_dedup_roots": "deduplicated_roots_for_root_count_packets",
            "normalized": True,
        },
        "forge_compiler_behavior_changed": False,
        "efrog_behavior_changed": False,
        "root_count_induction_target_proved": False,
        "public_ready": False,
        "marketplace_ready": False,
    }


def compatibility_report(packet: dict[str, Any]) -> str:
    return "\n".join(
        [
            "# Forge/eFrog Polynomial Certificate Compatibility v20",
            "",
            f"Status: `{packet['status']}`",
            "",
            "This report defines the future certificate shape that Forge/eFrog",
            "could emit for MachLib polynomial evidence packets. It is report-only.",
            "",
            "## Future Shape",
            "",
            "- `coeffs`: low-to-high normalized coefficient list.",
            "- `constant`: leading coefficient for the linear-factor product.",
            "- `linear_roots`: ordered exact roots when known.",
            "- `expected_product_coeffs`: normalized coefficients to validate against.",
            "- `expected_dedup_roots`: deduplicated roots for finite root-count packets.",
            "- `normalized`: must be true.",
            "",
            "## Boundary",
            "",
            "- No Forge compiler behavior changed.",
            "- No eFrog behavior changed.",
            "- No general root-count theorem claim.",
        ]
    ) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", default=str(DEFAULT_V18_PACKET))
    parser.add_argument(
        "--out-json",
        default=f"product_readiness/{PACKET_ID}.json",
    )
    parser.add_argument(
        "--out-certificates",
        default=f"product_readiness/machlib_quadratic_certificate_import_v19_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-card",
        default=f"product_readiness/machlib_degree_root_evidence_card_v20_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-compat-json",
        default=f"product_readiness/machlib_forge_efrog_polynomial_certificate_compatibility_v20_{DATE_TAG}.json",
    )
    parser.add_argument(
        "--out-report",
        default=f"reports/machlib_quadratic_certificate_import_v19_{DATE_TAG}.md",
    )
    parser.add_argument(
        "--out-card-report",
        default=f"reports/machlib_degree_root_evidence_card_v20_{DATE_TAG}.md",
    )
    parser.add_argument(
        "--out-compat-report",
        default=f"reports/machlib_forge_efrog_polynomial_certificate_compatibility_v20_{DATE_TAG}.md",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    payload = build_payload(load_pipeline(Path(args.source)))
    card = evidence_card(payload)
    compat = compatibility_packet()

    if args.strict:
        if payload["status"] != "MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_READY":
            raise SystemExit("v19/v20 root certificate pipeline failed")
        if payload["v19_imported_certificate_count"] < 1:
            raise SystemExit("expected at least one imported quadratic certificate")
        if payload["v19_validation_failure_count"] != 0:
            raise SystemExit("expected zero v19 validation failures")
        for key, value in payload["boundary"].items():
            if value is not False:
                raise SystemExit(f"boundary.{key} must be false")

    paths = {
        "json": Path(args.out_json),
        "certificates": Path(args.out_certificates),
        "card": Path(args.out_card),
        "compat_json": Path(args.out_compat_json),
        "report": Path(args.out_report),
        "card_report": Path(args.out_card_report),
        "compat_report": Path(args.out_compat_report),
    }
    for path in paths.values():
        path.parent.mkdir(parents=True, exist_ok=True)

    paths["json"].write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    paths["certificates"].write_text(
        json.dumps(
            {
                "date": DATE,
                "source": PACKET_ID,
                "certificates": payload["v19_imported_certificates"],
                "validations": payload["v19_validations"],
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )
    paths["card"].write_text(json.dumps(card, indent=2) + "\n", encoding="utf-8")
    paths["compat_json"].write_text(json.dumps(compat, indent=2) + "\n", encoding="utf-8")
    paths["report"].write_text(certificate_import_report(payload), encoding="utf-8")
    paths["card_report"].write_text(evidence_card_report(card), encoding="utf-8")
    paths["compat_report"].write_text(compatibility_report(compat), encoding="utf-8")

    for path in paths.values():
        print(f"WROTE {path}")
    print(payload["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
