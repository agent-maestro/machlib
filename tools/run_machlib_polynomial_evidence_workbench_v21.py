#!/usr/bin/env python3
"""MachLib polynomial evidence workbench v21-v25.

This is an internal bounded evidence tool. It accepts a coefficient list or a
tiny polynomial expression, routes it through the v16/v18/v19 pipeline, and
emits Explorer/CapCard-shaped internal evidence packets.
"""

from __future__ import annotations

import argparse
import ast
import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


DATE = "2026-05-25"
DATE_TAG = "2026_05_25"
PACKET_ID = "machlib_polynomial_evidence_workbench_v21_2026_05_25"
V16_TOOL = Path(__file__).with_name("run_machlib_rational_root_search_v16.py")
V19_TOOL = Path(__file__).with_name("build_machlib_root_certificate_pipeline_v19_v20.py")


BOUNDARY_FALSE_KEYS = [
    "general_root_count_theorem_proved",
    "root_count_induction_target_proved",
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


def load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


v16 = load_module("machlib_rational_root_search_v16_for_workbench", V16_TOOL)
v19 = load_module("machlib_root_certificate_pipeline_v19_for_workbench", V19_TOOL)
v15 = v16.v15
v17 = v19.v17


def trim(coeffs: list[Fraction]) -> list[Fraction]:
    return v15.normalize(coeffs)


def add_poly(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    out = [Fraction(0, 1)] * max(len(left), len(right))
    for i, value in enumerate(left):
        out[i] += value
    for i, value in enumerate(right):
        out[i] += value
    return trim(out)


def neg_poly(value: list[Fraction]) -> list[Fraction]:
    return trim([-x for x in value])


def mul_poly(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    return trim(v15.mul_coeff(left, right))


def pow_poly(base: list[Fraction], exponent: int) -> list[Fraction]:
    if exponent < 0:
        raise ValueError("negative polynomial powers are not supported")
    out = [Fraction(1, 1)]
    for _ in range(exponent):
        out = mul_poly(out, base)
    return out


def parse_number_node(node: ast.AST) -> Fraction:
    if isinstance(node, ast.Constant) and isinstance(node.value, int):
        return Fraction(node.value, 1)
    if isinstance(node, ast.Constant) and isinstance(node.value, float):
        return Fraction(str(node.value))
    raise ValueError("only numeric constants are supported in polynomial expressions")


def parse_poly_node(node: ast.AST) -> list[Fraction]:
    if isinstance(node, ast.Expression):
        return parse_poly_node(node.body)
    if isinstance(node, ast.Name):
        if node.id != "x":
            raise ValueError("only variable x is supported")
        return [Fraction(0, 1), Fraction(1, 1)]
    if isinstance(node, ast.Constant):
        return [parse_number_node(node)]
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub):
        return neg_poly(parse_poly_node(node.operand))
    if isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.UAdd):
        return parse_poly_node(node.operand)
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
        return add_poly(parse_poly_node(node.left), parse_poly_node(node.right))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Sub):
        return add_poly(parse_poly_node(node.left), neg_poly(parse_poly_node(node.right)))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Mult):
        return mul_poly(parse_poly_node(node.left), parse_poly_node(node.right))
    if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Pow):
        exponent = parse_number_node(node.right)
        if exponent.denominator != 1:
            raise ValueError("polynomial powers must be integer constants")
        return pow_poly(parse_poly_node(node.left), exponent.numerator)
    raise ValueError("unsupported expression form")


def parse_polynomial_expr(expr: str) -> list[int | str]:
    tree = ast.parse(expr.replace("^", "**"), mode="eval")
    coeffs = parse_poly_node(tree)
    return v16.encode_coeffs(coeffs)


def parse_coeffs_text(text: str) -> list[int | str]:
    return v16.parse_coeff_argument(text)


def build_single_pipeline(
    coeffs: list[int | str],
    *,
    source_kind: str,
    source_text: str,
    root_limit: int,
    denominator_limit: int,
) -> dict[str, Any]:
    case = {
        "case_id": "workbench_input_v21",
        "description": f"Workbench input from {source_kind}",
        "coeffs": coeffs,
    }
    search = v16.run_cases([case], root_limit, denominator_limit)
    residual = v17.residual_packet(case, search["case_results"][0])
    imported_certificate = v19.build_quadratic_import_certificate(residual)
    imported_validation = None
    if imported_certificate is not None:
        imported_validation = v15.validate_certificate(imported_certificate).__dict__

    if search["certificate_generated_count"] > 0:
        workbench_status = "CERTIFICATE_AVAILABLE"
    elif imported_validation and imported_validation["status"] == "PASS":
        workbench_status = "CERTIFICATE_IMPORTED_FROM_QUADRATIC_RESIDUAL"
    else:
        workbench_status = "BLOCKED_WITH_EXACT_REASON"

    return {
        "packet_id": PACKET_ID,
        "date": DATE,
        "status": "MACHLIB_POLYNOMIAL_EVIDENCE_WORKBENCH_V21_READY",
        "source_kind": source_kind,
        "source_text": source_text,
        "coeffs": coeffs,
        "root_limit": root_limit,
        "denominator_limit": denominator_limit,
        "workbench_status": workbench_status,
        "v16_search": search,
        "v17_residual_packet": residual,
        "v18_quadratic_classification": residual["quadratic_classification"],
        "v19_imported_certificate": imported_certificate,
        "v19_imported_validation": imported_validation,
        "root_count_induction_target_status": "DEFINED_NOT_PROVED",
        "boundary": {key: False for key in BOUNDARY_FALSE_KEYS},
    }


def explorer_export(payload: dict[str, Any]) -> dict[str, Any]:
    result = payload["v16_search"]["case_results"][0]
    validation = payload["v19_imported_validation"]
    return {
        "export_id": "machlib_explorer_root_packet_export_v22_2026_05_25",
        "status": "INTERNAL_EXPLORER_EXPORT_READY",
        "title": "MachLib polynomial root evidence",
        "source_packet": payload["packet_id"],
        "coeffs": payload["coeffs"],
        "found_roots": result["linear_roots"],
        "remaining_coeffs": result["remaining_coeffs"],
        "search_status": result["status"],
        "search_blocker": result["blocker"],
        "quadratic_classification": payload["v18_quadratic_classification"],
        "certificate_status": None if validation is None else validation["status"],
        "imported_certificate_id": None
        if payload["v19_imported_certificate"] is None
        else payload["v19_imported_certificate"]["certificate_id"],
        "ui_sections": [
            "coefficients",
            "found_roots",
            "residual",
            "blocker_or_classification",
            "certificate_status",
            "claim_boundary",
        ],
        "public_ready": False,
        "marketplace_ready": False,
        "root_count_induction_target_proved": False,
    }


def root_count_target_inventory() -> dict[str, Any]:
    return {
        "packet_id": "machlib_root_count_target_inventory_v23_2026_05_25",
        "status": "ROOT_COUNT_TARGET_INVENTORY_READY",
        "lean_module": "MachLib.NormalizedPolynomialRootCount",
        "checked_targets": [
            "rootCountForKnownPacketTarget_checked",
            "rootCountForLinearFactorProductsTarget_checked",
            "rootCountForRepeatedLinearProductsTarget_checked",
            "rootCountForFactoredTarget_checked",
        ],
        "defined_not_proved_targets": [
            "RootCountInductionTarget",
            "RootCountForArbitraryCoeffTarget",
        ],
        "exact_theorem_shape": {
            "input": "normalized coefficient list p",
            "nonzero_witness": "LastNonzero p",
            "output": "finite root list roots",
            "requirements": [
                "RootListSound p roots",
                "RootListDistinct roots",
                "RootListDegreeBound p roots",
            ],
        },
        "next_lean_bridge": "derive more assumptions behind certificate validation, then attack arbitrary root enumeration only with explicit factorization evidence",
        "root_count_induction_target_proved": False,
        "public_theorem_claim": False,
    }


def validation_bridge(payload: dict[str, Any]) -> dict[str, Any]:
    validation = payload["v19_imported_validation"]
    return {
        "packet_id": "machlib_certificate_validation_bridge_v24_2026_05_25",
        "status": "DERIVED_EXECUTABLE_CERTIFICATE_VALIDATION_READY"
        if validation and validation["status"] == "PASS"
        else "DERIVED_EXECUTABLE_CERTIFICATE_VALIDATION_BLOCKED",
        "bridge": "exact coefficient product reconstruction plus root evaluation validation",
        "input_certificate_id": None
        if payload["v19_imported_certificate"] is None
        else payload["v19_imported_certificate"]["certificate_id"],
        "validation": validation,
        "derived_bridge_scope": "executable exact arithmetic certificate validation, not a Lean theorem",
        "product_evaluation_soundness_status": "EXECUTABLE_CHECKED_FOR_IMPORTED_CERTIFICATE"
        if validation and validation["status"] == "PASS"
        else "NO_IMPORTED_CERTIFICATE",
        "root_count_induction_target_proved": False,
        "public_theorem_claim": False,
    }


def efrog_adapter_packet(payload: dict[str, Any]) -> dict[str, Any]:
    return {
        "packet_id": "machlib_efrog_polynomial_adapter_dry_run_v25_2026_05_25",
        "status": "EFROG_POLYNOMIAL_ADAPTER_DRY_RUN_READY",
        "source_kind": payload["source_kind"],
        "source_text": payload["source_text"],
        "emitted_coeffs": payload["coeffs"],
        "certificate_shape": {
            "coeffs": "low_to_high_normalized_coefficients",
            "constant": "leading_coefficient_for_linear_factor_product",
            "linear_roots": "ordered_exact_roots_when_known",
            "expected_product_coeffs": "normalized_coefficients_for_validation",
            "expected_dedup_roots": "deduplicated_roots_for finite root-count packets",
            "normalized": True,
        },
        "efrog_behavior_changed": False,
        "forge_compiler_behavior_changed": False,
        "adapter_mode": "dry_run_only",
        "public_ready": False,
        "marketplace_ready": False,
    }


def markdown_report(payload: dict[str, Any], export: dict[str, Any]) -> str:
    q = payload["v18_quadratic_classification"]
    return "\n".join(
        [
            "# MachLib Polynomial Evidence Workbench v21",
            "",
            f"Status: `{payload['status']}`",
            f"Workbench result: `{payload['workbench_status']}`",
            "",
            "## Input",
            "",
            f"- Source: `{payload['source_kind']}`",
            f"- Text: `{payload['source_text']}`",
            f"- Coefficients: `{payload['coeffs']}`",
            "",
            "## Evidence",
            "",
            f"- Search status: `{export['search_status']}`",
            f"- Found roots: `{export['found_roots']}`",
            f"- Remaining coefficients: `{export['remaining_coeffs']}`",
            f"- Quadratic classification: `{q['classification']}`",
            f"- Certificate status: `{export['certificate_status']}`",
            "",
            "## Boundary",
            "",
            "- Bounded exact arithmetic only.",
            "- No arbitrary root discovery claim.",
            "- RootCountInductionTarget remains defined but not proved.",
            "- No Forge/eFrog behavior change.",
            "- Internal Explorer export only.",
        ]
    ) + "\n"


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--coeffs", help="Comma-separated low-to-high coefficients, e.g. 56,-15,1")
    group.add_argument("--expr", help="Tiny polynomial expression, e.g. x^2 - 15*x + 56")
    parser.add_argument("--root-limit", type=int, default=6)
    parser.add_argument("--denominator-limit", type=int, default=4)
    parser.add_argument("--out-dir", default="product_readiness")
    parser.add_argument("--report-dir", default="reports")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    if args.expr:
        coeffs = parse_polynomial_expr(args.expr)
        source_kind = "efrog_dry_run_expression"
        source_text = args.expr
    else:
        text = args.coeffs or "56,-15,1"
        coeffs = parse_coeffs_text(text)
        source_kind = "coefficient_list"
        source_text = text

    payload = build_single_pipeline(
        coeffs,
        source_kind=source_kind,
        source_text=source_text,
        root_limit=args.root_limit,
        denominator_limit=args.denominator_limit,
    )
    export = explorer_export(payload)
    inventory = root_count_target_inventory()
    bridge = validation_bridge(payload)
    adapter = efrog_adapter_packet(payload)

    if args.strict:
        if payload["status"] != "MACHLIB_POLYNOMIAL_EVIDENCE_WORKBENCH_V21_READY":
            raise SystemExit("workbench status mismatch")
        if export["status"] != "INTERNAL_EXPLORER_EXPORT_READY":
            raise SystemExit("Explorer export status mismatch")
        if payload["workbench_status"] == "CERTIFICATE_IMPORTED_FROM_QUADRATIC_RESIDUAL":
            validation = payload["v19_imported_validation"]
            if validation is None or validation["status"] != "PASS":
                raise SystemExit("imported certificate validation must pass")
        for key, value in payload["boundary"].items():
            if value is not False:
                raise SystemExit(f"boundary.{key} must be false")

    out_dir = Path(args.out_dir)
    report_dir = Path(args.report_dir)
    outputs = {
        out_dir / f"{PACKET_ID}.json": payload,
        out_dir / f"machlib_explorer_root_packet_export_v22_{DATE_TAG}.json": export,
        out_dir / f"machlib_root_count_target_inventory_v23_{DATE_TAG}.json": inventory,
        out_dir / f"machlib_certificate_validation_bridge_v24_{DATE_TAG}.json": bridge,
        out_dir / f"machlib_efrog_polynomial_adapter_dry_run_v25_{DATE_TAG}.json": adapter,
    }
    for path, data in outputs.items():
        write_json(path, data)

    report_dir.mkdir(parents=True, exist_ok=True)
    (report_dir / f"machlib_polynomial_evidence_workbench_v21_{DATE_TAG}.md").write_text(
        markdown_report(payload, export),
        encoding="utf-8",
    )
    (report_dir / f"machlib_root_count_target_inventory_v23_{DATE_TAG}.md").write_text(
        "# MachLib Root-Count Target Inventory v23\n\n"
        f"Status: `{inventory['status']}`\n\n"
        "Checked targets compose known packets and explicit linear-factor products.\n"
        "`RootCountInductionTarget` and `RootCountForArbitraryCoeffTarget` remain defined but not proved.\n",
        encoding="utf-8",
    )
    (report_dir / f"machlib_efrog_polynomial_adapter_dry_run_v25_{DATE_TAG}.md").write_text(
        "# MachLib eFrog Polynomial Adapter Dry Run v25\n\n"
        f"Status: `{adapter['status']}`\n\n"
        f"Input `{adapter['source_text']}` emitted coefficients `{adapter['emitted_coeffs']}`.\n"
        "This is a dry-run adapter only; Forge/eFrog behavior was not changed.\n",
        encoding="utf-8",
    )

    for path in list(outputs) + [
        report_dir / f"machlib_polynomial_evidence_workbench_v21_{DATE_TAG}.md",
        report_dir / f"machlib_root_count_target_inventory_v23_{DATE_TAG}.md",
        report_dir / f"machlib_efrog_polynomial_adapter_dry_run_v25_{DATE_TAG}.md",
    ]:
        print(f"WROTE {path}")
    print(payload["status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
