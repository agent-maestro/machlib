#!/usr/bin/env python3
"""Validate MachLib function-class draft EML records."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
MIN_COUNTS = {
    "D_FINITE_CERTIFICATE": 5,
    "ANALYTIC_LOCAL_SERIES": 4,
    "SMOOTH_FINITE_JET": 4,
    "CONTINUITY_EPSILON_DELTA": 4,
}
BOUNDARY_CLASSES = {"CLASS_BOUNDARY_RELATION", "NON_EXAMPLE_OR_LIMITATION"}
REQUIRED_FIELDS = {
    "record_id",
    "function_class",
    "title",
    "expression_or_object",
    "local_domain_or_guard",
    "certificate_type",
    "certificate_payload",
    "assumptions",
    "validation_checks",
    "limitations",
    "not_claimed",
    "public_ready",
    "upload_allowed",
    "release_ready",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
    "status",
}
FALSE_FIELDS = {
    "public_ready",
    "upload_allowed",
    "release_ready",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
}
BLOCKED_PHRASES = [
    "public theorem result",
    "public proof result",
    "public open-problem result",
    "complete real-analysis formalization",
    "fully formalizes real analysis",
    "fully replaces the external formal-library ecosystem",
    "replaces the external formal-library ecosystem",
]
TOKEN_RE = re.compile(r"hf_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,}|pypi-[A-Za-z0-9]{20,}")
MATHLIB_NEEDLES = ["import " + "Mathlib", "from " + "Mathlib", "Mathlib" + "."]


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def iter_json_files(root: Path) -> list[Path]:
    return sorted(path for path in root.rglob("*.json") if path.is_file())


def collect_records(root: Path) -> tuple[list[dict[str, Any]], list[str]]:
    failures: list[str] = []
    records: list[dict[str, Any]] = []
    for path in iter_json_files(root):
        try:
            obj = load_json(path)
        except Exception as exc:  # pragma: no cover - exercised through CLI
            failures.append(f"{path}: JSON parse failed: {exc}")
            continue
        if isinstance(obj, dict) and isinstance(obj.get("records"), list):
            for row in obj["records"]:
                if isinstance(row, dict):
                    records.append(row)
                else:
                    failures.append(f"{path}: non-object record present")
    return records, failures


def text_scan(root: Path) -> list[str]:
    failures: list[str] = []
    for path in sorted(p for p in root.rglob("*") if p.is_file()):
        text = path.read_text(encoding="utf-8", errors="ignore")
        for needle in MATHLIB_NEEDLES:
            if needle in text:
                failures.append(f"{path}: blocked external formal-library text: {needle}")
        if TOKEN_RE.search(text):
            failures.append(f"{path}: token-like secret detected")
        lowered = text.lower()
        for phrase in ["public_ready true", "upload_allowed true", "release_ready true"]:
            if phrase in lowered:
                failures.append(f"{path}: forbidden true guardrail phrase {phrase}")
    return failures


def _has_any(payload: dict[str, Any], keys: set[str]) -> bool:
    return any(key in payload for key in keys)


def validate_record(row: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    rid = str(row.get("record_id", "<missing>"))
    missing = sorted(REQUIRED_FIELDS - set(row))
    if missing:
        failures.append(f"{rid}: missing required fields {missing}")
    for key in FALSE_FIELDS:
        if row.get(key) is not False:
            failures.append(f"{rid}: {key} must be false")
    if row.get("status") != "DRAFT_INTERNAL":
        failures.append(f"{rid}: status must be DRAFT_INTERNAL")
    text = json.dumps(row, sort_keys=True).lower()
    for phrase in BLOCKED_PHRASES:
        if phrase in text and "not_claimed" not in phrase:
            # The records may say "not public proof claim"; they must not assert
            # one. The stronger blocked phrases above should not appear as claims.
            if not text.count("not " + phrase):
                failures.append(f"{rid}: blocked claim phrase present: {phrase}")
    payload = row.get("certificate_payload")
    if not isinstance(payload, dict) or not payload:
        failures.append(f"{rid}: certificate_payload must be a non-empty object")
        payload = {}
    limitations = row.get("limitations")
    if not isinstance(limitations, list) or not limitations:
        failures.append(f"{rid}: limitations must be non-empty")
    fclass = row.get("function_class")
    if fclass == "D_FINITE_CERTIFICATE":
        if not _has_any(payload, {"ode", "polynomial_coefficients"}):
            failures.append(f"{rid}: D-finite record needs ODE or coefficient payload")
    elif fclass == "ANALYTIC_LOCAL_SERIES":
        if not _has_any(payload, {"series_kind", "coefficients"}):
            failures.append(f"{rid}: analytic record needs local series/coefficient payload")
    elif fclass == "SMOOTH_FINITE_JET":
        if not _has_any(payload, {"jet_kind", "derivative_payload", "boundary_checks"}):
            failures.append(f"{rid}: smooth record needs derivative/jet/boundary payload")
    elif fclass == "CONTINUITY_EPSILON_DELTA":
        if not _has_any(payload, {"continuity_payload", "modulus"}):
            failures.append(f"{rid}: continuous record needs epsilon-delta/modulus payload")
    elif fclass in BOUNDARY_CLASSES:
        if payload.get("non_overclaim") is not True:
            failures.append(f"{rid}: boundary record needs non_overclaim relation")
    else:
        failures.append(f"{rid}: unknown function_class {fclass}")
    return failures


def build_result(root: Path) -> dict[str, Any]:
    records, failures = collect_records(root)
    category_counts = Counter(str(row.get("function_class")) for row in records)
    for row in records:
        failures.extend(validate_record(row))
    for category, minimum in MIN_COUNTS.items():
        if category_counts.get(category, 0) < minimum:
            failures.append(f"{category}: count below {minimum}")
    boundary_count = sum(category_counts.get(name, 0) for name in BOUNDARY_CLASSES)
    if boundary_count < 3:
        failures.append("boundary/non-example count below 3")
    if len(records) < 20:
        failures.append("record_count below 20")
    failures.extend(text_scan(root))
    failures = sorted(set(failures))
    category_counts["BOUNDARY_OR_NON_EXAMPLE"] = boundary_count
    status = "PASS" if not failures else "FAIL"
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "record_count": len(records),
        "category_counts": dict(sorted(category_counts.items())),
        "json_parse_status": "PASS" if not any("JSON parse failed" in f for f in failures) else "FAIL",
        "required_field_status": "PASS" if not any("missing required fields" in f for f in failures) else "FAIL",
        "required_false_boolean_status": "PASS" if not any("must be false" in f for f in failures) else "FAIL",
        "zero_mathlib_status": "PASS" if not any("external formal-library" in f for f in failures) else "FAIL",
        "guardrail_status": status,
        "function_class_status": "DRAFT_INTERNAL_VALIDATED" if not failures else "FAIL",
        "warnings": [],
        "failures": failures,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    result = build_result(args.root)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(
        "FUNCTION_CLASS_VALIDATION",
        result["record_count"],
        result["function_class_status"],
        result["zero_mathlib_status"],
    )
    if args.strict and result["failures"]:
        for failure in result["failures"]:
            print(f"FAIL\t{failure}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
