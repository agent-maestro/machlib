#!/usr/bin/env python3
"""Validate MachLib stochastic/hybrid draft records."""

from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
REQUIRED_CLASSES = {
    "DIFFUSION_TRACE",
    "STOCHASTIC_INCREMENT",
    "DRIFT_DIFFUSION_SIGNATURE",
    "NOISE_PLACEHOLDER",
    "JUMP_COUNTING_PROCESS",
    "TRANSITION_RATE_RECORD",
    "DISCRETE_STATE_TRACE",
    "HYBRID_TRACE",
    "TRANSITION_COUNT_MATRIX",
    "BOUNDARY_NO_OVERCLAIM",
    "PRODUCTION_CONTROL_NO_GO",
}
REQUIRED_FIELDS = [
    "schema_version",
    "record_id",
    "process_class",
    "title",
    "expression_or_trace",
    "certificate_type",
    "certificate_payload",
    "validation_checks",
    "limitations",
    "not_claimed",
    "status",
]
FALSE_FIELDS = [
    "public_ready",
    "upload_allowed",
    "release_ready",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]
DEPENDENCY_NEEDLES = ["import " + "Mathlib", "from " + "Mathlib", "Mathlib" + "."]
TOKEN_PATTERNS = [
    re.compile(r"hf_[A-Za-z0-9]{20,}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
    re.compile(r"pypi-[A-Za-z0-9]{20,}"),
]
REQUIRED_NOT_CLAIMED = [
    "not stochastic calculus formalization",
    "not an sde theorem",
    "not a markov theorem",
    "not production controller evidence",
    "not certified safety",
    "not hardware truth",
    "not public-ready",
    "not upload-ready",
    "not release-ready",
]
FORBIDDEN_POSITIVE_CLAIMS = [
    "stochastic calculus " + "formalized",
    "sde theorem " + "proved",
    "markov theorem " + "proved",
    "public theorem/proof/open-problem result achieved",
    "public_ready" + ": true",
    "upload_allowed" + ": true",
    "release_ready" + ": true",
    "marketplace_ready" + ": true",
    "production_ready" + ": true",
]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def as_text(value: Any) -> str:
    return value if isinstance(value, str) else json.dumps(value, sort_keys=True)


def validate(root: Path) -> dict[str, Any]:
    failures: list[str] = []
    warnings: list[str] = []
    records: list[dict[str, Any]] = []
    json_parse_status = "PASS"
    try:
        records = read_json(root / "records_2026_05_20.json").get("records", [])
    except Exception as exc:  # noqa: BLE001 - report exact parse issue.
        failures.append(f"JSON parse failed: {exc}")
        json_parse_status = "FAIL"

    required_field_failures: list[str] = []
    false_boolean_failures: list[str] = []
    guardrail_failures: list[str] = []

    if len(records) < 12:
        failures.append("record_count below 12")

    class_counts = Counter(str(record.get("process_class")) for record in records if isinstance(record, dict))
    missing = sorted(REQUIRED_CLASSES - set(class_counts))
    if missing:
        failures.append(f"missing process classes: {missing}")

    for idx, record in enumerate(records):
        rid = record.get("record_id", f"record_{idx}") if isinstance(record, dict) else f"record_{idx}"
        if not isinstance(record, dict):
            required_field_failures.append(f"{rid}: record is not object")
            continue
        for field in REQUIRED_FIELDS:
            if field not in record:
                required_field_failures.append(f"{rid}: missing {field}")
        if record.get("schema_version") != "1.0.0":
            required_field_failures.append(f"{rid}: schema_version must be 1.0.0")
        for field in FALSE_FIELDS:
            if record.get(field) is not False:
                false_boolean_failures.append(f"{rid}: {field} must be false")
        if record.get("status") != "DRAFT_INTERNAL":
            guardrail_failures.append(f"{rid}: status must be DRAFT_INTERNAL")

        text = as_text(record)
        lower = text.lower()
        if any(needle in text for needle in DEPENDENCY_NEEDLES):
            guardrail_failures.append(f"{rid}: Mathlib import/dependency string detected")
        if any(pattern.search(text) for pattern in TOKEN_PATTERNS):
            guardrail_failures.append(f"{rid}: token-like secret detected")
        for phrase in FORBIDDEN_POSITIVE_CLAIMS:
            if phrase in lower:
                guardrail_failures.append(f"{rid}: forbidden positive claim phrase {phrase}")
        not_claimed = " ".join(str(item).lower() for item in record.get("not_claimed", []))
        for phrase in REQUIRED_NOT_CLAIMED:
            if phrase not in not_claimed:
                guardrail_failures.append(f"{rid}: missing not_claimed phrase {phrase}")

    failures.extend(required_field_failures)
    failures.extend(false_boolean_failures)
    failures.extend(guardrail_failures)

    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "record_count": len(records),
        "present_process_classes": sorted(class_counts),
        "process_class_counts": dict(sorted(class_counts.items())),
        "json_parse_status": json_parse_status,
        "required_field_status": "PASS" if not required_field_failures else "FAIL",
        "required_false_boolean_status": "PASS" if not false_boolean_failures else "FAIL",
        "zero_mathlib_status": "PASS" if not failures else "FAIL",
        "guardrail_status": "PASS" if not guardrail_failures else "FAIL",
        "status": "DRAFT_INTERNAL_VALIDATED" if not failures else "FAIL",
        "warnings": warnings,
        "failures": failures,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    result = validate(args.root)
    write_json(args.out, result)
    print("STOCHASTIC_HYBRID_VALIDATION", result["record_count"], result["status"], result["zero_mathlib_status"])
    if args.strict and result["failures"]:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
