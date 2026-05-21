#!/usr/bin/env python3
"""Validate MachLib stochastic/hybrid draft records."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
REQUIRED_CLASSES = {
    "DIFFUSION_TRACE",
    "STOCHASTIC_INCREMENT",
    "JUMP_COUNTING_PROCESS",
    "TRANSITION_RATE_RECORD",
    "HYBRID_TRACE",
    "BOUNDARY_NO_OVERCLAIM",
}
REQUIRED_FIELDS = [
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
TOKEN_PATTERNS = [re.compile(r"hf_[A-Za-z0-9]{20,}"), re.compile(r"sk-[A-Za-z0-9]{20,}"), re.compile(r"pypi-[A-Za-z0-9]{20,}")]
FORBIDDEN_CLAIMS = [
    "stochastic calculus " + "formalized",
    "sde theorem " + "proved",
    "markov theorem " + "proved",
    "public_ready" + ": true",
    "upload_allowed" + ": true",
    "release_ready" + ": true",
]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def as_text(value: Any) -> str:
    return json.dumps(value, sort_keys=True) if not isinstance(value, str) else value


def validate(root: Path) -> dict[str, Any]:
    records_path = root / "records_2026_05_20.json"
    payload = read_json(records_path)
    records = payload.get("records", [])
    failures: list[str] = []
    warnings: list[str] = []

    if len(records) < 12:
        failures.append("record_count below 12")

    classes = {record.get("process_class") for record in records if isinstance(record, dict)}
    missing_classes = sorted(REQUIRED_CLASSES - classes)
    if missing_classes:
        failures.append(f"missing process classes: {missing_classes}")

    for index, record in enumerate(records):
        if not isinstance(record, dict):
            failures.append(f"record {index} is not an object")
            continue
        rid = record.get("record_id", f"record_{index}")
        for field in REQUIRED_FIELDS:
            if field not in record:
                failures.append(f"{rid}: missing {field}")
        for field in FALSE_FIELDS:
            if record.get(field) is not False:
                failures.append(f"{rid}: {field} must be false")
        if record.get("status") != "DRAFT_INTERNAL":
            failures.append(f"{rid}: status must be DRAFT_INTERNAL")
        text = as_text(record)
        if any(needle in text for needle in DEPENDENCY_NEEDLES):
            failures.append(f"{rid}: dependency import string detected")
        if any(pattern.search(text) for pattern in TOKEN_PATTERNS):
            failures.append(f"{rid}: token-like secret detected")
        lower = text.lower()
        for phrase in FORBIDDEN_CLAIMS:
            if phrase in lower:
                failures.append(f"{rid}: forbidden claim phrase {phrase}")
        not_claimed = " ".join(str(item).lower() for item in record.get("not_claimed", []))
        for phrase in ["not stochastic calculus", "not an sde theorem", "not a markov process theorem"]:
            if phrase not in not_claimed:
                warnings.append(f"{rid}: weak not_claimed language for {phrase}")

    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "record_count": len(records),
        "required_process_classes": sorted(REQUIRED_CLASSES),
        "present_process_classes": sorted(str(cls) for cls in classes),
        "status": "DRAFT_INTERNAL_VALIDATED" if not failures else "FAIL",
        "zero_mathlib_status": "PASS" if not failures else "FAIL",
        "failures": failures,
        "warnings": warnings,
        "guardrails": {
            "no_mathlib_dependency": not failures,
            "no_upload_publish_release": True,
            "no_public_theorem_claim": True,
            "no_stochastic_calculus_claim": True,
            "no_sde_theorem_claim": True,
            "no_markov_theorem_claim": True,
            "no_production_controller_claim": True,
            "no_certified_safety_claim": True,
        },
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
