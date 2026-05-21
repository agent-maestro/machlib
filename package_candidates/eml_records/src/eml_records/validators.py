"""Validation helpers for local draft EML-style records."""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable

from .loaders import load_records
from .schema import (
    DEFAULT_NOT_CLAIMED_CONCEPTS,
    FAMILY_UNKNOWN,
    STOCHASTIC_NOT_CLAIMED_CONCEPTS,
    detect_family,
    false_boolean_failures,
    missing_not_claimed_concepts,
    missing_required_fields,
    status_is_allowed,
)


@dataclass
class ValidationResult:
    valid: bool
    record_id: str | None = None
    family: str | None = None
    record_count: int = 0
    valid_count: int = 0
    warning_count: int = 0
    failure_count: int = 0
    family_counts: dict[str, int] = field(default_factory=dict)
    warnings: list[str] = field(default_factory=list)
    failures: list[str] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        return {
            "valid": self.valid,
            "record_id": self.record_id,
            "family": self.family,
            "record_count": self.record_count,
            "valid_count": self.valid_count,
            "warning_count": self.warning_count,
            "failure_count": self.failure_count,
            "family_counts": self.family_counts,
            "warnings": self.warnings,
            "failures": self.failures,
        }


def _as_record(row: dict[str, Any]) -> dict[str, Any]:
    draft = row.get("draft_eml_seed")
    if isinstance(draft, dict):
        merged = dict(draft)
        theorem = row.get("theorem")
        if isinstance(theorem, dict):
            merged.setdefault("record_id", theorem.get("id"))
            merged.setdefault("lane", theorem.get("lane"))
        return merged
    return row


def _text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    return json.dumps(value, sort_keys=True)


def _not_claimed_text(record: dict[str, Any]) -> str:
    return " ".join(
        [
            _text(record.get("not_claimed")),
            _text(record.get("limitations")),
            _text(record.get("constraints")),
        ]
    ).lower()


def _has_positive_phrase(text: str, phrase: str) -> bool:
    start = 0
    while True:
        idx = text.find(phrase, start)
        if idx == -1:
            return False
        prefix = text[max(0, idx - 16) : idx]
        if "not " not in prefix and "no " not in prefix:
            return True
        start = idx + len(phrase)


def classify_family(record: dict[str, Any]) -> str:
    row = _as_record(record)
    return detect_family(row if row is record else {"draft_eml_seed": row})


def _validate_generic(
    record: dict[str, Any],
    failures: list[str],
    warnings: list[str],
    strict: bool,
) -> None:
    rid = str(record.get("record_id", "<missing>"))
    missing = missing_required_fields(record)
    if missing:
        failures.append(f"{rid}: missing required fields {missing}")
    for field_name in false_boolean_failures(record):
        failures.append(f"{rid}: {field_name} must be false")
    status = record.get("status")
    if not status_is_allowed(status):
        message = f"{rid}: status {status!r} is not allowed"
        if strict:
            failures.append(message)
        else:
            warnings.append(message)
    if not isinstance(record.get("limitations"), list) or not record.get("limitations"):
        failures.append(f"{rid}: limitations must be a non-empty list")
    if not isinstance(record.get("not_claimed"), list) or not record.get("not_claimed"):
        failures.append(f"{rid}: not_claimed must be a non-empty list")

    text = _not_claimed_text(record)
    for concept in missing_not_claimed_concepts(text, DEFAULT_NOT_CLAIMED_CONCEPTS):
        message = f"{rid}: missing not_claimed concept {concept}"
        if strict:
            failures.append(message)
        else:
            warnings.append(message)

    lowered = _text(record).lower()
    positive_claims = [
        "theorem proved",
        "open problem solved",
        "certified safety",
        "production controller",
        "public_ready: true",
        "upload_allowed: true",
        "release_ready: true",
    ]
    for phrase in positive_claims:
        if _has_positive_phrase(lowered, phrase):
            failures.append(f"{rid}: forbidden positive claim phrase {phrase}")
    if "import mathlib" in lowered or "from mathlib" in lowered or "mathlib." in lowered:
        failures.append(f"{rid}: Mathlib dependency evidence detected")

    if classify_family(record) == FAMILY_UNKNOWN:
        warnings.append(f"{rid}: record family is UNKNOWN")


def _validate_function_class(record: dict[str, Any], failures: list[str]) -> None:
    rid = str(record.get("record_id", "<missing>"))
    if not record.get("function_class"):
        failures.append(f"{rid}: function_class is required")
    if "certificate_type" not in record and "certificate_payload" not in record:
        failures.append(f"{rid}: function-class record needs certificate_type or certificate_payload")
    if not record.get("limitations"):
        failures.append(f"{rid}: function-class record needs limitations")


def _validate_stochastic_hybrid(record: dict[str, Any], failures: list[str]) -> None:
    rid = str(record.get("record_id", "<missing>"))
    for field_name in ("process_class", "certificate_type", "certificate_payload"):
        if field_name not in record:
            failures.append(f"{rid}: stochastic/hybrid record missing {field_name}")
    text = _not_claimed_text(record)
    for concept, alternatives in STOCHASTIC_NOT_CLAIMED_CONCEPTS.items():
        if concept in missing_not_claimed_concepts(text, {concept: alternatives}):
            failures.append(f"{rid}: missing stochastic boundary concept {concept}")


def _validate_lane_seed(record: dict[str, Any], failures: list[str]) -> None:
    rid = str(record.get("record_id") or record.get("task_id") or "<missing>")
    if not (record.get("record_id") or record.get("task_id")):
        failures.append(f"{rid}: lane seed needs record_id or task_id")
    if not (record.get("status") or record.get("draft_marker") or record.get("draft_internal")):
        failures.append(f"{rid}: lane seed needs status or draft/internal marker")


def validate_record(record: dict[str, Any], strict: bool = False) -> ValidationResult:
    row = _as_record(record)
    failures: list[str] = []
    warnings: list[str] = []
    _validate_generic(row, failures, warnings, strict)
    family = classify_family(record)
    if family == "FUNCTION_CLASS":
        _validate_function_class(row, failures)
    elif family == "STOCHASTIC_HYBRID":
        _validate_stochastic_hybrid(row, failures)
    elif family == "LANE_SEED":
        _validate_lane_seed(row, failures)

    return ValidationResult(
        valid=not failures,
        record_id=str(row.get("record_id", "<missing>")),
        family=family,
        record_count=1,
        valid_count=0 if failures else 1,
        warning_count=len(warnings),
        failure_count=len(failures),
        family_counts={family: 1},
        warnings=warnings,
        failures=failures,
    )


def _flatten_inputs(records: Iterable[Any]) -> list[dict[str, Any]]:
    flattened: list[dict[str, Any]] = []
    for row in records:
        if isinstance(row, dict):
            flattened.append(row)
        elif isinstance(row, list):
            flattened.extend(_flatten_inputs(row))
    return flattened


def validate_records(records: Iterable[dict[str, Any]], strict: bool = False) -> ValidationResult:
    failures: list[str] = []
    warnings: list[str] = []
    family_counts: Counter[str] = Counter()
    valid_count = 0
    count = 0
    for record in _flatten_inputs(records):
        count += 1
        result = validate_record(record, strict=strict)
        failures.extend(result.failures)
        warnings.extend(result.warnings)
        family_counts.update(result.family_counts)
        if result.valid:
            valid_count += 1
    return ValidationResult(
        valid=not failures,
        record_count=count,
        valid_count=valid_count,
        warning_count=len(warnings),
        failure_count=len(failures),
        family_counts=dict(sorted(family_counts.items())),
        warnings=warnings,
        failures=failures,
    )


def validate_file(path: Path, strict: bool = False) -> ValidationResult:
    records, load_failures, _ = load_records(path)
    result = validate_records(records, strict=strict)
    failures = [*load_failures, *result.failures]
    return ValidationResult(
        valid=not failures,
        record_count=result.record_count,
        valid_count=result.valid_count if not load_failures else 0,
        warning_count=result.warning_count,
        failure_count=len(failures),
        family_counts=result.family_counts,
        warnings=result.warnings,
        failures=failures,
    )


def validate_path(
    path: Path,
    family: str | None = None,
    strict: bool = False,
    include: tuple[str, ...] | None = None,
    exclude_dir: tuple[str, ...] | None = None,
) -> ValidationResult:
    records, load_failures, _ = load_records(path, include=include, exclude_dir=exclude_dir)
    result = validate_records(records, strict=strict)
    failures = [*load_failures, *result.failures]
    if family and result.family_counts.get(family, 0) == 0:
        failures.append(f"expected family {family} was not found")
    return ValidationResult(
        valid=not failures,
        record_count=result.record_count,
        valid_count=result.valid_count if not load_failures else 0,
        warning_count=result.warning_count,
        failure_count=len(failures),
        family_counts=result.family_counts,
        warnings=result.warnings,
        failures=failures,
    )
