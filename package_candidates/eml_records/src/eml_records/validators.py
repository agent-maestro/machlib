"""Validation helpers for local draft EML-style records."""

from __future__ import annotations

import json
from collections import Counter
from dataclasses import dataclass, field
from typing import Any, Iterable

from .schema import (
    ALLOWED_STATUSES,
    DEFAULT_NOT_CLAIMED_CONCEPTS,
    REQUIRED_FALSE_BOOLEANS,
    REQUIRED_GENERIC_FIELDS,
    STOCHASTIC_NOT_CLAIMED_CONCEPTS,
    RecordFamily,
)


@dataclass
class ValidationResult:
    valid: bool
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


def _contains_concept(text: str, alternatives: Iterable[str]) -> bool:
    return any(phrase.lower() in text for phrase in alternatives)


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
    if "lane" in row or "draft_eml_seed" in record:
        return RecordFamily.LANE_SEED.value
    if "function_class" in row:
        return RecordFamily.FUNCTION_CLASS.value
    if "process_class" in row:
        return RecordFamily.STOCHASTIC_HYBRID.value
    if "evidence_type" in row or "validation_trace" in row:
        return RecordFamily.EVIDENCE_RECORD.value
    return RecordFamily.UNKNOWN.value


def _validate_generic(record: dict[str, Any], failures: list[str], warnings: list[str]) -> None:
    rid = str(record.get("record_id", "<missing>"))
    missing = sorted(REQUIRED_GENERIC_FIELDS - set(record))
    if missing:
        failures.append(f"{rid}: missing required fields {missing}")
    for field_name in sorted(REQUIRED_FALSE_BOOLEANS):
        if record.get(field_name) is not False:
            failures.append(f"{rid}: {field_name} must be false")
    status = record.get("status")
    if status not in ALLOWED_STATUSES:
        failures.append(f"{rid}: status {status!r} is not allowed")
    if not isinstance(record.get("limitations"), list) or not record.get("limitations"):
        failures.append(f"{rid}: limitations must be a non-empty list")
    if not isinstance(record.get("not_claimed"), list) or not record.get("not_claimed"):
        failures.append(f"{rid}: not_claimed must be a non-empty list")

    text = _not_claimed_text(record)
    for concept, alternatives in DEFAULT_NOT_CLAIMED_CONCEPTS.items():
        if not _contains_concept(text, alternatives):
            failures.append(f"{rid}: missing not_claimed concept {concept}")

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

    if classify_family(record) == RecordFamily.UNKNOWN.value:
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
        if not _contains_concept(text, alternatives):
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
    _validate_generic(row, failures, warnings)
    family = classify_family(record)
    if family == RecordFamily.FUNCTION_CLASS.value:
        _validate_function_class(row, failures)
    elif family == RecordFamily.STOCHASTIC_HYBRID.value:
        _validate_stochastic_hybrid(row, failures)
    elif family == RecordFamily.LANE_SEED.value:
        _validate_lane_seed(row, failures)

    return ValidationResult(
        valid=not failures,
        record_count=1,
        valid_count=0 if failures else 1,
        warning_count=len(warnings),
        failure_count=len(failures),
        family_counts={family: 1},
        warnings=warnings,
        failures=failures,
    )


def validate_records(records: Iterable[dict[str, Any]], strict: bool = False) -> ValidationResult:
    failures: list[str] = []
    warnings: list[str] = []
    family_counts: Counter[str] = Counter()
    valid_count = 0
    count = 0
    for record in records:
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
