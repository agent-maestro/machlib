"""Schema constants for the local draft eml-records package."""

from __future__ import annotations

from enum import StrEnum


class RecordFamily(StrEnum):
    LANE_SEED = "LANE_SEED"
    FUNCTION_CLASS = "FUNCTION_CLASS"
    STOCHASTIC_HYBRID = "STOCHASTIC_HYBRID"
    EVIDENCE_RECORD = "EVIDENCE_RECORD"
    UNKNOWN = "UNKNOWN"


FAMILY_LANE_SEED = RecordFamily.LANE_SEED.value
FAMILY_FUNCTION_CLASS = RecordFamily.FUNCTION_CLASS.value
FAMILY_STOCHASTIC_HYBRID = RecordFamily.STOCHASTIC_HYBRID.value
FAMILY_EVIDENCE_RECORD = RecordFamily.EVIDENCE_RECORD.value
FAMILY_UNKNOWN = RecordFamily.UNKNOWN.value


ALLOWED_STATUSES = {
    "DRAFT_INTERNAL",
    "DRAFT_INTERNAL_VALIDATED",
    "OBSERVATION",
    "NEEDS_REVIEW",
    "BLOCKED_NO_GO",
}

REQUIRED_GENERIC_FIELDS = {
    "record_id",
    "status",
    "public_ready",
    "upload_allowed",
    "release_ready",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
    "limitations",
    "not_claimed",
}

REQUIRED_FALSE_BOOLEANS = {
    "public_ready",
    "upload_allowed",
    "release_ready",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
}

DEFAULT_NOT_CLAIMED_CONCEPTS = {
    "not public-ready": ("not public-ready", "not public ready"),
    "not upload-ready": ("not upload-ready", "not upload ready"),
    "not release-ready": ("not release-ready", "not release ready"),
    "not a public theorem/proof/open-problem claim": (
        "not a public theorem/proof/open-problem claim",
        "no public theorem/proof/open-problem claim",
        "not a public theorem",
        "not a public proof",
        "not a public open-problem",
    ),
}

STOCHASTIC_NOT_CLAIMED_CONCEPTS = {
    "not stochastic calculus": ("not stochastic calculus", "no stochastic calculus"),
    "not SDE theorem": ("not an sde theorem", "no sde theorem", "not sde theorem"),
    "not Markov theorem": ("not a markov theorem", "no markov theorem", "not markov theorem"),
    "not production controller": (
        "not production controller",
        "not production controller evidence",
        "no production controller",
    ),
    "not certified safety": ("not certified safety", "no certified safety"),
}


def missing_required_fields(record: dict, required_fields: set[str] | None = None) -> list[str]:
    fields = required_fields or REQUIRED_GENERIC_FIELDS
    return sorted(fields - set(record))


def false_boolean_failures(record: dict, fields: set[str] | None = None) -> list[str]:
    checked = fields or REQUIRED_FALSE_BOOLEANS
    return sorted(field for field in checked if record.get(field) is not False)


def status_is_allowed(status: object) -> bool:
    return status in ALLOWED_STATUSES


def text_contains_concept(text: str, alternatives: tuple[str, ...]) -> bool:
    lowered = text.lower()
    return any(phrase.lower() in lowered for phrase in alternatives)


def missing_not_claimed_concepts(
    text: str,
    concepts: dict[str, tuple[str, ...]] | None = None,
) -> list[str]:
    checked = concepts or DEFAULT_NOT_CLAIMED_CONCEPTS
    return [
        concept
        for concept, alternatives in checked.items()
        if not text_contains_concept(text, alternatives)
    ]


def detect_family(record: dict) -> str:
    draft = record.get("draft_eml_seed")
    if isinstance(draft, dict):
        return FAMILY_LANE_SEED
    if "lane" in record:
        return FAMILY_LANE_SEED
    if "function_class" in record:
        return FAMILY_FUNCTION_CLASS
    if "process_class" in record:
        return FAMILY_STOCHASTIC_HYBRID
    if "evidence_type" in record or "validation_trace" in record:
        return FAMILY_EVIDENCE_RECORD
    return FAMILY_UNKNOWN
