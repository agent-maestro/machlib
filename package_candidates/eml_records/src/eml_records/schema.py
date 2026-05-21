"""Schema constants for the local draft eml-records package."""

from __future__ import annotations

from enum import StrEnum


class RecordFamily(StrEnum):
    LANE_SEED = "LANE_SEED"
    FUNCTION_CLASS = "FUNCTION_CLASS"
    STOCHASTIC_HYBRID = "STOCHASTIC_HYBRID"
    EVIDENCE_RECORD = "EVIDENCE_RECORD"
    UNKNOWN = "UNKNOWN"


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
