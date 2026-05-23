"""Claim and guardrail policy checks for CapCard Lab cards."""

from __future__ import annotations

import json
import re
from typing import Any

from .schema import FALSE_ACTION_FIELDS, FORBIDDEN_POSITIVE, NOT_CLAIMED, ValidationResult

TOKEN_PATTERN = re.compile(r"pypi-[A-Za-z0-9]{20,}|hf_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,}")


def blob(value: Any) -> str:
    return json.dumps(value, sort_keys=True) if not isinstance(value, str) else value


def is_negative_boundary(text: str, phrase: str) -> bool:
    lower = text.lower()
    phrase = phrase.lower()
    return f"not {phrase}" in lower or f"no {phrase}" in lower or f"false {phrase}" in lower


def validate_claims(card: dict[str, Any], *, fixture_only: bool = False) -> ValidationResult:
    reasons: list[str] = []
    text = blob(card)
    lower = text.lower()
    positive_surface = " ".join(
        str(card.get(key, ""))
        for key in ["copy", "marketplace_copy", "summary", "description", "display_name", "title"]
    )
    if TOKEN_PATTERN.search(text) and not fixture_only:
        reasons.append("token-like secret present")
    for field in FALSE_ACTION_FIELDS:
        if card.get(field) is not False:
            reasons.append(f"{field} must be false")
    if card.get("safe_to_publish_publicly") is True and not fixture_only:
        reasons.append("safe_to_publish_publicly must remain false")
    for phrase in FORBIDDEN_POSITIVE:
        if phrase.lower() in positive_surface.lower() and not is_negative_boundary(positive_surface, phrase):
            if not fixture_only:
                reasons.append(f"forbidden positive claim: {phrase}")
        elif phrase.lower() in lower and not is_negative_boundary(lower, phrase):
            if not fixture_only:
                reasons.append(f"forbidden positive claim: {phrase}")
    boundary_text = " ".join(str(item) for item in card.get("not_claimed", []) + card.get("limitations", [])).lower()
    for phrase in NOT_CLAIMED:
        if phrase.lower() not in boundary_text and card.get("readiness_band") not in {"SUPPORT_ONLY_NO_HARDWARE", "FUTURE_ONLY"}:
            reasons.append(f"missing boundary: {phrase}")
    return ValidationResult("PASS" if not reasons else "FAIL", reasons)
