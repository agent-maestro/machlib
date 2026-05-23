"""Robust JSON extraction for local Qwen output."""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from typing import Any


TOKEN_PATTERNS = [
    re.compile(r"pypi-[A-Za-z0-9]{20,}"),
    re.compile(r"hf_[A-Za-z0-9]{20,}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
]

FORBIDDEN_TRUE_FIELDS = [
    "public_ready",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "production_marketplace_modified",
    "marketplace_upload_performed",
    "public_claim",
    "theorem_proof_claim",
    "open_problem_claim",
    "certified_safety_claim",
    "production_controller_claim",
]

REQUIRED_CAPCARD_FIELDS = [
    "candidate_id",
    "status",
    "evidence_basis",
    "limitations",
    "not_claimed",
]


@dataclass(frozen=True)
class ExtractionResult:
    extraction_status: str
    extracted_json: dict[str, Any] | None
    diagnostics: list[str]
    candidate_count: int = 0

    def to_dict(self) -> dict[str, Any]:
        return {
            "extraction_status": self.extraction_status,
            "extracted_json": self.extracted_json,
            "diagnostics": self.diagnostics,
            "candidate_count": self.candidate_count,
        }


def has_token_like_secret(text: str) -> bool:
    return any(pattern.search(text) for pattern in TOKEN_PATTERNS)


def _strip_fences(text: str) -> list[str]:
    matches = re.findall(r"```(?:json)?\s*(\{.*?\})\s*```", text, flags=re.DOTALL | re.IGNORECASE)
    return matches


def _balanced_object_candidates(text: str) -> list[str]:
    candidates: list[str] = []
    starts = [idx for idx, char in enumerate(text) if char == "{"]
    for start in starts:
        depth = 0
        in_string = False
        escaped = False
        for idx in range(start, len(text)):
            char = text[idx]
            if in_string:
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
                continue
            if char == '"':
                in_string = True
            elif char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    candidates.append(text[start : idx + 1])
                    break
    return candidates


def _is_safe_object(data: dict[str, Any], required_fields: list[str] | None) -> list[str]:
    diagnostics: list[str] = []
    if has_token_like_secret(json.dumps(data, sort_keys=True)):
        diagnostics.append("token_like_secret_detected")
    for key in FORBIDDEN_TRUE_FIELDS:
        if data.get(key) is True:
            diagnostics.append(f"forbidden_true_field:{key}")
    for key in required_fields or []:
        if key not in data:
            diagnostics.append(f"missing_required_field:{key}")
    return diagnostics


def extract_json_object(raw_output: str, required_fields: list[str] | None = None) -> ExtractionResult:
    if not raw_output.strip():
        return ExtractionResult("JSON_MISSING", None, ["empty_output"])
    if has_token_like_secret(raw_output):
        return ExtractionResult("JSON_INVALID", None, ["token_like_secret_detected"], 0)

    candidates = []
    stripped = raw_output.strip()
    try:
        data = json.loads(stripped)
        if isinstance(data, dict):
            diagnostics = _is_safe_object(data, required_fields)
            if diagnostics:
                return ExtractionResult("JSON_INVALID", None, diagnostics, 1)
            return ExtractionResult("EXACT_JSON", data, [], 1)
    except json.JSONDecodeError:
        pass

    candidates.extend(_strip_fences(raw_output))
    candidates.extend(_balanced_object_candidates(raw_output))
    seen: set[str] = set()
    unique = []
    for candidate in candidates:
        if candidate not in seen:
            seen.add(candidate)
            unique.append(candidate)

    invalid_reasons: list[str] = []
    for candidate in unique:
        try:
            data = json.loads(candidate)
        except json.JSONDecodeError as exc:
            invalid_reasons.append(f"candidate_invalid_json:{exc.msg}")
            continue
        if not isinstance(data, dict):
            invalid_reasons.append("candidate_root_not_object")
            continue
        diagnostics = _is_safe_object(data, required_fields)
        if diagnostics:
            invalid_reasons.extend(diagnostics)
            continue
        return ExtractionResult("JSON_EXTRACTED_FROM_THINKING_TEXT", data, [], len(unique))

    if unique:
        return ExtractionResult("JSON_INVALID", None, invalid_reasons or ["no_safe_json_candidate"], len(unique))
    return ExtractionResult("JSON_MISSING", None, ["no_json_object_found"], 0)
