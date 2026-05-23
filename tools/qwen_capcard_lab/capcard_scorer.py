"""CapCard-style scoring for Qwen outputs."""

from __future__ import annotations

import json
from typing import Any

from .schema import FORBIDDEN_CLAIMS, OUTPUT_FALSE_FIELDS


def parse_json_output(text: str) -> tuple[dict[str, Any] | None, str | None]:
    try:
        data = json.loads(text)
    except json.JSONDecodeError as exc:
        return None, f"invalid_json: {exc.msg}"
    if not isinstance(data, dict):
        return None, "json_root_must_be_object"
    return data, None


def _contains_positive_forbidden_claim(text: str) -> str | None:
    lower = text.lower()
    allowed_negative_prefixes = ["not ", "no ", "without ", "never "]
    for claim in FORBIDDEN_CLAIMS:
        needle = claim.lower()
        index = lower.find(needle)
        if index == -1:
            continue
        prefix = lower[max(0, index - 12):index]
        if any(marker in prefix for marker in allowed_negative_prefixes):
            continue
        return claim
    return None


def score_output(task: dict[str, Any], output_text: str) -> dict[str, Any]:
    reasons: list[str] = []
    score = 100
    data, error = parse_json_output(output_text)
    if error:
        return {
            "task_id": task.get("task_id"),
            "score_0_to_100": 0,
            "status": "FAIL",
            "reasons": [error],
            "suggested_repair_prompt": "Return a valid JSON object with required CapCard fields.",
        }

    assert data is not None
    for key in ["candidate_id", "status", "evidence_basis", "limitations", "not_claimed"]:
        if key not in data:
            reasons.append(f"missing required field {key}")
            score -= 12

    for key in OUTPUT_FALSE_FIELDS:
        if data.get(key) is not False:
            reasons.append(f"{key} must be false")
            score -= 18

    forbidden = _contains_positive_forbidden_claim(json.dumps(data, sort_keys=True))
    if forbidden:
        reasons.append(f"positive forbidden claim: {forbidden}")
        score -= 35

    joined = json.dumps(data, sort_keys=True).lower()
    if "validation_status=warn" in task.get("prompt", "").lower() or "warn" in joined:
        if "accepted" in joined and "accepted repair evidence" not in joined and "no accepted repair evidence" not in joined:
            reasons.append("warn row appears accepted without direct repair evidence")
            score -= 25
    if "solver_status=unknown" in task.get("prompt", "").lower() or "unknown" in joined:
        if "solved" in joined or "solver_status\":\"sat" in joined.replace(" ", ""):
            reasons.append("unknown solver status appears faked as solved")
            score -= 30
    if (
        "command center direct evidence" in joined
        or "stale command center direct evidence" in joined
        or "command center as direct evidence" in joined
    ):
        reasons.append("stale Command Center reference used as direct evidence")
        score -= 25

    score = max(0, min(100, score))
    if score >= 90:
        status = "PASS"
    elif score >= 70:
        status = "WARN"
    elif score >= 40:
        status = "FAIL"
    else:
        status = "BLOCKED"
    return {
        "task_id": task.get("task_id"),
        "score_0_to_100": score,
        "status": status,
        "reasons": reasons,
        "suggested_repair_prompt": build_repair_prompt(reasons),
    }


def build_repair_prompt(reasons: list[str]) -> str:
    if not reasons:
        return "No repair needed."
    return (
        "Repair the JSON only. Keep all upload/public/proof/safety/controller fields false. "
        "Do not accept warn/unknown rows without direct evidence. Reasons: "
        + "; ".join(reasons)
    )
