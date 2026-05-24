"""Retry policy for Qwen CapCard supervised calls."""

from __future__ import annotations


REPAIRABLE_NEEDLES = [
    "JSON_INVALID",
    "JSON_MISSING",
    "missing",
    "stale Command Center",
    "unknown solver",
    "warn row",
    "false acceptance",
]

STOP_NEEDLES = [
    "token_like_secret",
    "petal_api_upload_performed_must_be_false",
    "huggingface_upload_performed_must_be_false",
    "certified_safety_claim_must_be_false",
    "theorem_proof_claim_must_be_false",
    "production_controller_claim_must_be_false",
    "forbidden_true_field",
]


def should_retry(score: dict, attempt_index: int, *, max_attempts: int = 3) -> bool:
    if attempt_index + 1 >= max_attempts:
        return False
    if score.get("status") == "PASS":
        return False
    reasons = " ".join(score.get("reasons", []))
    if any(needle in reasons for needle in STOP_NEEDLES):
        return False
    return any(needle in reasons for needle in REPAIRABLE_NEEDLES) or score.get("score_0_to_100", 0) < 90


def repair_instruction(score: dict) -> str:
    reasons = "; ".join(score.get("reasons", [])) or "score below pass threshold"
    return (
        "Repair the previous answer. Return schema JSON only. Keep all public/upload/proof/"
        "safety/controller fields false. Do not invent missing evidence. Reasons: "
        + reasons
    )
