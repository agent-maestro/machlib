"""Teacher memory for reusable Qwen CapCard repair rules."""

from __future__ import annotations

from collections import Counter
from typing import Any


def failure_pattern(score: dict) -> str:
    reasons = score.get("reasons", [])
    if not reasons:
        return "low_score_without_specific_reason"
    if any("JSON" in reason for reason in reasons):
        return "json_or_schema_failure"
    if any("unknown solver" in reason for reason in reasons):
        return "unknown_solver_fake_solved"
    if any("stale Command Center" in reason for reason in reasons):
        return "stale_reference_misuse"
    if any("forbidden" in reason or "must_be_false" in reason for reason in reasons):
        return "forbidden_or_true_boundary_field"
    return reasons[0].replace(" ", "_")[:80]


def memory_entry(task: dict, model: str, runtime_mode: str, score: dict) -> dict[str, Any]:
    pattern = failure_pattern(score)
    return {
        "failure_pattern": pattern,
        "scorer_reason": score.get("reasons", []),
        "repair_instruction": score.get("suggested_repair_prompt", "Return schema JSON only."),
        "corrected_schema_target": "CapCard structured task result with all public/upload/proof/safety/controller fields false",
        "task_family": task.get("family"),
        "model": model,
        "runtime_mode": runtime_mode,
        "reuse_priority": 5 if pattern != "low_score_without_specific_reason" else 2,
        "examples_sanitized": True,
    }


def build_teacher_memory(results: list[dict]) -> dict[str, Any]:
    entries = []
    for row in results:
        final = row.get("final_score", {})
        if final.get("status") != "PASS":
            entries.append(memory_entry(row.get("task", {}), row.get("model", ""), row.get("runtime_mode", ""), final))
    counts = Counter(entry["failure_pattern"] for entry in entries)
    return {
        "memory_id": "qwen_capcard_teacher_memory_v4_2026_05_23",
        "status": "DRAFT_INTERNAL",
        "entry_count": len(entries),
        "top_failure_patterns": counts.most_common(10),
        "entries": entries[:100],
        "public_ready": False,
        "fine_tune_performed": False,
        "huggingface_upload_performed": False,
        "petal_api_upload_performed": False,
    }
