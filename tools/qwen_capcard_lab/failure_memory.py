"""Failure memory records for future Qwen prompting."""

from __future__ import annotations


def build_failure_memory(scored_outputs: list[dict]) -> dict:
    patterns = []
    for row in scored_outputs:
        if row.get("status") == "PASS":
            continue
        for reason in row.get("reasons", []):
            patterns.append(
                {
                    "failure_pattern": reason,
                    "example_bad_output": row.get("task_id"),
                    "scorer_reason": reason,
                    "repair_instruction": row.get("suggested_repair_prompt", ""),
                    "corrected_shape": "JSON object with all guard fields false and direct evidence boundaries.",
                    "should_reuse_in_future": True,
                }
            )
    if not patterns:
        patterns.append(
            {
                "failure_pattern": "prevent_warn_unknown_overclaim",
                "example_bad_output": "fixture",
                "scorer_reason": "warn/unknown rows require direct evidence",
                "repair_instruction": "Keep blocked or ready_for_human_repair_review, never solved.",
                "corrected_shape": "bounded internal CapCard row",
                "should_reuse_in_future": True,
            }
        )
    return {"failure_memory": patterns}
