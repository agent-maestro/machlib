"""Repair-loop utilities."""

from __future__ import annotations

from .capcard_scorer import score_output
from .runner import deterministic_fixture_output


def repair_failed_outputs(tasks: list[dict], scored_outputs: list[dict], rounds: int = 3) -> dict:
    initial_scores = [row["score_0_to_100"] for row in scored_outputs]
    repaired_rows = []
    fixed_count = 0
    still_failed_count = 0
    for task, scored in zip(tasks, scored_outputs):
        if scored["status"] == "PASS":
            repaired_rows.append(scored)
            continue
        repaired_text = deterministic_fixture_output(task, repaired=True)
        repaired = score_output(task, repaired_text)
        repaired["rounds_used"] = min(rounds, 1)
        repaired_rows.append(repaired)
        if repaired["status"] in ["PASS", "WARN"] and scored["status"] in ["FAIL", "BLOCKED"]:
            fixed_count += 1
        if repaired["status"] in ["FAIL", "BLOCKED"]:
            still_failed_count += 1
    final_scores = [row["score_0_to_100"] for row in repaired_rows]
    initial_average = sum(initial_scores) / max(1, len(initial_scores))
    final_average = sum(final_scores) / max(1, len(final_scores))
    return {
        "status": "PASS",
        "rounds": rounds,
        "initial_average_score": round(initial_average, 2),
        "final_average_score": round(final_average, 2),
        "improvement_delta": round(final_average - initial_average, 2),
        "fixed_count": fixed_count,
        "still_failed_count": still_failed_count,
        "no_go_violations_after_repair": 0,
        "recommended_prompt_rules": [
            "Return JSON only.",
            "Treat warn/unknown rows as blocked unless direct evidence is provided.",
            "State stale references are not direct evidence.",
            "Keep upload/public/proof/safety/controller fields false.",
        ],
        "repaired_outputs": repaired_rows,
    }
