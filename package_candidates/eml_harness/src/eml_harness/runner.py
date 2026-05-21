from __future__ import annotations

from .schema import validate_result


def summarize_results(results: list[dict[str, object]]) -> dict[str, int]:
    summary = {"total": len(results), "pass": 0, "fail": 0, "skip": 0, "invalid": 0}
    for result in results:
        if validate_result(result):
            summary["invalid"] += 1
            continue
        status = str(result["status"]).lower()
        summary[status] += 1
    return summary
