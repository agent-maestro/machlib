"""Routing policy for supervised local Qwen CapCard calls."""

from __future__ import annotations

from .model_registry import ModelRuntime


def runtime_allowed(runtime: ModelRuntime, *, min_schema_rate: float = 0.8) -> bool:
    if not runtime.available or not runtime.startup_success:
        return False
    if runtime.no_go_violation_count > 0:
        return False
    if runtime.schema_json_rate < min_schema_rate:
        return False
    return True


def select_runtime(task: dict, registry: list[ModelRuntime]) -> ModelRuntime:
    allowed = [row for row in registry if runtime_allowed(row)]
    if not allowed:
        fallback = [row for row in registry if row.available and row.startup_success]
        if not fallback:
            raise RuntimeError("no available local Qwen runtime")
        preferred_fallback = [
            row
            for row in fallback
            if row.model == "qwen3:30b" and row.runtime_mode == "api_schema_format_think_false"
        ]
        if preferred_fallback:
            return preferred_fallback[0]
        return max(fallback, key=lambda row: (row.average_score, row.schema_json_rate, -row.median_latency))

    family = task.get("family", "")
    coder_families = {"model_self_correction", "source_traceability"}
    coder = [
        row
        for row in allowed
        if row.model == "qwen3-coder:30b"
        and row.runtime_mode.startswith("api_schema")
        and row.average_score >= 90
        and family in coder_families
    ]
    if coder:
        return max(coder, key=lambda row: (row.average_score, row.schema_json_rate, -row.median_latency))

    preferred = [
        row
        for row in allowed
        if row.model == "qwen3:30b" and row.runtime_mode == "api_schema_format_think_false"
    ]
    if preferred:
        return preferred[0]
    return max(allowed, key=lambda row: (row.average_score, row.schema_json_rate, -row.median_latency))


def should_block_runtime(history: list[dict], *, threshold: int = 2) -> bool:
    bad = 0
    for row in history:
        reasons = row.get("score", {}).get("reasons", [])
        if any("forbidden" in reason or "must_be_false" in reason for reason in reasons):
            bad += 1
    return bad >= threshold
