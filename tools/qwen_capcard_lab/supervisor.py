"""Reusable local Qwen CapCard supervisor."""

from __future__ import annotations

import json
import time
from pathlib import Path
from typing import Any

from .capcard_scorer import score_output
from .json_extract import REQUIRED_STRUCTURED_RESULT_FIELDS, validate_structured_result
from .local_model import STRUCTURED_REQUIRED_FIELDS, build_structured_prompt, call_ollama_json, call_ollama_structured_api
from .retry_policy import repair_instruction, should_retry
from .router import select_runtime


def structured_to_capcard(task: dict, data: dict) -> str:
    payload = {
        "candidate_id": data.get("task_id") or task.get("task_id"),
        "status": data.get("candidate_status", "BLOCKED_WITH_EXACT_FIX_LIST"),
        "evidence_basis": ["supervised schema output"] if data.get("evidence_present") else ["model reported missing direct evidence"],
        "limitations": list(data.get("missing_evidence", [])) + [data.get("explanation", "")],
        "not_claimed": [
            "not PETAL/API uploaded",
            "not Hugging Face uploaded",
            "not public-ready",
            "not a theorem proof",
            "not certified safety",
            "not production controller evidence",
        ],
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "public_claim": False,
        "theorem_proof_claim": False,
        "open_problem_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
    }
    return json.dumps(payload, sort_keys=True)


def score_structured(task: dict, call: dict) -> dict:
    data = call.get("extracted_json")
    if data is None:
        return {
            "task_id": task.get("task_id"),
            "score_0_to_100": 0,
            "status": "FAIL",
            "reasons": [call.get("extraction_status", "JSON_MISSING"), *call.get("extraction_diagnostics", [])],
            "suggested_repair_prompt": "Return valid schema JSON only.",
            "schema_valid": False,
        }
    diagnostics = validate_structured_result(data)
    if diagnostics:
        return {
            "task_id": task.get("task_id"),
            "score_0_to_100": 0,
            "status": "FAIL",
            "reasons": diagnostics,
            "suggested_repair_prompt": "Repair schema JSON and keep forbidden/action fields false.",
            "schema_valid": False,
        }
    scored = score_output(task, structured_to_capcard(task, data))
    scored["schema_valid"] = True
    return scored


def call_runtime(model: str, runtime_mode: str, prompt: str, timeout_seconds: int, task_id: str) -> dict:
    structured_prompt = build_structured_prompt(prompt, task_id=task_id)
    if runtime_mode == "api_schema_format_think_false":
        return call_ollama_structured_api(
            model,
            structured_prompt,
            timeout_seconds=timeout_seconds,
            required_fields=STRUCTURED_REQUIRED_FIELDS,
            think_false=True,
            use_schema=True,
        ).to_dict()
    if runtime_mode == "api_schema_format":
        return call_ollama_structured_api(
            model,
            structured_prompt,
            timeout_seconds=timeout_seconds,
            required_fields=STRUCTURED_REQUIRED_FIELDS,
            use_schema=True,
        ).to_dict()
    return call_ollama_json(
        model,
        structured_prompt,
        timeout_seconds=timeout_seconds,
        required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS,
        mode=runtime_mode,
    ).to_dict()


class QwenCapCardSupervisor:
    def __init__(self, registry: list, *, timeout_seconds: int = 30, max_attempts: int = 3):
        self.registry = registry
        self.timeout_seconds = timeout_seconds
        self.max_attempts = max_attempts

    def run_task(self, task: dict, out_dir: Path | None = None) -> dict[str, Any]:
        runtime = select_runtime(task, self.registry)
        prompt = task["prompt"]
        attempts = []
        start = time.monotonic()
        for attempt_index in range(self.max_attempts):
            call = call_runtime(runtime.model, runtime.runtime_mode, prompt, self.timeout_seconds, task["task_id"])
            scored = score_structured(task, call)
            attempts.append({"attempt_index": attempt_index, "call": call, "score": scored})
            if out_dir is not None:
                out_dir.mkdir(parents=True, exist_ok=True)
                (out_dir / f"{task['task_id']}_{attempt_index:02d}.json").write_text(
                    json.dumps({"task": task, "runtime": runtime.to_dict(), "call": call, "score": scored}, indent=2, sort_keys=True)
                    + "\n"
                )
            if not should_retry(scored, attempt_index, max_attempts=self.max_attempts):
                break
            prompt = repair_instruction(scored) + "\nOriginal task:\n" + task["prompt"]
        best = max(attempts, key=lambda row: row["score"].get("score_0_to_100", 0))
        return {
            "task": task,
            "task_id": task["task_id"],
            "family": task.get("family"),
            "model": runtime.model,
            "runtime_mode": runtime.runtime_mode,
            "attempt_count": len(attempts),
            "attempts": attempts,
            "final_call": best["call"],
            "final_score": best["score"],
            "runtime_seconds": round(time.monotonic() - start, 3),
            "real_model_output": True,
        }
