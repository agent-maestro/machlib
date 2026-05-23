"""Local runner for Qwen CapCard tasks."""

from __future__ import annotations

import json
import shutil
import subprocess
from pathlib import Path
from typing import Any


def ollama_available() -> bool:
    return shutil.which("ollama") is not None


def run_ollama(model: str, prompt: str, timeout_seconds: int = 120) -> tuple[str | None, str | None]:
    if not ollama_available():
        return None, "ollama unavailable"
    try:
        proc = subprocess.run(
            ["ollama", "run", model, prompt],
            check=False,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
        )
    except subprocess.TimeoutExpired:
        return None, f"ollama run timed out after {timeout_seconds}s"
    if proc.returncode != 0:
        return None, proc.stderr.strip() or f"ollama exited {proc.returncode}"
    return proc.stdout.strip(), None


def deterministic_fixture_output(task: dict[str, Any], repaired: bool = False) -> str:
    status = "READY_FOR_HUMAN_REPAIR_REVIEW" if repaired else "BLOCKED_WITH_EXACT_FIX_LIST"
    payload = {
        "candidate_id": task["task_id"],
        "status": status,
        "evidence_basis": [
            "local scorer fixture",
            "Qwen runtime not represented as real output for this row",
            "direct repair evidence still required for warn/unknown rows",
        ],
        "limitations": [
            "dry-run scorer-only output" if not repaired else "repair-loop template output",
            "row 2/3 warn and unknown blockers remain bounded unless direct evidence is added",
            "stale Command Center references are not direct evidence",
        ],
        "not_claimed": [
            "not PETAL/API uploaded",
            "not Hugging Face uploaded",
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


def write_model_output(path: Path, task_id: str, model: str, output_text: str, real_model_output: bool) -> None:
    path.mkdir(parents=True, exist_ok=True)
    (path / f"{task_id}_{model.replace(':', '_')}.json").write_text(
        json.dumps(
            {
                "task_id": task_id,
                "model": model,
                "real_model_output": real_model_output,
                "output_text": output_text,
            },
            indent=2,
            sort_keys=True,
        )
        + "\n"
    )
