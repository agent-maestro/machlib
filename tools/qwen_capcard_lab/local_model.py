"""Local model adapter for Ollama-backed Qwen calls."""

from __future__ import annotations

import json
import subprocess
import time
from dataclasses import dataclass
from typing import Any
from urllib import request, error

from .json_extract import ExtractionResult, extract_json_object


LOCAL_OLLAMA_API = "http://127.0.0.1:11434/api/generate"

CAPCARD_RESULT_SCHEMA: dict[str, Any] = {
    "type": "object",
    "additionalProperties": False,
    "required": [
        "task_id",
        "status",
        "candidate_status",
        "evidence_present",
        "missing_evidence",
        "forbidden_claims_present",
        "public_ready",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "production_marketplace_modified",
        "theorem_proof_claim",
        "certified_safety_claim",
        "production_controller_claim",
        "explanation",
    ],
    "properties": {
        "task_id": {"type": "string"},
        "status": {"type": "string", "enum": ["PASS", "WARN", "FAIL", "BLOCKED"]},
        "candidate_status": {
            "type": "string",
            "enum": [
                "BLOCKED_WITH_EXACT_FIX_LIST",
                "READY_FOR_HUMAN_REPAIR_REVIEW",
                "INTERNAL_DRAFT_CANDIDATE",
            ],
        },
        "evidence_present": {"type": "boolean"},
        "missing_evidence": {"type": "array", "items": {"type": "string"}},
        "forbidden_claims_present": {"type": "boolean", "const": False},
        "public_ready": {"type": "boolean", "const": False},
        "petal_api_upload_performed": {"type": "boolean", "const": False},
        "huggingface_upload_performed": {"type": "boolean", "const": False},
        "production_marketplace_modified": {"type": "boolean", "const": False},
        "theorem_proof_claim": {"type": "boolean", "const": False},
        "certified_safety_claim": {"type": "boolean", "const": False},
        "production_controller_claim": {"type": "boolean", "const": False},
        "explanation": {"type": "string"},
    },
}

STRUCTURED_REQUIRED_FIELDS = list(CAPCARD_RESULT_SCHEMA["required"])


@dataclass(frozen=True)
class LocalModelCallResult:
    model: str
    prompt: str
    command: list[str]
    raw_output: str
    stderr: str
    returncode: int | None
    runtime_seconds: float
    extraction_status: str
    extracted_json: dict[str, Any] | None
    extraction_diagnostics: list[str]
    real_model_output: bool
    mode: str = "cli_default"
    schema_valid: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "prompt": self.prompt,
            "command": self.command,
            "raw_output": self.raw_output,
            "stderr": self.stderr,
            "returncode": self.returncode,
            "runtime_seconds": round(self.runtime_seconds, 3),
            "extraction_status": self.extraction_status,
            "extracted_json": self.extracted_json,
            "extraction_diagnostics": self.extraction_diagnostics,
            "real_model_output": self.real_model_output,
            "mode": self.mode,
            "schema_valid": self.schema_valid,
        }


def structured_schema_text() -> str:
    return json.dumps(CAPCARD_RESULT_SCHEMA, sort_keys=True)


def build_structured_prompt(task_prompt: str, *, task_id: str | None = None) -> str:
    task_line = f"Task id: {task_id}\n" if task_id else ""
    return (
        "Return one JSON object that validates against this JSON Schema. "
        "No markdown, no prose, no hidden reasoning text in the response.\n"
        f"{task_line}"
        "If evidence is missing, set evidence_present false and list missing_evidence. "
        "Never invent acceptance. Keep every upload, public, proof, safety, and production field false.\n"
        "Schema:\n"
        + structured_schema_text()
        + "\nTask:\n"
        + task_prompt
    )


def _schema_valid(data: dict[str, Any] | None, required_fields: list[str] | None) -> bool:
    if data is None:
        return False
    return all(key in data for key in required_fields or [])


def call_ollama_json(
    model: str,
    prompt: str,
    *,
    timeout_seconds: int = 120,
    required_fields: list[str] | None = None,
    mode: str = "cli_default",
) -> LocalModelCallResult:
    command_prompt = prompt
    command = ["ollama", "run", model, command_prompt]
    if mode == "cli_think_false":
        command_prompt = "/set nothink\n" + prompt
        command = ["ollama", "run", model, command_prompt]
    elif mode == "cli_hide_thinking":
        command_prompt = "Do not include thinking text. Return only the final JSON.\n" + prompt
        command = ["ollama", "run", model, command_prompt]
    start = time.monotonic()
    try:
        proc = subprocess.run(
            command,
            capture_output=True,
            text=True,
            timeout=timeout_seconds,
            check=False,
        )
    except subprocess.TimeoutExpired as exc:
        runtime = time.monotonic() - start
        raw = (exc.stdout or "") if isinstance(exc.stdout, str) else ""
        err = (exc.stderr or "") if isinstance(exc.stderr, str) else ""
        return LocalModelCallResult(
            model=model,
            prompt=prompt,
            command=command,
            raw_output=raw,
            stderr=err,
            returncode=None,
            runtime_seconds=runtime,
            extraction_status="MODEL_TIMEOUT",
            extracted_json=None,
            extraction_diagnostics=[f"timeout_after_{timeout_seconds}s"],
            real_model_output=True,
            mode=mode,
        )
    runtime = time.monotonic() - start
    raw_output = proc.stdout or ""
    stderr = proc.stderr or ""
    if proc.returncode != 0:
        return LocalModelCallResult(
            model=model,
            prompt=prompt,
            command=command,
            raw_output=raw_output,
            stderr=stderr,
            returncode=proc.returncode,
            runtime_seconds=runtime,
            extraction_status="MODEL_ERROR",
            extracted_json=None,
            extraction_diagnostics=[stderr.strip() or f"returncode_{proc.returncode}"],
            real_model_output=True,
            mode=mode,
        )
    extraction: ExtractionResult = extract_json_object(raw_output, required_fields=required_fields)
    return LocalModelCallResult(
        model=model,
        prompt=prompt,
        command=command,
        raw_output=raw_output,
        stderr=stderr,
        returncode=proc.returncode,
        runtime_seconds=runtime,
        extraction_status=extraction.extraction_status,
        extracted_json=extraction.extracted_json,
        extraction_diagnostics=extraction.diagnostics,
        real_model_output=True,
        mode=mode,
        schema_valid=_schema_valid(extraction.extracted_json, required_fields),
    )


def call_ollama_structured_api(
    model: str,
    prompt: str,
    *,
    timeout_seconds: int = 120,
    required_fields: list[str] | None = None,
    think_false: bool = False,
    use_schema: bool = True,
    endpoint: str = LOCAL_OLLAMA_API,
) -> LocalModelCallResult:
    if not endpoint.startswith("http://127.0.0.1:") and not endpoint.startswith("http://localhost:"):
        return LocalModelCallResult(
            model=model,
            prompt=prompt,
            command=["ollama-api", endpoint],
            raw_output="",
            stderr="external_url_blocked",
            returncode=None,
            runtime_seconds=0,
            extraction_status="MODEL_ERROR",
            extracted_json=None,
            extraction_diagnostics=["external_url_blocked"],
            real_model_output=False,
            mode="api_schema_format_think_false" if think_false else "api_schema_format",
        )

    if use_schema:
        mode = "api_schema_format_think_false" if think_false else "api_schema_format"
    else:
        mode = "api_json_format"
    body: dict[str, Any] = {
        "model": model,
        "prompt": prompt,
        "format": CAPCARD_RESULT_SCHEMA if use_schema else "json",
        "stream": False,
    }
    if think_false:
        body["think"] = False
        body["options"] = {"think": False}
    payload = json.dumps(body).encode("utf-8")
    start = time.monotonic()
    req = request.Request(
        endpoint,
        data=payload,
        headers={"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with request.urlopen(req, timeout=timeout_seconds) as response:
            raw_response = response.read().decode("utf-8", errors="replace")
    except TimeoutError:
        return LocalModelCallResult(
            model=model,
            prompt=prompt,
            command=["ollama-api", endpoint, model, "format:schema" if use_schema else "format:json"],
            raw_output="",
            stderr="timeout",
            returncode=None,
            runtime_seconds=time.monotonic() - start,
            extraction_status="MODEL_TIMEOUT",
            extracted_json=None,
            extraction_diagnostics=[f"timeout_after_{timeout_seconds}s"],
            real_model_output=True,
            mode=mode,
        )
    except (error.URLError, OSError) as exc:
        return LocalModelCallResult(
            model=model,
            prompt=prompt,
            command=["ollama-api", endpoint, model, "format:schema" if use_schema else "format:json"],
            raw_output="",
            stderr=str(exc),
            returncode=None,
            runtime_seconds=time.monotonic() - start,
            extraction_status="STRUCTURED_API_UNAVAILABLE",
            extracted_json=None,
            extraction_diagnostics=[str(exc)],
            real_model_output=True,
            mode=mode,
        )

    runtime = time.monotonic() - start
    try:
        envelope = json.loads(raw_response)
    except json.JSONDecodeError:
        return LocalModelCallResult(
            model=model,
            prompt=prompt,
            command=["ollama-api", endpoint, model, "format:schema" if use_schema else "format:json"],
            raw_output=raw_response,
            stderr="invalid_api_json",
            returncode=None,
            runtime_seconds=runtime,
            extraction_status="JSON_INVALID",
            extracted_json=None,
            extraction_diagnostics=["api_envelope_invalid_json"],
            real_model_output=True,
            mode=mode,
        )
    response_text = str(envelope.get("response", ""))
    extraction = extract_json_object(response_text, required_fields=required_fields)
    status = "SCHEMA_JSON" if extraction.extraction_status == "EXACT_JSON" and not extraction.diagnostics else extraction.extraction_status
    if extraction.extraction_status == "EXACT_JSON":
        status = "SCHEMA_JSON"
    return LocalModelCallResult(
        model=model,
        prompt=prompt,
        command=["ollama-api", endpoint, model, "format:schema" if use_schema else "format:json"],
        raw_output=response_text,
        stderr="",
        returncode=None,
        runtime_seconds=runtime,
        extraction_status=status,
        extracted_json=extraction.extracted_json,
        extraction_diagnostics=extraction.diagnostics,
        real_model_output=True,
        mode=mode,
        schema_valid=_schema_valid(extraction.extracted_json, required_fields),
    )
