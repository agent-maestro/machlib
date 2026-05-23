"""Local model adapter for Ollama-backed Qwen calls."""

from __future__ import annotations

import subprocess
import time
from dataclasses import dataclass
from typing import Any

from .json_extract import ExtractionResult, extract_json_object


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
        }


def call_ollama_json(
    model: str,
    prompt: str,
    *,
    timeout_seconds: int = 120,
    required_fields: list[str] | None = None,
) -> LocalModelCallResult:
    command = ["ollama", "run", model, prompt]
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
    )
