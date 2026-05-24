"""Local model/runtime registry for the Qwen CapCard supervisor."""

from __future__ import annotations

import subprocess
from dataclasses import dataclass
from typing import Any


RUNTIME_MODES = [
    "api_schema_format_think_false",
    "api_schema_format",
    "cli_think_false",
    "cli_hide_thinking",
]

DEFAULT_MODELS = ["qwen3:30b", "qwen3-coder:30b"]


@dataclass(frozen=True)
class ModelRuntime:
    model: str
    runtime_mode: str
    available: bool = True
    startup_success: bool = True
    schema_json_rate: float = 0.0
    no_go_violation_count: int = 0
    average_score: float = 0.0
    median_latency: float = 0.0
    notes: str = ""

    def to_dict(self) -> dict[str, Any]:
        return {
            "model": self.model,
            "runtime_mode": self.runtime_mode,
            "available": self.available,
            "startup_success": self.startup_success,
            "schema_json_rate": self.schema_json_rate,
            "no_go_violation_count": self.no_go_violation_count,
            "average_score": self.average_score,
            "median_latency": self.median_latency,
            "notes": self.notes,
        }


def ollama_model_available(model: str) -> bool:
    proc = subprocess.run(["ollama", "show", model], capture_output=True, text=True, check=False)
    return proc.returncode == 0


def build_default_registry() -> list[ModelRuntime]:
    rows: list[ModelRuntime] = []
    for model in DEFAULT_MODELS:
        available = ollama_model_available(model)
        for mode in RUNTIME_MODES:
            rows.append(
                ModelRuntime(
                    model=model,
                    runtime_mode=mode,
                    available=available,
                    startup_success=available,
                    notes="local Ollama runtime candidate" if available else "model unavailable",
                )
            )
    return rows


def registry_from_matrix(matrix: dict[str, Any]) -> list[ModelRuntime]:
    rows = []
    for row in matrix.get("rows", []):
        rows.append(
            ModelRuntime(
                model=row["model"],
                runtime_mode=row["runtime_mode"],
                available=row.get("available", True),
                startup_success=row.get("startup_success", True),
                schema_json_rate=float(row.get("schema_json_rate", 0.0)),
                no_go_violation_count=int(row.get("no_go_violation_count", 0)),
                average_score=float(row.get("average_score", 0.0)),
                median_latency=float(row.get("median_latency", 0.0)),
                notes=row.get("notes", ""),
            )
        )
    return rows
