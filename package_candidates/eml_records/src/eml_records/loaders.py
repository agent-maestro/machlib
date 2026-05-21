"""JSON loading helpers for local EML record validation."""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def iter_json_files(path: Path) -> list[Path]:
    if path.is_file():
        return [path] if path.suffix == ".json" else []
    return sorted(candidate for candidate in path.rglob("*.json") if candidate.is_file())


def records_from_json_object(obj: Any) -> list[dict[str, Any]]:
    if isinstance(obj, list):
        return [row for row in obj if isinstance(row, dict)]
    if isinstance(obj, dict):
        if isinstance(obj.get("records"), list):
            return [row for row in obj["records"] if isinstance(row, dict)]
        return [obj]
    return []


def load_records(path: Path) -> tuple[list[dict[str, Any]], list[str], int]:
    records: list[dict[str, Any]] = []
    failures: list[str] = []
    scanned_file_count = 0
    for json_path in iter_json_files(path):
        scanned_file_count += 1
        try:
            obj = json.loads(json_path.read_text(encoding="utf-8"))
        except Exception as exc:  # noqa: BLE001 - expose parse failure in CLI.
            failures.append(f"{json_path}: JSON parse failed: {exc}")
            continue
        records.extend(records_from_json_object(obj))
    return records, failures, scanned_file_count
