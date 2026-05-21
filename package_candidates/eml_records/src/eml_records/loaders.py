"""JSON loading helpers for local EML record validation."""

from __future__ import annotations

import json
from fnmatch import fnmatch
from pathlib import Path
from typing import Any


DEFAULT_EXCLUDE_DIRS = {
    ".git",
    ".venv",
    "__pycache__",
    "node_modules",
    "dist",
    "build",
    ".mypy_cache",
    ".pytest_cache",
}


def load_json_file(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def _matches_include(path: Path, include: tuple[str, ...]) -> bool:
    return any(fnmatch(path.name, pattern) or fnmatch(str(path), pattern) for pattern in include)


def _is_excluded(path: Path, root: Path, exclude_dirs: set[str]) -> bool:
    try:
        parts = path.relative_to(root).parts
    except ValueError:
        parts = path.parts
    return any(part in exclude_dirs for part in parts[:-1])


def iter_json_files(
    path: Path,
    include: tuple[str, ...] | None = None,
    exclude_dir: tuple[str, ...] | None = None,
) -> list[Path]:
    include_patterns = include or ("*.json",)
    excluded = set(DEFAULT_EXCLUDE_DIRS)
    excluded.update(exclude_dir or ())
    if path.is_file():
        return [path] if _matches_include(path, include_patterns) else []
    return sorted(
        candidate
        for candidate in path.rglob("*")
        if candidate.is_file()
        and not _is_excluded(candidate, path, excluded)
        and _matches_include(candidate, include_patterns)
    )


def _flatten_records(value: Any) -> list[dict[str, Any]]:
    if isinstance(value, dict):
        return [value]
    if isinstance(value, list):
        records: list[dict[str, Any]] = []
        for row in value:
            records.extend(_flatten_records(row))
        return records
    return []


def records_from_json_object(obj: Any) -> list[dict[str, Any]]:
    if isinstance(obj, dict) and isinstance(obj.get("records"), list):
        return _flatten_records(obj["records"])
    return _flatten_records(obj)


def load_records_from_path(
    path: Path,
    include: tuple[str, ...] | None = None,
    exclude_dir: tuple[str, ...] | None = None,
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for json_path in iter_json_files(path, include=include, exclude_dir=exclude_dir):
        records.extend(records_from_json_object(load_json_file(json_path)))
    return records


def load_records(
    path: Path,
    include: tuple[str, ...] | None = None,
    exclude_dir: tuple[str, ...] | None = None,
) -> tuple[list[dict[str, Any]], list[str], int]:
    records: list[dict[str, Any]] = []
    failures: list[str] = []
    scanned_file_count = 0
    for json_path in iter_json_files(path, include=include, exclude_dir=exclude_dir):
        scanned_file_count += 1
        try:
            obj = load_json_file(json_path)
        except Exception as exc:  # noqa: BLE001 - expose parse failure in CLI.
            failures.append(f"{json_path}: JSON parse failed: {exc}")
            continue
        records.extend(records_from_json_object(obj))
    return records, failures, scanned_file_count
