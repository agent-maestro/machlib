"""Smoke tests for the `machlib` CLI."""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]


def _run(*args: str) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        [sys.executable, "tools/cli/main.py", *args],
        cwd=str(REPO_ROOT),
        capture_output=True,
        text=True,
        timeout=60,
    )


def test_stats_reports_record_count() -> None:
    r = _run("stats")
    assert r.returncode == 0, r.stderr
    assert "total records" in r.stdout
    assert "by domain:" in r.stdout
    assert "by lane:" in r.stdout


def test_stats_json_format() -> None:
    r = _run("stats", "--format", "json")
    assert r.returncode == 0, r.stderr
    import json

    parsed = json.loads(r.stdout)
    assert "total_records" in parsed
    assert "domains" in parsed
    assert "lanes" in parsed


def test_help_does_not_crash() -> None:
    r = _run("--help")
    assert r.returncode == 0
    for sub in ("stats", "generate", "verify"):
        assert sub in r.stdout
