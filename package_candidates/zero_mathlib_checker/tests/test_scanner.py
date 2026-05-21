import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from zero_mathlib_checker.scanner import scan_root  # noqa: E402


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_clean_sample_passes(tmp_path):
    write(tmp_path / "A.lean", "import MachLib.Basic\n")
    result = scan_root(tmp_path)
    assert result.passed is True
    assert result.direct_match_count == 0


@pytest.mark.parametrize(
    "text",
    ["import " + "Mathlib\n", "from " + "Mathlib import X\n", "example := " + "Mathlib" + ".foo\n"],
)
def test_direct_patterns_fail(tmp_path, text):
    write(tmp_path / "Bad.lean", text)
    result = scan_root(tmp_path)
    assert result.passed is False
    assert result.direct_match_count == 1


def test_dependency_hint_in_lakefile_fails(tmp_path):
    write(tmp_path / "lakefile.lean", "require mathlib from git\n")
    result = scan_root(tmp_path)
    assert result.passed is False
    assert result.dependency_evidence_count == 1


def test_policy_text_can_be_allowed(tmp_path):
    write(tmp_path / "README.md", "POLICY_TEXT import " + "Mathlib is mentioned as policy text\n")
    blocked = scan_root(tmp_path)
    allowed = scan_root(tmp_path, allow_policy_text=True)
    assert blocked.passed is False
    assert allowed.passed is True
    assert allowed.policy_text_count == 1


def test_json_summary_from_cli(tmp_path):
    write(tmp_path / "A.lean", "import MachLib.Basic\n")
    proc = subprocess.run(
        [sys.executable, "-m", "zero_mathlib_checker.cli", "scan", str(tmp_path), "--json"],
        cwd=ROOT,
        env={**os.environ, "PYTHONPATH": str(SRC)},
        text=True,
        capture_output=True,
        check=True,
    )
    data = json.loads(proc.stdout)
    assert data["passed"] is True
    assert data["direct_match_count"] == 0
