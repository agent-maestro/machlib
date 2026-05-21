import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from zero_mathlib_checker.cli import main  # noqa: E402
from zero_mathlib_checker.scanner import scan_path, scan_root  # noqa: E402


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_clean_sample_passes(tmp_path):
    write(tmp_path / "A.lean", "import MachLib.Basic\n")
    result = scan_path(tmp_path)
    assert result.passed is True
    assert result.dependency_evidence_count == 0
    assert result.direct_match_count == 0


@pytest.mark.parametrize(
    ("text", "evidence_type"),
    [
        ("import " + "Mathlib\n", "IMPORT_MATHLIB"),
        ("from " + "Mathlib import X\n", "FROM_MATHLIB"),
        ("example := " + "Mathlib" + ".foo\n", "MATHLIB_DOT_REFERENCE"),
    ],
)
def test_direct_patterns_fail(tmp_path, text, evidence_type):
    write(tmp_path / "Bad.lean", text)
    result = scan_path(tmp_path)
    assert result.passed is False
    assert result.direct_match_count == 1
    assert result.dependency_evidence_count == 1
    assert result.evidence[0].evidence_type == evidence_type


@pytest.mark.parametrize("name", ["lakefile.lean", "lake-manifest.json", "lakefile.toml"])
def test_dependency_hint_in_lake_files_fails(tmp_path, name):
    write(tmp_path / name, "require mathlib from git\n")
    result = scan_path(tmp_path)
    assert result.passed is False
    assert result.dependency_evidence_count == 1
    assert result.evidence[0].evidence_type == "MATHLIB_DEPENDENCY_DECLARATION"


def test_policy_text_can_be_allowed(tmp_path):
    write(tmp_path / "README.md", "POLICY_TEXT import " + "Mathlib is mentioned as policy text\n")
    blocked = scan_path(tmp_path)
    allowed = scan_path(tmp_path, allow_policy_text=True)
    assert blocked.passed is False
    assert allowed.passed is True
    assert allowed.policy_text_count == 1


def test_policy_text_not_allowed_without_flag(tmp_path):
    write(tmp_path / "README.md", "POLICY_TEXT from " + "Mathlib appears in policy text\n")
    result = scan_path(tmp_path)
    assert result.passed is False
    assert result.dependency_evidence_count == 1


def test_excluded_directories_are_ignored(tmp_path):
    write(tmp_path / "node_modules" / "Bad.lean", "import " + "Mathlib\n")
    write(tmp_path / "src" / "Good.lean", "import MachLib.Basic\n")
    result = scan_path(tmp_path)
    assert result.passed is True
    assert result.scanned_files == 1


def test_extra_exclude_dir_is_ignored(tmp_path):
    write(tmp_path / "vendor" / "Bad.lean", "import " + "Mathlib\n")
    result = scan_path(tmp_path, exclude_dirs=("vendor",))
    assert result.passed is True
    assert result.scanned_files == 0


def test_include_filter_limits_scan(tmp_path):
    write(tmp_path / "Bad.lean", "import " + "Mathlib\n")
    write(tmp_path / "README.md", "from " + "Mathlib import Foo\n")
    result = scan_path(tmp_path, include=("*.md",))
    assert result.passed is False
    assert result.scanned_files == 1
    assert result.evidence[0].path == "README.md"


def test_scan_root_compatibility_alias(tmp_path):
    write(tmp_path / "A.lean", "def x := 1\n")
    assert scan_root(tmp_path).passed is True


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
    assert data["dependency_evidence_count"] == 0
    assert data["scanned_files"] == 1


def test_cli_main_exit_codes(tmp_path, capsys):
    write(tmp_path / "Good.lean", "def x := 1\n")
    assert main(["scan", str(tmp_path)]) == 0
    good_output = capsys.readouterr().out
    assert "ZERO_MATHLIB_CHECKER PASS" in good_output

    write(tmp_path / "Bad.lean", "import " + "Mathlib\n")
    assert main(["scan", str(tmp_path)]) == 1
    bad_output = capsys.readouterr().out
    assert "ZERO_MATHLIB_CHECKER FAIL" in bad_output
