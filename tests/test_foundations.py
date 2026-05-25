"""Smoke tests for the independent Lean foundations.

These check the *artefacts* of the build (no Mathlib imports,
expected files exist, lake build passes) rather than re-running
Lean's kernel inside pytest.
"""
from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
FOUNDATIONS = REPO_ROOT / "foundations"
MACHLIB_DIR = FOUNDATIONS / "MachLib"


def test_foundations_directory_exists() -> None:
    assert FOUNDATIONS.is_dir()
    assert MACHLIB_DIR.is_dir()


def test_phase1_modules_present() -> None:
    expected = {
        "Basic.lean", "Exp.lean", "Log.lean", "Trig.lean", "EML.lean",
    }
    actual = {p.name for p in MACHLIB_DIR.glob("*.lean")}
    missing = expected - actual
    assert not missing, f"Phase 1 modules missing: {sorted(missing)}"


def test_aggregator_imports_all_phase1_modules() -> None:
    aggregator = FOUNDATIONS / "MachLib.lean"
    text = aggregator.read_text(encoding="utf-8")
    for module in ("Basic", "Exp", "Log", "Trig", "EML"):
        assert f"import MachLib.{module}" in text, (
            f"aggregator missing import of MachLib.{module}"
        )


def test_zero_mathlib_imports() -> None:
    """No active foundations file imports Mathlib."""
    for path in list(MACHLIB_DIR.glob("*.lean")) + [FOUNDATIONS / "MachLib.lean"]:
        text = path.read_text(encoding="utf-8")
        for line in text.splitlines():
            stripped = line.strip()
            if stripped.startswith("import "):
                assert "Mathlib" not in stripped, (
                    f"{path}:{line!r} — Mathlib import in active foundations"
                )


def test_lakefile_has_no_mathlib_require() -> None:
    text = (FOUNDATIONS / "lakefile.lean").read_text(encoding="utf-8")
    code_lines = [
        ln for ln in text.splitlines()
        if not ln.strip().startswith("--")
    ]
    code = "\n".join(code_lines)
    assert "require mathlib" not in code, (
        "lakefile.lean still requires mathlib"
    )


@pytest.mark.skipif(
    shutil.which("lake") is None
    and not (Path.home() / ".elan" / "bin" / "lake.exe").exists(),
    reason="lake binary not on PATH",
)
def test_lake_build_passes() -> None:
    """Run `lake build` and assert exit 0."""
    lake = shutil.which("lake") or str(
        Path.home() / ".elan" / "bin" / "lake.exe"
    )
    result = subprocess.run(
        [lake, "build"],
        cwd=str(FOUNDATIONS),
        capture_output=True,
        text=True,
        timeout=120,
    )
    assert result.returncode == 0, (
        f"lake build failed: stdout={result.stdout!r} stderr={result.stderr!r}"
    )
    # The foundations build currently includes explicit RED/GREEN and
    # discovered-kernel draft files. Those are allowed to emit Lean's
    # `sorry` warning while remaining internal draft evidence; this smoke test
    # only gates successful build completion and the separate zero-Mathlib
    # dependency checks above.
