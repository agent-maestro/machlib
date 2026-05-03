"""End-to-end smoke tests for LeanKernelVerifier (C-239).

These tests invoke `lake build` against the local MachLib lake project,
so they require:
  - elan + lean v4.14.0 on PATH (or ~/.elan/bin available)
  - foundations/ already cold-built (lake build at least once)

Tests are auto-skipped when the toolchain isn't reachable.
"""
from __future__ import annotations

import os
import shutil
from pathlib import Path

import pytest

# Make ~/.elan/bin reachable for lake/lean if not already on PATH.
_ELAN_BIN = Path.home() / ".elan" / "bin"
if _ELAN_BIN.is_dir():
    _path = os.environ.get("PATH", "")
    if str(_ELAN_BIN) not in _path:
        os.environ["PATH"] = f"{_ELAN_BIN}{os.pathsep}{_path}"

# Skip the whole module if lake is unreachable.
_TOOLCHAIN_OK = shutil.which("lake") is not None
pytestmark = pytest.mark.skipif(
    not _TOOLCHAIN_OK, reason="lake not on PATH; install elan first"
)

# Import after the PATH adjustment so the verifier sees the right env.
from gym.verifiers import LeanKernelVerifier  # noqa: E402


# A self-contained synthetic theorem with the target-sorry marker.
# Imports + open clauses match the Discovered/ file shape so the
# verifier exercises the same elaborator path the sweep will use.
_TEMPLATE = """\
import MachLib.Basic
import MachLib.EML
import MachLib.Trig
import MachLib.Forge

open MachLib
open MachLib.Real

theorem _test_exp_nonneg (x : Real) : (0 : Real) ≤ Real.exp x := by
  sorry /-TARGET-/
"""


@pytest.fixture(scope="module")
def verifier() -> LeanKernelVerifier:
    """Single verifier instance reused across tests (warm cache)."""
    return LeanKernelVerifier(default_timeout=30.0)


def test_construction(verifier: LeanKernelVerifier) -> None:
    assert verifier.name == "lean_kernel_v1"
    assert verifier.backend == "local"
    assert verifier._worker.is_available(), (
        "LeanWorker is not available; check PATH and that "
        f"foundations/ exists at {verifier._worker.lean_repo}"
    )


def test_positive_control_known_good_tactic(verifier: LeanKernelVerifier) -> None:
    """A known-correct tactic should be accepted."""
    closed = verifier.verify(
        _TEMPLATE,
        tactic_sequence=["exact exp_nonneg _"],
        timeout_seconds=30.0,
    )
    assert closed is True, (
        "Positive control failed — `exact exp_nonneg _` should close "
        "`(0 : Real) ≤ Real.exp x`. Likely cause: MachLib cold build "
        "missing or import path wrong."
    )


def test_negative_control_obviously_wrong_tactic(verifier: LeanKernelVerifier) -> None:
    """A tactic that doesn't close the goal must be rejected."""
    closed = verifier.verify(
        _TEMPLATE,
        tactic_sequence=["trivial"],
        timeout_seconds=30.0,
    )
    assert closed is False, (
        "Negative control failed — `trivial` should NOT close "
        "`(0 : Real) ≤ Real.exp x` (the goal is not `True`)."
    )


def test_missing_target_marker_rejects(verifier: LeanKernelVerifier) -> None:
    """If the source has no TARGET_SORRY_MARKER, verify must fail closed."""
    no_marker = _TEMPLATE.replace("sorry /-TARGET-/", "exact exp_nonneg _")
    closed = verifier.verify(no_marker, tactic_sequence=["rfl"])
    assert closed is False
