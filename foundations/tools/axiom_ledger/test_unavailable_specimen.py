"""SPECIMEN for the axiom-ledger UNAVAILABLE path. A gate with no firing specimen is unvalidated.

WHAT THIS GUARDS. Before 2026-08-01, running `check_ledger.py` on a box with no Lean toolchain
produced a raw `FileNotFoundError: 'lake'` traceback and exit 1 -- the SAME exit code as a drifted
trust boundary. Found by the reproduction dry run, in a clean container, where the honest answer
"nobody checked" was indistinguishable from "the axiom boundary broke".

    A MISSING INSTRUMENT MUST NOT REPORT AS A FAILED MEASUREMENT.

BOTH DIRECTIONS, because a gate that only fires is as useless as one that never does:

  1. FIRES   -- with `lake` removed from PATH, the runner must exit 2 and say UNAVAILABLE.
  2. QUIET   -- with the real PATH, it must NOT report UNAVAILABLE. Without this direction, a
                runner hard-wired to print UNAVAILABLE would pass direction 1 and the specimen
                would certify a gate that has stopped measuring anything.

Direction 2 is skipped -- not passed -- when no toolchain is present, because a check that cannot
run reports UNAVAILABLE rather than success. That is the same rule this file exists to enforce,
applied to the file itself.

Run: python3 tools/axiom_ledger/test_unavailable_specimen.py   (exit 0 = specimen validated)
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
RUNNER = HERE / "check_ledger.py"


def _run(env: dict[str, str]) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(RUNNER)], cwd=HERE,
                          capture_output=True, text=True, env=env)


def direction_fires() -> str | None:
    """`lake` absent -> exit 2, the word UNAVAILABLE, and NO traceback."""
    env = dict(os.environ)
    # An empty-but-present PATH: `lake` is unfindable while the interpreter still runs.
    env["PATH"] = str(HERE / "_no_such_bin_dir")
    p = _run(env)
    out = p.stdout + p.stderr

    if p.returncode != 2:
        return f"expected exit 2 (UNAVAILABLE), got {p.returncode}. output={out[-400:]!r}"
    if "UNAVAILABLE" not in out:
        return f"exit 2 but never said UNAVAILABLE. output={out[-400:]!r}"
    if "Traceback" in out:
        return f"reported UNAVAILABLE but still dumped a traceback. output={out[-400:]!r}"
    if "lake" not in out:
        return f"UNAVAILABLE without naming the missing tool. output={out[-400:]!r}"
    return None


def direction_quiet() -> str | None:
    """Toolchain present -> whatever the verdict, it must NOT be UNAVAILABLE."""
    if shutil.which("lake") is None:
        print("  direction 2: SKIPPED — no `lake` on PATH, so this direction is UNAVAILABLE, "
              "not passing.")
        return None
    p = _run(dict(os.environ))
    out = p.stdout + p.stderr
    if p.returncode == 2 or "UNAVAILABLE" in out:
        return f"the toolchain IS present and the runner still reported UNAVAILABLE: {out[-400:]!r}"
    return None


def main() -> int:
    fails = []
    for name, fn in (("1 FIRES (no toolchain)", direction_fires),
                     ("2 QUIET (toolchain present)", direction_quiet)):
        err = fn()
        print(f"  direction {name}: {'FAIL — ' + err if err else 'ok'}")
        if err:
            fails.append(name)
    if fails:
        print(f"SPECIMEN FAILED: {fails}")
        return 1
    print("SPECIMEN OK — UNAVAILABLE fires when the instrument is missing and stays quiet when it "
          "is not.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
