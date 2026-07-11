#!/usr/bin/env python3
"""AxiomLedger CI runner — enforces the machine-checked axiom trust boundary.

`AxiomLedger.lean` is the gate: building it `logError`s (→ non-zero exit) on any boundary
drift — a new/undisclosed axiom (unknown), a ledger entry whose axiom vanished (rot), a
shipped headline footprint growing past the trusted set (leak), or a disclosed axiom going
load-bearing. This runner builds it and asserts green, and `--self-test` proves the gate goes
RED on a canary (same discipline as claim_audit.py's canary).

No grep, no name paraphrase in the trust path: the gate enumerates axioms from the Lean
environment and reads footprints from the kernel's own `collectAxioms`.

Usage:
    python3 tools/axiom_ledger/check_ledger.py              # enforce the boundary
    python3 tools/axiom_ledger/check_ledger.py --self-test  # + prove the gate goes RED on a canary
"""
import os, re, subprocess, sys, tempfile

FOUND = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
LEDGER = os.path.join(FOUND, "AxiomLedger.lean")
G, R, RST, B = "\033[32m", "\033[31m", "\033[0m", "\033[1m"


def run_lean(path: str) -> tuple[int, str]:
    p = subprocess.run(["lake", "env", "lean", path], cwd=FOUND,
                       capture_output=True, text=True)
    return p.returncode, p.stdout + p.stderr


def enforce() -> int:
    code, out = run_lean(LEDGER)
    ok = re.search(r"AxiomLedger OK: (\d+) axioms pinned; (\d+) headline", out)
    if code == 0 and ok:
        print(f"{G}{B}AXIOM-LEDGER PASS{RST}  {ok.group(1)} axioms pinned, "
              f"{ok.group(2)} headline footprints ⊆ trusted.")
        return 0
    print(f"{R}{B}AXIOM-LEDGER FAIL{RST} — the trust boundary drifted:")
    for line in out.splitlines():
        if "AxiomLedger:" in line or "error" in line.lower():
            print(f"    {R}{line.strip()}{RST}")
    return 1


def self_test() -> int:
    """Perturb the ledger (inject a vanished axiom) and confirm the gate goes RED."""
    src = open(LEDGER, encoding="utf-8").read()
    canary = src.replace("def knownAxioms : List Name := [",
                         "def knownAxioms : List Name := [`MachLib.Real._ledger_canary_absent, ", 1)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=FOUND, delete=False) as f:
        f.write(canary); path = f.name
    try:
        code, out = run_lean(path)
    finally:
        os.unlink(path)
    if code != 0 and "rot" in out:
        print(f"{G}canary OK{RST} — the gate goes RED when the ledger drifts (rot detected).")
        return 0
    print(f"{R}canary FAILED — the gate did NOT go red on a drifted ledger; it has no teeth.{RST}")
    return 1


def main() -> int:
    rc = enforce()
    if "--self-test" in sys.argv:
        rc |= self_test()
    return rc


if __name__ == "__main__":
    sys.exit(main())
