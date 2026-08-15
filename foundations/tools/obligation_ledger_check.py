#!/usr/bin/env python3
"""Gate: the obligations ledger must not rot.

`EMLDepthTameness` ends with a table of named obligations and their status. "Discharged" is
machine-checkable — a theorem concludes the proposition. "Open" was not, so the column was
hand-maintained: discharge an obligation, forget the row, and nothing failed.

This closes that. For each row:

  status "open"        -> FAIL if any theorem concludes the proposition (the row is stale)
  status "discharged"  -> FAIL if the named discharger is absent, or does not conclude it

Exit 0 pass, 1 stale/missing, 2 the ledger itself could not be read (UNAVAILABLE, not a pass).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "MachLib" / "EMLDepthTameness.lean"
SOURCES = sorted((ROOT / "MachLib").glob("*.lean"))

ROW = re.compile(
    r"^\|\s*`([A-Za-z0-9_]+)`\s*\|[^|]*\|\s*\*\*(open|discharged)\*\*\s*\|\s*(.*?)\s*\|\s*$"
)


def declarations(text):
    """Yield (kind, name, signature) for each top-level declaration."""
    lines = text.split("\n")
    starts = [
        i for i, l in enumerate(lines)
        if re.match(r"^(theorem|def|noncomputable def|private theorem) ", l)
    ]
    for n, i in enumerate(starts):
        end = starts[n + 1] if n + 1 < len(starts) else len(lines)
        block = "\n".join(lines[i:end])
        m = re.match(r"^(theorem|def|noncomputable def|private theorem)\s+([A-Za-z0-9_']+)", block)
        if not m:
            continue
        # signature = everything up to the proof/definition body
        sig = re.split(r":=", block, maxsplit=1)[0]
        yield m.group(1), m.group(2), sig


def dischargers_of(prop, decls):
    """Theorems whose CONCLUSION is `prop` — not merely those mentioning it."""
    out = []
    for kind, name, sig in decls:
        if not kind.endswith("theorem"):
            continue
        # strip binders `(h : Prop)` so a consumer does not read as a discharger
        stripped = re.sub(r"\([^()]*:\s*" + re.escape(prop) + r"\b[^()]*\)", "", sig)
        # conclusion is the tail after the last top-level `:`
        tail = stripped.rsplit(":", 1)[-1].strip()
        if re.match(r"^" + re.escape(prop) + r"\b", tail):
            out.append(name)
    return out


def check_rows(rows, decls):
    """Returns (bad_count, report_lines). Shared by the gate and its self-test."""
    bad, out = 0, []
    for prop, status, discharger in rows:
        found = dischargers_of(prop, decls)
        if status == "open":
            if found:
                out.append(f"  STALE  {prop}: marked open but discharged by {', '.join(found)}")
                bad += 1
            else:
                out.append(f"  ok     {prop}: open, no discharger")
        else:
            named = re.findall(r"`([A-Za-z0-9_\']+)`", discharger)
            hit = [n for n in named if n in found]
            if hit:
                out.append(f"  ok     {prop}: discharged by {hit[0]}")
            else:
                out.append(f"  BROKEN {prop}: marked discharged; "
                           f"cited {named or '(none)'}, actual dischargers {found or '(none)'}")
                bad += 1
    return bad, out


def self_test(decls) -> int:
    """Two convict specimens. The gate is unvalidated until both fire."""
    ok = True

    # 1. A discharged obligation mislabelled open must be caught.
    bad, out = check_rows([("VarLeftEmlRightHard", "open", "")], decls)
    fired = bad == 1 and "STALE" in out[0]
    print(f"  canary 1 (discharged row mislabelled open)  {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 2. An open obligation mislabelled discharged must be caught.
    bad, out = check_rows([("SignHardCase", "discharged", "`no_such_theorem`")], decls)
    fired = bad == 1 and "BROKEN" in out[0]
    print(f"  canary 2 (open row mislabelled discharged)  {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 3. And the true ledger must still pass, so the canaries are not just "everything fails".
    bad, _ = check_rows([("VarLeftEmlRightHard", "discharged", "`varLeftEmlRightHard_of_band`")],
                        decls)
    quiet = bad == 0
    print(f"  canary 3 (a correct row stays silent)       {'SILENT' if quiet else 'FIRES'}")
    ok &= quiet

    print()
    if not ok:
        print("LEDGER SELF-TEST FAIL — a canary did not fire; the gate is unvalidated")
        return 1
    print("LEDGER SELF-TEST PASS — both canaries fire")
    return 0


def main() -> int:
    if not LEDGER.exists():
        print(f"UNAVAILABLE: {LEDGER} not found", file=sys.stderr)
        return 2
    rows = [m.groups() for m in (ROW.match(l) for l in LEDGER.read_text().split("\n")) if m]
    if not rows:
        print("UNAVAILABLE: no ledger rows parsed — has the table format changed?", file=sys.stderr)
        return 2

    decls = []
    for src in SOURCES:
        decls.extend(declarations(src.read_text()))

    if "--self-test" in sys.argv:
        rc = self_test(decls)
        if rc:
            return rc
        print()

    bad, out = check_rows(rows, decls)
    for line in out:
        print(line)

    print()
    if bad:
        print(f"OBLIGATION-LEDGER FAIL — {bad}/{len(rows)} row(s) do not match the corpus")
        return 1
    print(f"OBLIGATION-LEDGER OK — {len(rows)} rows match the corpus")
    return 0


if __name__ == "__main__":
    sys.exit(main())
