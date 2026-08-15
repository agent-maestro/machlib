#!/usr/bin/env python3
"""Gate: the obligations ledger must not rot.

`EMLDepthTameness` ends with a table of named obligations and their status. "Discharged" is
machine-checkable — a theorem concludes the proposition. "Open" was not, so the column was
hand-maintained: discharge an obligation, forget the row, and nothing failed.

This closes that. For each row:

  status "open"        -> FAIL if any theorem concludes the proposition (the row is stale)
  status "discharged"  -> FAIL if the named discharger is absent, or does not conclude it

The table is DUPLICATED in CHANGELOG.md, and the copy is what actually went stale first: a row was
added to the Lean ledger and the changelog kept saying "Four propositions" over four rows. A gate
that reads one copy of a duplicated table certifies the copy nobody reads. So both are parsed and
required to agree, obligation for obligation.

Exit 0 pass, 1 stale/missing/divergent, 2 a ledger could not be read (UNAVAILABLE, not a pass).
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "MachLib" / "EMLDepthTameness.lean"
CHANGELOG = ROOT.parent / "CHANGELOG.md"
SOURCES = sorted((ROOT / "MachLib").glob("*.lean"))


def parse_rows(text):
    """Rows as (prop, status, discharger).

    Column-count agnostic on purpose: the Lean ledger carries a `where` column the changelog copy
    does not, and pinning column positions would make the gate silently stop matching one of them.
    A row is any table line whose first cell is a backticked identifier and which has exactly one
    **open** / **discharged** cell.
    """
    rows = []
    for line in text.split("\n"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if not cells:
            continue
        m = re.fullmatch(r"`([A-Za-z0-9_']+)`", cells[0])
        if not m:
            continue
        stat = [c for c in cells if c in ("**open**", "**discharged**", "**refuted**")]
        if len(stat) != 1:
            continue
        i = cells.index(stat[0])
        rows.append((m.group(1), stat[0].strip("*"), " ".join(cells[i + 1:])))
    return rows


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
        if status in ("open", "refuted"):
            # "refuted" means we believe P false; a theorem concluding P would be a contradiction,
            # so the corpus check is the same one, and a hit is more serious rather than less.
            if found:
                out.append(f"  {'CONTRA' if status == 'refuted' else 'STALE '} {prop}: marked "
                           f"{status} but concluded by {', '.join(found)}")
                bad += 1
            else:
                out.append(f"  ok     {prop}: {status}, no theorem concludes it")
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


def check_mirror(rows, mirror):
    """The duplicated table must agree, or the gate certifies the copy nobody reads."""
    lm = {p: st for p, st, _ in rows}
    mm = {p: st for p, st, _ in mirror}
    bad, out = 0, []
    for prop in sorted(set(lm) | set(mm)):
        if prop not in mm:
            out.append(f"  DRIFT  {prop}: in the Lean ledger, missing from CHANGELOG.md"); bad += 1
        elif prop not in lm:
            out.append(f"  DRIFT  {prop}: in CHANGELOG.md, missing from the Lean ledger"); bad += 1
        elif lm[prop] != mm[prop]:
            out.append(f"  DRIFT  {prop}: Lean says {lm[prop]}, "
                       f"CHANGELOG.md says {mm[prop]}"); bad += 1
    if not bad:
        out.append(f"  ok     CHANGELOG.md mirror agrees on all {len(mm)} rows")
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

    # 3. A dropped row in the changelog copy -- the drift that actually happened.
    a = [("SignHardCase", "open", ""), ("Depth3DecayHard", "open", "")]
    bad, out = check_mirror(a, a[:1])
    fired = bad == 1 and "DRIFT" in out[0]
    print(f"  canary 3 (row missing from the CHANGELOG copy)  {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 4. A refuted row that something proves anyway -- the contradiction case.
    bad, out = check_rows([("VarLeftEmlRightHard", "refuted", "")], decls)
    fired = bad == 1 and "CONTRA" in out[0]
    print(f"  canary 4 (refuted row proved anyway)           {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 5. A status that disagrees between the two copies.
    bad, out = check_mirror([("SignHardCase", "open", "")],
                            [("SignHardCase", "discharged", "")])
    fired = bad == 1 and "DRIFT" in out[0]
    print(f"  canary 5 (status disagrees across copies)      {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 5. And the true ledger must still pass, so the canaries are not just "everything fails".
    bad, _ = check_rows([("VarLeftEmlRightHard", "discharged", "`varLeftEmlRightHard_of_band`")],
                        decls)
    b2, _ = check_mirror(a, a)
    quiet = bad == 0 and b2 == 0
    print(f"  canary 6 (correct rows stay silent)            {'SILENT' if quiet else 'FIRES'}")
    ok &= quiet

    print()
    if not ok:
        print("LEDGER SELF-TEST FAIL — a canary did not fire; the gate is unvalidated")
        return 1
    print("LEDGER SELF-TEST PASS — all five convict specimens fire")
    return 0


def main() -> int:
    if not LEDGER.exists():
        print(f"UNAVAILABLE: {LEDGER} not found", file=sys.stderr)
        return 2
    rows = parse_rows(LEDGER.read_text())
    if not rows:
        print("UNAVAILABLE: no ledger rows parsed — has the table format changed?", file=sys.stderr)
        return 2
    if not CHANGELOG.exists():
        print(f"UNAVAILABLE: {CHANGELOG} not found", file=sys.stderr)
        return 2
    mirror = parse_rows(CHANGELOG.read_text())
    if not mirror:
        print("UNAVAILABLE: no rows parsed from CHANGELOG.md's ledger copy", file=sys.stderr)
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

    dbad, dout = check_mirror(rows, mirror)
    bad += dbad
    for line in dout:
        print(line)

    print()
    if bad:
        print(f"OBLIGATION-LEDGER FAIL — {bad}/{len(rows)} row(s) do not match the corpus")
        return 1
    print(f"OBLIGATION-LEDGER OK — {len(rows)} rows match the corpus and the CHANGELOG mirror")
    return 0


if __name__ == "__main__":
    sys.exit(main())
