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
        stat = [c for c in cells
                if c in ("**open**", "**discharged**", "**refuted**", "**reduced**")]
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


def refuters_of(prop, decls):
    """Theorems whose conclusion is `¬ prop` — what a "refuted" row must cite."""
    out = []
    for kind, name, sig in decls:
        if not kind.endswith("theorem"):
            continue
        tail = sig.rsplit(":", 1)[-1].strip()
        if re.match(r"^¬\s*" + re.escape(prop) + r"\b", tail):
            out.append(name)
    return out


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


def assumes(name, residue, decls):
    """Does theorem `name` take a hypothesis of type `residue`?

    This is what separates a REDUCTION from a DISCHARGE. `dischargers_of` deliberately strips
    binders of the obligation's own type, so a *consumer* of `P` cannot masquerade as a proof of
    `P`. But a theorem `(h : Residue) : P` concludes `P` while depending on a different, still-open
    proposition — it passes `dischargers_of` unchanged and would be recorded as an unconditional
    proof. That is the exact shape of an illegitimate composition: two individually true facts
    ("this theorem concludes P" and "P has a ledger row") combining into a false one ("P is proved").
    """
    for _kind, nm, sig in decls:
        if nm != name:
            continue
        return re.search(r"\([^()]*:\s*" + re.escape(residue) + r"\s*\)", sig) is not None
    return False


def check_rows(rows, decls):
    """Returns (bad_count, report_lines). Shared by the gate and its self-test."""
    bad, out = 0, []
    for prop, status, discharger in rows:
        found = dischargers_of(prop, decls)
        if status == "refuted":
            # A theorem concluding P would contradict the row; and the row must be BACKED by a
            # theorem concluding ¬P, otherwise "refuted" is just an assertion with extra confidence.
            refs = refuters_of(prop, decls)
            if found:
                out.append(f"  CONTRA {prop}: marked refuted but concluded by {', '.join(found)}")
                bad += 1
            elif not refs:
                out.append(f"  UNBACKED {prop}: marked refuted, but no theorem concludes ¬{prop}")
                bad += 1
            else:
                out.append(f"  ok     {prop}: refuted by {refs[0]}")
        elif status == "open":
            if found:
                out.append(f"  STALE  {prop}: marked open but discharged by {', '.join(found)}")
                bad += 1
            else:
                out.append(f"  ok     {prop}: open, no theorem concludes it")
        elif status == "reduced":
            # A reduction is NOT a discharge. Three conditions, and dropping any one of them lets
            # an open problem read as solved:
            #   1. the cited theorem really concludes `prop`      (else nothing was shown at all)
            #   2. it really assumes the cited residue            (else it IS a discharge, or the
            #      row names a residue the proof never used)
            #   3. the residue is itself a ledger row             (else the obligation was reduced
            #      to something nobody tracks, which is how debt disappears)
            named = re.findall(r"`([A-Za-z0-9_\']+)`", discharger)
            known = {p for p, _, _ in rows}
            thm = next((n for n in named if n in found), None)
            residue = next((n for n in named if n != thm), None)
            if thm is None:
                out.append(f"  BROKEN {prop}: marked reduced; cited {named or '(none)'}, "
                           f"actual dischargers {found or '(none)'}")
                bad += 1
            elif residue is None:
                out.append(f"  MALFORMED {prop}: marked reduced but names no residue; the row must "
                           f"cite both the reducing theorem and what it reduces to")
                bad += 1
            elif not assumes(thm, residue, decls):
                out.append(f"  UNCONDITIONAL {prop}: {thm} concludes it without assuming {residue} "
                           f"— that is a discharge, not a reduction")
                bad += 1
            elif residue not in known:
                out.append(f"  UNTRACKED {prop}: reduced to {residue}, which has no ledger row")
                bad += 1
            else:
                out.append(f"  ok     {prop}: reduced by {thm} to {residue}")
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

    # 4b. A refuted row with no refutation theorem behind it.
    bad, out = check_rows([("SignHardCase", "refuted", "")], decls)
    fired = bad == 1 and "UNBACKED" in out[0]
    print(f"  canary 5 (refuted row with no ¬-theorem)      {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 5. A status that disagrees between the two copies.
    bad, out = check_mirror([("SignHardCase", "open", "")],
                            [("SignHardCase", "discharged", "")])
    fired = bad == 1 and "DRIFT" in out[0]
    print(f"  canary 6 (status disagrees across copies)      {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 6. A REDUCED row whose reducer does not actually assume the residue. This is the specimen
    # that matters most for the new status: `expExpGapBelow_holds` concludes `ExpExpGapBelow`
    # unconditionally, so calling it a "reduction to BoundedCellApproach" is a lie the previous
    # gate could not see -- the theorem does conclude the prop, and the residue is a real row.
    bad, out = check_rows([("ExpExpGapBelow", "reduced",
                            "`expExpGapBelow_holds` → `BoundedCellApproach`")], decls)
    fired = bad == 1 and any("UNCONDITIONAL" in l for l in out)
    print(f"  canary 7 (reduced row that is really a discharge) {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7. A REDUCED row whose residue is not tracked anywhere. Without this check an obligation can
    # be "reduced" into a proposition nobody has a row for, and the debt silently leaves the ledger.
    # The row is otherwise CORRECT -- the reducer does assume this residue -- so the specimen
    # isolates the registration check rather than tripping the UNCONDITIONAL branch first.
    bad, out = check_rows([("BoundedCellApproach", "reduced",
                            "`boundedCellApproach_of_eml` → `BoundedEmlCellApproach`")], decls)
    fired = bad == 1 and any("UNTRACKED" in l for l in out)
    print(f"  canary 8 (reduced to an unregistered residue)  {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 8. And the true ledger must still pass, so the canaries are not just "everything fails".
    # A CORRECT reduced row is included: a new status that only ever fires is as useless as one
    # that never does, and this is the row the two specimens above are perturbations of.
    # NOTE: these are LITERAL specimens, not a copy of the ledger, and the open row has to be
    # repointed whenever the obligation it names is discharged -- `BoundedEmlCellApproachLarge`
    # stood here until the router proved it on 2026-08-18, at which point this canary fired and
    # the whole self-test failed. That is the specimen doing its job, but the lesson is that the
    # open row must name an obligation with no proof in sight, not merely one open today.
    bad, _ = check_rows([("VarLeftEmlRightHard", "discharged", "`varLeftEmlRightHard_of_band`"),
                         ("BoundedCellApproach", "reduced",
                          "`boundedCellApproach_of_eml` → `BoundedEmlCellApproach`"),
                         ("BoundedEmlCellApproach", "reduced",
                          "`boundedEmlCellApproach_of_large` → `BoundedEmlCellApproachLarge`"),
                         ("BoundedEmlCellApproachLarge", "discharged",
                          "`boundedEmlCellApproachLarge_holds`"),
                         ("Depth3DecayExp", "open", "—")], decls)
    b2, _ = check_mirror(a, a)
    quiet = bad == 0 and b2 == 0
    print(f"  canary 9 (correct rows stay silent)            {'SILENT' if quiet else 'FIRES'}")
    ok &= quiet

    print()
    if not ok:
        print("LEDGER SELF-TEST FAIL — a canary did not fire; the gate is unvalidated")
        return 1
    print("LEDGER SELF-TEST PASS — all eight convict specimens fire")
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
