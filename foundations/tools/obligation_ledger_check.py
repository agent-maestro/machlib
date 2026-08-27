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
import os
import re
import subprocess
import sys
import tempfile
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
                if c in ("**open**", "**discharged**", "**refuted**", "**reduced**",
                         "**assumed**")]
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


def conclusion_of(sig):
    """The tail after the binder/conclusion separator — the FIRST colon at bracket depth 0.

    `rsplit(":", 1)` was used here and its comment claimed "the last top-level `:`". It is not
    top-level aware, and a **type ascription inside the conclusion** breaks it:

        theorem pIrred_X : PIrred ([0, 1] : List Real)

    splits at the ascription's colon and yields `List Real)`, so the theorem does not read as
    concluding `PIrred` and the corpus's only `PIrred` construction was invisible. Found 2026-08-27
    by `tools/hypothesis_audit.py`, which reported `PIrred` as consumed-and-never-produced.

    The FIRST depth-0 colon is the right one, not the last: binders are always bracketed, so the
    separator is the first colon outside brackets, and a `∀ x : T,` *inside* the conclusion then
    cannot be mistaken for it either — which `rsplit` also got wrong.
    """
    depth = 0
    for i, ch in enumerate(sig):
        if ch in "([{":
            depth += 1
        elif ch in ")]}":
            depth -= 1
        elif ch == ":" and depth == 0:
            return sig[i + 1:]
    return sig


def refuters_of(prop, decls):
    """Theorems whose conclusion is `¬ prop` — what a "refuted" row must cite."""
    out = []
    for kind, name, sig in decls:
        if not kind.endswith("theorem"):
            continue
        tail = conclusion_of(sig).strip()
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
        tail = conclusion_of(stripped).strip()
        # An EQUIVALENCE is not a discharge. `foo : P ↔ Q` prefix-matches `P` and would otherwise be
        # counted as concluding it -- which is how a reduction reads as a solution. Found 2026-08-24
        # when `signHardCase_iff_compareExpExpPos` silently made canary 5 stop firing.
        if "↔" in tail:
            continue
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


def reduction_cycles(rows):
    """Cycles in the reduction graph.

    A `reduced` row is honest bookkeeping: the obligation now rests on a residue that is itself
    tracked. But if the residue chain comes back round, **nothing has been reduced** — the rows are
    one obligation written several ways, and every one of them is still open.

    No per-row check can see this. Each row in a cycle passes all three reduction conditions: the
    cited theorem concludes the prop, it does assume the residue, and the residue is a real ledger
    row. The defect is in the graph, not in any row — which is exactly the shape of the failure the
    `reduced` status was introduced to make visible, one level up.

    Added 2026-08-26, when `DecayFloor` and `GrowthEnvelope` were proved equivalent and each became
    a legitimate reduction of the other. Without this the open column would have lost a row for a
    result that closed nothing.
    """
    known = {p for p, _, _ in rows}
    edge = {}
    for prop, status, cell in rows:
        if status != "reduced":
            continue
        named = re.findall(r"`([A-Za-z0-9_\']+)`", cell)
        residue = next((n for n in named if n in known and n != prop), None)
        if residue:
            edge[prop] = residue
    cycles = []
    for start in edge:
        node, path = start, []
        for _ in range(len(edge) + 1):
            if node not in edge:
                break
            path.append(node)
            node = edge[node]
            if node == start:
                if frozenset(path) not in [frozenset(c) for c in cycles]:
                    cycles.append(path)
                break
    return cycles


def proved_equivalences(rows, decls):
    """Pairs of ledger rows the corpus proves EQUIVALENT, as `(a, b, theorem)`.

    A proved `a ↔ b` between two rows means they are **one obligation written twice** — the same
    thing a reduction cycle means, arrived at by a different route. `reduction_cycles` cannot see
    it: it walks the residue edges of `reduced` rows, and an equivalence between two rows both
    marked `open` contributes no edge at all.

    Nor can `dischargers_of`, and that is deliberate — it skips any conclusion containing `↔`, so
    that `foo : P ↔ Q` does not read as a proof of `P` (canary 9). Correct, and it left an
    equivalence contributing *nothing* to any check rather than merely not contributing a
    discharge. Two mechanisms each declining to look at the same theorem is how the count went
    wrong.

    Found 2026-08-26: `towerReducesToSign_iff_towerLowerBound` has been in the corpus since
    `b5c9fd53`, and `EMLTowerAfterSign`'s own docstring says "two ledger rows that looked like
    separate debts are one debt stated twice" — while the ledger went on reporting two.

    CONDITIONAL equivalences do not count and are returned separately: `(h : X) : a ↔ b` says the
    rows agree *given `X`*, which collapses nothing until `X` is discharged. They are reported
    rather than dropped, because a silent skip is the defect this function exists to remove.
    """
    known = {p for p, _, _ in rows}
    uncond, cond = [], []
    for kind, name, sig in decls:
        if not kind.endswith("theorem"):
            continue
        tail = conclusion_of(sig)
        head = sig[:len(sig) - len(tail) - 1]
        m = re.fullmatch(r"([A-Za-z0-9_'.]+)\s*↔\s*([A-Za-z0-9_'.]+)", tail.strip())
        if not m:
            continue
        # strip the namespace prefix: rows are registered by bare name (`TowerLowerBound`), the
        # theorem may write `EMLTree.TowerLowerBound`.
        a, b = (g.rsplit(".", 1)[-1] for g in m.groups())
        if a == b or a not in known or b not in known:
            continue
        # any binder in the head makes the equivalence conditional
        binder = re.search(r"[\(\{\[][^\(\)\{\}\[\]]*:", head)
        (cond if binder else uncond).append((a, b, name))
    return uncond, cond


def open_units(rows, cycles, equivs):
    """The open obligations, grouped so each unit is ONE obligation however many rows carry it.

    A unit starts as either a whole reduction cycle (whose rows are `reduced`, each to the next,
    so nothing was reduced away) or a single `open` row. Units are then merged across proved
    equivalences. Rows that are `discharged`, `refuted`, or legitimately `reduced` along a linear
    chain to a tracked residue are not open and form no unit.

    The number of units is the honest debt; the total membership is the number of rows carrying
    it. Both are reported, because either alone is misreadable — see the note at the print site.
    """
    units = [set(c) for c in cycles]
    units += [{p} for p, st, _ in rows if st == "open"]
    merged = True
    while merged:
        merged = False
        for a, b, _ in equivs:
            ia = next((i for i, u in enumerate(units) if a in u), None)
            ib = next((i for i, u in enumerate(units) if b in u), None)
            if ia is not None and ib is not None and ia != ib:
                # pop the HIGHER index: popping the lower one first would shift the other, and the
                # merge would write into the wrong unit and leave a duplicate behind.
                lo, hi = min(ia, ib), max(ia, ib)
                units[lo] |= units.pop(hi)
                merged = True
                break
    return units


def check_equivalences(rows, uncond):
    """An equivalence to a SETTLED row settles the other side.

    `dischargers_of` skips `↔` conclusions, so a row proved equivalent to a discharged one is
    never marked stale by the per-row check — it reads as a perfectly good open row. That is the
    same blind spot as the miscount, in its dangerous direction: the miscount overstates the debt,
    this understates the corpus.
    """
    status = {p: st for p, st, _ in rows}
    bad, out = 0, []
    for a, b, thm in uncond:
        sa, sb = status.get(a), status.get(b)
        for x, sx, y, sy in ((a, sa, b, sb), (b, sb, a, sa)):
            if sx == "open" and sy in ("discharged", "refuted"):
                out.append(f"  STALE  {x}: marked open, but {thm} proves it equivalent to {y}, "
                           f"which is {sy}")
                bad += 1
        if {sa, sb} == {"discharged", "refuted"}:
            out.append(f"  CONTRA {a} ⟷ {b}: {thm} proves them equivalent, but one is discharged "
                       f"and the other refuted")
            bad += 1
    return bad, out


# ── The axiom half of "discharged" ──────────────────────────────────────────────────────────────
#
# Until 2026-08-26 this gate contained no reference to axioms, footprints or `sorryAx` at all, and
# the 2026-08-19 trust-boundary note (`exploration/signhardcase_trust_boundary_2026_08_19/NOTE.md`)
# recorded that as a live defect and an explicit PRECONDITION on ever importing an external
# assumption:
#
#   > if someone adds `axiom signHardCase_ax : SignHardCase` plus a one-line theorem concluding it,
#   > the obligations ledger will report the row as **discharged** — indistinguishable from a proof.
#   > The axiom ledger would separately surface the new axiom as footprint drift. But NO GATE JOINS
#   > THOSE TWO FACTS, and the misleading one is the one a reader reaches for.
#
# This joins them. Both halves of "discharged" are now checked: that a theorem concludes the
# proposition (above), and that the theorem is a PROOF rather than a restatement of an assumption.


def _lean(src: str) -> str:
    """Run a snippet against the built corpus. Returns combined output, or '' if it could not run."""
    fd, path = tempfile.mkstemp(suffix=".lean", dir=str(ROOT))
    try:
        with os.fdopen(fd, "w") as f:
            f.write(src)
        proc = subprocess.run(["lake", "env", "lean", os.path.relpath(path, str(ROOT))],
                              cwd=str(ROOT), capture_output=True, text=True, timeout=900)
        return proc.stdout + proc.stderr
    except Exception:
        return ""
    finally:
        os.unlink(path)


def cited_witness(prop, status, cell, decls):
    """The theorem a non-open row rests on, or None."""
    if status == "open":
        return None
    named = re.findall(r"`([A-Za-z0-9_\']+)`", cell)
    pool = refuters_of(prop, decls) if status == "refuted" else dischargers_of(prop, decls)
    return next((n for n in named if n in pool), None)


def footprints(names):
    """`#print axioms` for every witness, in ONE `lake env lean` run (~1 s for all of them).

    Returns `{name: set(axioms)}`; a name absent from the result did not resolve, and the caller
    must treat that as UNAVAILABLE rather than as a clean footprint. A gate that reads a failed
    Lean run as an empty axiom set would report every row as pristine exactly when it knows least.
    """
    if not names:
        return {}
    src = "import MachLib\n" + "".join(f"#print axioms MachLib.{n}\n" for n in names)
    out = _lean(src)
    got = {}
    for m in re.finditer(r"'([A-Za-z0-9_.\']+)' depends on axioms:\s*\[(.*?)\]", out, re.S):
        got[m.group(1).split(".")[-1]] = {a.strip() for a in m.group(2).split(",") if a.strip()}
    for m in re.finditer(r"'([A-Za-z0-9_.\']+)' does not depend on any axioms", out):
        got[m.group(1).split(".")[-1]] = set()
    return got


def axiom_types(axioms):
    """`#check` each axiom, in one run. Returns `{axiom: printed type}`."""
    if not axioms:
        return {}
    names = sorted(axioms)
    out = _lean("import MachLib\n" + "".join(f"#check @{a}\n" for a in names))
    got = {}
    for m in re.finditer(r"^([A-Za-z0-9_.\']+)\s*:\s*(.+)$", out, re.M):
        got[m.group(1)] = m.group(2).strip()
    return got


def check_footprints(rows, decls, fps, types):
    """A `discharged` row must be discharged by a PROOF.

    Three failures, and the second is the one the trust-boundary note is about:

      1. the witness could not be resolved at all — UNAVAILABLE, never a pass
      2. `sorryAx` anywhere in the footprint — the row says proved and nothing is
      3. an axiom in the footprint whose TYPE IS THE OBLIGATION — that is an assumption wearing a
         theorem's clothes. `axiom foo_ax : Foo` + `theorem foo_holds : Foo := foo_ax` passes every
         other check in this file. Such a row must be marked `assumed`, which is checked in
         `check_rows` and reports the axiom by name.
    """
    bad, out, unavailable = 0, [], False
    for prop, status, cell in rows:
        w = cited_witness(prop, status, cell, decls)
        if w is None:
            continue
        if w not in fps:
            out.append(f"  UNAVAIL {prop}: could not read the footprint of {w} — is the corpus built?")
            unavailable = True
            continue
        fp = fps[w]
        if "sorryAx" in fp:
            out.append(f"  SORRY  {prop}: {w} depends on sorryAx; the row claims {status}")
            bad += 1
        assumed = [a for a in sorted(fp)
                   if types.get(a, "").split(".")[-1] == prop]
        if assumed and status != "assumed":
            out.append(f"  ASSUMED {prop}: {w} rests on axiom {assumed[0]}, whose type IS {prop} — "
                       f"that is a disclosed assumption, not a proof; mark the row `assumed`")
            bad += 1
        elif status == "assumed":
            # Dots on purpose: axioms are cited fully qualified (`MachLib.foo_ax`), and the
            # identifier regex used everywhere else in this file stops at the dot. Accept either
            # the qualified name or its last component, so the row may write whichever reads better.
            named = re.findall(r"`([A-Za-z0-9_.\']+)`", cell)
            short = {n.split(".")[-1] for n in named}
            if not any(a in named or a.split(".")[-1] in short for a in assumed):
                out.append(f"  UNNAMED {prop}: marked assumed, but the row does not name the axiom "
                           f"it assumes (footprint offers {assumed or '(none)'})")
                bad += 1
            else:
                out.append(f"  ok     {prop}: ASSUMED — external, via axiom {assumed[0]}")
    return bad, out, unavailable


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
            # `discharged` and `assumed` share this half — a theorem must conclude the prop. What
            # separates them is the AXIOM half, in `check_footprints`: whether that theorem is a
            # proof or a restatement of an assumption.
            named = re.findall(r"`([A-Za-z0-9_\']+)`", discharger)
            hit = [n for n in named if n in found]
            if hit:
                out.append(f"  ok     {prop}: {status} by {hit[0]}")
            else:
                out.append(f"  BROKEN {prop}: marked {status}; "
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
    # SYNTHETIC specimen on purpose: this canary needs a prop NO theorem concludes, so it must
    # not name a live obligation. It named `SignHardCase`, and went silent the day a reduction
    # theorem concluded it. "refuted"/"discharged" specimens are only stable if the named prop
    # stays unconcluded -- which is a property of the CORPUS, not of the status label.
    bad, out = check_rows([("CanaryNeverConcludedProp", "refuted", "")], decls)
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

    # 7b. An EQUIVALENCE is not a discharge. `dischargers_of` matches the conclusion by PREFIX, so
    # `foo : P ↔ Q` would read as concluding `P` -- and a REDUCTION would read as a SOLUTION. This
    # is a direct unit test on synthetic declarations rather than a ledger row, because the defect
    # is in the matcher, not in any row. Found 2026-08-24: `signHardCase_iff_compareExpExpPos`
    # silently made canary 5 stop firing, which is how the rule got noticed at all.
    iff_decl  = [("theorem", "fake_iff",   "theorem fake_iff : CanaryProp ↔ SomethingElse")]
    bare_decl = [("theorem", "fake_bare",  "theorem fake_bare : CanaryProp")]
    fired = (dischargers_of("CanaryProp", iff_decl) == []
             and dischargers_of("CanaryProp", bare_decl) == ["fake_bare"])
    print(f"  canary 9 (an ↔ is not a discharge)             {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 8. And the true ledger must still pass, so the canaries are not just "everything fails".
    # A CORRECT reduced row is included: a new status that only ever fires is as useless as one
    # that never does, and this is the row the two specimens above are perturbations of.
    # These are LITERAL specimens, not a copy of the ledger, and the open row is DELIBERATELY a
    # name no theorem can ever conclude rather than a live obligation.
    #
    # It was a live one twice, and both broke on the same day: `BoundedEmlCellApproachLarge` stood
    # here until the router proved it (2026-08-18), and `Depth3DecayExp` replaced it and was
    # discharged hours later by the dispatch. Each time this canary fired and took the whole gate
    # down with it -- a self-test that fails because the corpus got BETTER is a bad self-test.
    #
    # CORRECTED 2026-08-24: the note here used to say the other three statuses are structurally
    # stable because "discharged and refuted rows do not revert". That is wrong, and canary 5 proved
    # it -- its specimen marked the LIVE obligation `SignHardCase` as "refuted", which fires only
    # while NO theorem concludes it. The day a reduction theorem concluded it, the canary went
    # silent and took the gate down. The stable property is not the status label: it is that the
    # named proposition stays unconcluded, which is a fact about the CORPUS. So no canary specimen
    # may name a live obligation, whatever status it is labelled with. So the open
    # specimen must not name one. A synthetic name exercises exactly the branch under control --
    # dischargers_of returns [] and the row must stay silent -- while canary 1 covers the other
    # branch with a real discharged proposition mislabelled open. Together they discriminate.
    bad, _ = check_rows([("VarLeftEmlRightHard", "discharged", "`varLeftEmlRightHard_of_band`"),
                         ("BoundedCellApproach", "reduced",
                          "`boundedCellApproach_of_eml` → `BoundedEmlCellApproach`"),
                         ("BoundedEmlCellApproach", "reduced",
                          "`boundedEmlCellApproach_of_large` → `BoundedEmlCellApproachLarge`"),
                         ("BoundedEmlCellApproachLarge", "discharged",
                          "`boundedEmlCellApproachLarge_holds`"),
                         ("SpecimenNeverConcluded", "open", "—")], decls)
    b2, _ = check_mirror(a, a)
    quiet = bad == 0 and b2 == 0
    print(f"  canary 10 (correct rows stay silent)          {'SILENT' if quiet else 'FIRES'}")
    ok &= quiet

    # 7c. A REDUCTION CYCLE. Two rows that reduce to each other pass every per-row check, and
    # would quietly leave the open column together. The specimen must also stay SILENT on a
    # legitimate linear chain, or it would just be "any reduction is suspicious".
    cyc = reduction_cycles([("CanaryA", "reduced", "`t1` → `CanaryB`"),
                            ("CanaryB", "reduced", "`t2` → `CanaryA`")])
    lin = reduction_cycles([("CanaryA", "reduced", "`t1` → `CanaryB`"),
                            ("CanaryB", "reduced", "`t2` → `CanaryC`"),
                            ("CanaryC", "discharged", "`t3`")])
    fired = len(cyc) == 1 and set(cyc[0]) == {"CanaryA", "CanaryB"} and lin == []
    print(f"  canary 11 (a reduction cycle reduces nothing)  {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7d. A PROVED EQUIVALENCE between two open rows. Same content as canary 11 — one obligation
    # written twice — reached by the other route, and the route no check was watching: an `↔` is
    # skipped by `dischargers_of` (canary 9, correctly) and contributes no residue edge for
    # `reduction_cycles` to walk, so before this it was seen by nothing at all.
    #
    # SYNTHETIC declarations on purpose. The live instance is
    # `towerReducesToSign_iff_towerLowerBound`, and naming it here would tie the canary to
    # `TowerLowerBound` staying open — the exact way canaries 5 and 10 broke, twice, on the corpus
    # getting better. What is under test is the mechanism, so the specimen owns its own decls.
    eq_decl = [("theorem", "fake_eq", "theorem fake_eq : CanaryA ↔ CanaryB")]
    rows_oo = [("CanaryA", "open", "—"), ("CanaryB", "open", "—")]
    uncond, _ = proved_equivalences(rows_oo, eq_decl)
    # and the discrimination: the SAME rows with no equivalence must stay two obligations, or the
    # check would only be saying that open rows are suspicious.
    fired = (len(uncond) == 1
             and len(open_units(rows_oo, [], uncond)) == 1
             and len(open_units(rows_oo, [], [])) == 2)
    print(f"  canary 12 (an ↔ between open rows is ONE debt) {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7e. An equivalence to a SETTLED row settles the other side. This is the same blind spot in
    # its dangerous direction: `dischargers_of` skips the `↔`, so a row proved equivalent to a
    # discharged one reads as a perfectly good open row and the corpus is understated.
    rows_od = [("CanaryA", "open", "—"), ("CanaryB", "discharged", "`fake_thm`")]
    ud, _ = proved_equivalences(rows_od, eq_decl)
    bad, out = check_equivalences(rows_od, ud)
    quiet, _ = check_equivalences(rows_oo, uncond)
    fired = (bad == 1 and any("STALE" in l and "CanaryA" in l for l in out) and quiet == 0)
    print(f"  canary 13 (↔ to a discharged row is STALE)    {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7f. A CONDITIONAL equivalence collapses NOTHING. `(h : X) : a ↔ b` says the rows agree given
    # `X`; until `X` is discharged they are still two debts. Without this the gate would merge rows
    # on the strength of a hypothesis nobody has supplied — which is precisely the failure
    # `assumes` exists to prevent one level down, and precisely the vacuity lesson of
    # `positive_branch_impossible`. It must still be REPORTED, not dropped: a silent skip is the
    # defect this whole family of checks exists to remove.
    cond_decl = [("theorem", "fake_cond", "theorem fake_cond (h : CanaryH) : CanaryA ↔ CanaryB")]
    uc, cc = proved_equivalences(rows_oo, cond_decl)
    fired = (uc == [] and len(cc) == 1 and len(open_units(rows_oo, [], uc)) == 2)
    print(f"  canary 14 (a conditional ↔ collapses nothing)  {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7g. AN ASSUMPTION WEARING A THEOREM'S CLOTHES. `axiom p_ax : P` plus
    # `theorem p_holds : P := p_ax` concludes `P`, cites no bad name, and passes every other check
    # in this file — the 2026-08-19 trust-boundary note flagged exactly this as the precondition on
    # ever importing an external assumption, and until today no gate joined "row says discharged" to
    # "witness rests on an axiom that IS the row".
    #
    # Synthetic footprints and types, passed in as arguments, so the specimen owns its whole world.
    a_decls = [("theorem", "canary_holds", "theorem canary_holds : CanaryProp")]
    a_rows  = [("CanaryProp", "discharged", "`canary_holds`")]
    a_fps   = {"canary_holds": {"MachLib.canary_ax"}}
    a_types = {"MachLib.canary_ax": "MachLib.CanaryProp"}
    bad, out, _ = check_footprints(a_rows, a_decls, a_fps, a_types)
    fired = bad == 1 and any("ASSUMED" in l for l in out)
    print(f"  canary 15 (an axiom typed as the row is not a proof) {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7h. A discharged row whose witness carries `sorryAx`.
    bad, out, _ = check_footprints(a_rows, a_decls, {"canary_holds": {"sorryAx"}}, {})
    fired = bad == 1 and any("SORRY" in l for l in out)
    print(f"  canary 16 (a discharged row resting on sorryAx)      {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7i. DISCRIMINATION, both ways. An ordinary axiom in the footprint must stay silent — nearly
    # every discharged row in this corpus depends on `MachLib.Real` and would otherwise fail — and a
    # correctly-marked `assumed` row that NAMES its axiom must stay silent too, or the new status
    # would be unusable the moment it was introduced.
    b1, _, _ = check_footprints(a_rows, a_decls, a_fps, {"MachLib.canary_ax": "MachLib.Something"})
    b2, o2, _ = check_footprints([("CanaryProp", "assumed", "`canary_holds` via `MachLib.canary_ax`")],
                                 a_decls, a_fps, a_types)
    b3, o3, _ = check_footprints([("CanaryProp", "assumed", "`canary_holds`")],
                                 a_decls, a_fps, a_types)
    fired = (b1 == 0 and b2 == 0 and any("ASSUMED — external" in l for l in o2)
             and b3 == 1 and any("UNNAMED" in l for l in o3))
    print(f"  canary 17 (discrimination: ordinary axiom vs named assumption) "
          f"{'FIRES' if fired else 'SILENT'}")
    ok &= fired

    # 7j. AN UNREADABLE FOOTPRINT IS NOT A CLEAN ONE. If the corpus is not built, `#print axioms`
    # resolves nothing — and a gate that read the empty result as "no axioms" would report every row
    # as pristine exactly when it knows least. It must exit 2. See the UNAVAILABLE rule.
    _, out, unavail = check_footprints(a_rows, a_decls, {}, {})
    fired = unavail and any("UNAVAIL" in l for l in out)
    print(f"  canary 18 (an unread footprint is UNAVAILABLE, not clean) {'FIRES' if fired else 'SILENT'}")
    ok &= fired

    print()
    if not ok:
        print("LEDGER SELF-TEST FAIL — a canary did not fire; the gate is unvalidated")
        return 1
    # No count here. It said "all ten" while eleven ran, because a literal in a message is a
    # snapshot that trains you to edit it rather than to re-derive it.
    print("LEDGER SELF-TEST PASS — every convict specimen fires")
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

    # The axiom half of "discharged". Two `lake env lean` runs, ~1 s each; this gate runs after
    # `lake build` in CI, and an unbuilt corpus must exit 2, not 0 — see check_footprints.
    wits = [w for w in (cited_witness(p_, st, cell, decls) for p_, st, cell in rows) if w]
    fps = footprints(wits)
    types = axiom_types({a for f in fps.values() for a in f})
    fbad, fout, funavail = check_footprints(rows, decls, fps, types)
    bad += fbad
    for line in fout:
        print(line)
    if funavail:
        print("UNAVAILABLE: witness footprints could not be read — run `lake build` first",
              file=sys.stderr)
        return 2
    # Printed even when nothing is wrong. A check that is silent on success is indistinguishable
    # from a check that did not run, and this one was absent entirely until today.
    print(f"  ok     witness footprints: {len(fps)} of {len(wits)} read, "
          f"{len({a for f in fps.values() for a in f})} distinct axioms, no sorryAx")

    uncond, cond = proved_equivalences(rows, decls)
    ebad, eout = check_equivalences(rows, uncond)
    bad += ebad
    for line in eout:
        print(line)

    cycles = reduction_cycles(rows)
    for cyc in cycles:
        print(f"  CYCLE  {' ⇄ '.join(cyc)}: these reduce to each other, so none of them is reduced "
              f"away — all {len(cyc)} are OPEN")
    for a, b, thm in cond:
        print(f"  COND   {a} ⟷ {b}: {thm} is a CONDITIONAL equivalence — it collapses nothing "
              f"until its hypothesis is discharged")

    print()
    if bad:
        print(f"OBLIGATION-LEDGER FAIL — {bad}/{len(rows)} row(s) do not match the corpus")
        return 1
    print(f"OBLIGATION-LEDGER OK — {len(rows)} rows match the corpus and the CHANGELOG mirror")

    # A row is not an obligation. A reduction cycle and a proved equivalence each mean "one
    # obligation written several ways", so both counts are printed: the row count would inflate
    # the debt, the obligation count alone would hide that the ledger carries several rows for it.
    # Neither number is readable without the other.
    units = open_units(rows, cycles, uncond)
    open_rows = sum(len(u) for u in units)
    for u in sorted(units, key=lambda u: sorted(u)):
        if len(u) > 1:
            print(f"  ONE    {' ⟷ '.join(sorted(u))}: {len(u)} rows, ONE open obligation")
    print(f"  open rows: {open_rows}")
    print(f"  distinct open obligations: {len(units)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
