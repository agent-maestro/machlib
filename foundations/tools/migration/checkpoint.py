"""CHECKPOINT: capture one toolchain-migration stop, freeze it, and decide acceptance.

## What this is

`BUMP_PLAN.md` fixes a six-criterion pass bar for every stop on
`v4.14.0 → v4.16.0 → v4.19.0 → v4.20.1 → v4.23.0 → v4.26.0`. This script *is* that pass bar,
executable: it runs all six gates, captures the 57 headline footprints, records the counts, hashes
the lot, and — given a `--compare-to` — prints ACCEPT or HALT.

The same instrument captures the *before* and every *after*. That is deliberate: a baseline measured
by one tool and compared by another is two instruments, and the difference between them shows up as a
finding that isn't one.

    python3 tools/migration/checkpoint.py --label v4.14.0-baseline --freeze
    ... bump the pin, rebuild ...
    python3 tools/migration/checkpoint.py --label v4.16.0 --compare-to snapshots/v4.14.0-baseline
    python3 tools/migration/checkpoint.py --verify snapshots/v4.14.0-baseline

## Counts come from cross-derivation, never from inspection

House rule, in its third and final form after the extractor incident of 2026-07-29 (a bracket-parse
bug enumerated 122 garbage names and *still* produced the right 57 footprints, because the junk
contributed none — the output was correct and the mechanism was broken, and only an independently
derived 57 could tell those apart):

> **A count is trustworthy when two derivations that share no code agree on it.** Not when it looks
> right, and not when one careful reader checked it.

So the 57 is asserted three ways here, and disagreement is an INSTRUMENT FAILURE that halts the stop
before any footprint is even compared:

  * `enumerated` — Python bracket-parse of `AxiomLedger.headlines`
  * `captured`   — the kernel's own `collectAxioms`, via `#print axioms`
  * `headline_footprints` — the Lean-side ledger gate's independent count

Likewise every other count (252 axioms, 5 derivations, 2 allowlisted `sorryAx`) is **parsed from the
gate that derived it** and compared against **the baseline's recorded value** — never against a
literal in this file. Hardcoding them would make this script a fourth place for the numbers to rot.

## A failed criterion is a FINDING, not a diff to accept

Eighteen versions of elaborator drift will produce at least one surprise. HALT means the step does
not advance until the delta is *attributed* — named cause, in the log, at the version that introduced
it. `--compare-to` prints the attribution aid (which theorem, which axioms moved) and exits 1. There
is deliberately no `--accept-anyway`: the only way past a footprint change is to understand it and
say so in the record.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import stat
import subprocess
import sys
import time

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SNAPS = os.path.join(FOUND, "snapshots")
PY = sys.executable
ANSI = re.compile(r"\x1b\[[0-9;]*m")

# criterion numbers refer to BUMP_PLAN.md's pass-bar table
GATES = [
    ("kernel_replay", 1, [PY, "tools/axiom_ledger/check_kernel_replay.py"]),
    # Criterion 7 joined at stop 3 (v4.20.1) -- at a stop BOUNDARY, before this pin's first capture,
    # per "an instrument does not join a measurement midway". Its trigger (Lean4Lean's maiden run
    # firing in both directions) was met at v4.19.0. Grade is "second implementation, shared lineage",
    # NOT "independent kernel" -- see BUMP_PLAN.md Amendment 2.
    ("lean4lean_replay", 7, [PY, "tools/axiom_ledger/check_lean4lean_replay.py"]),
    ("ledger", 3, [PY, "tools/axiom_ledger/check_ledger.py"]),
    ("derivable", 4, [PY, "tools/axiom_ledger/check_derivable.py"]),
    ("sorry_audit", 5, ["lake", "env", "lean", "tools/sorry_audit.lean"]),
    # ORDER IS LOAD-BEARING: criterion 7 PLANTS a compiled proof of `False` (lean4checker's AddFalse
    # specimen) and removes it again, and criterion 6 is the ONLY gate that would catch a failed
    # cleanup -- the smuggled declaration sits at the root namespace, so the ledger's prefix-filtered
    # axiom enumeration misses it; nothing depends on it, so no footprint moves; and it is not a
    # `sorry`. This is not hypothetical: the cleanup DID fail once (wrong olean path), leaving
    # `MachLib/ZZZSpecimenAddFalse.olean` in the build tree. Keep artifact_drift AFTER lean4lean_replay.
    ("artifact_drift", 6, [PY, "tools/axiom_ledger/check_artifact_drift.py"]),
    ("toolchain", 0, [PY, "tools/axiom_ledger/check_toolchain.py"]),
]

# count name -> (gate it is parsed from, regex, human label)
COUNTS = {
    "axioms_pinned": ("ledger", r"(\d+) axioms pinned", "axioms pinned"),
    "headline_footprints": ("ledger", r"(\d+) headline footprints", "headline footprints (Lean side)"),
    "derivations": ("derivable", r"derivableAxioms: (\d+) entr", "derivations"),
    "sorry_decls": ("sorry_audit", r"(\d+) sorryAx decls", "allowlisted sorryAx decls"),
}


def sh(cmd: list[str]) -> tuple[int, str]:
    p = subprocess.run(cmd, cwd=FOUND, capture_output=True, text=True)
    return p.returncode, ANSI.sub("", p.stdout + p.stderr)


def run_gates(logs: str) -> tuple[dict[str, int], dict[str, str]]:
    codes, outs = {}, {}
    for name, crit, cmd in GATES:
        print(f"  [{name}] ", end="", flush=True)
        code, out = sh(cmd)
        codes[name], outs[name] = code, out
        open(os.path.join(logs, f"{name}.log"), "w").write(out)
        print(f"exit {code}" + ("" if crit == 0 else f"   (criterion {crit})"))
    return codes, outs


def capture_footprints(target: str, logs: str) -> dict:
    print("  [footprints] ", end="", flush=True)
    p = subprocess.run([PY, "tools/axiom_ledger/footprint_snapshot.py"], cwd=FOUND,
                       capture_output=True, text=True)
    open(os.path.join(target, "footprints.json"), "w").write(p.stdout)
    open(os.path.join(logs, "footprints.log"), "w").write(ANSI.sub("", p.stderr))
    if p.returncode != 0:
        print(f"exit {p.returncode} — EXTRACTOR FAILED")
        return {}
    fp = json.loads(p.stdout)
    print(f"enumerated {fp['enumerated']}, captured {fp['captured']}, "
          f"missing {len(fp['missing'])}   (criterion 2)")
    return fp


def parse_counts(outs: dict[str, str]) -> tuple[dict[str, int | None], list[str]]:
    counts: dict[str, int | None] = {}
    errs = []
    for key, (gate, rx, label) in COUNTS.items():
        m = re.search(rx, outs.get(gate, ""))
        counts[key] = int(m.group(1)) if m else None
        if not m:
            errs.append(f"count '{label}' NOT EXTRACTED from {gate} — a count that cannot be "
                        f"derived is an instrument failure, not a zero")
    return counts, errs


def cross_derive_57(fp: dict, counts: dict[str, int | None]) -> list[str]:
    """The three-way agreement. Disagreement halts before any comparison is attempted."""
    a, b, c = fp.get("enumerated"), fp.get("captured"), counts.get("headline_footprints")
    if None in (a, b, c):
        return [f"headline count incomplete: enumerated={a} captured={b} lean_gate={c}"]
    if not a == b == c:
        return [f"HEADLINE COUNT DISAGREEMENT: bracket-parse={a}, kernel collectAxioms={b}, "
                f"Lean ledger gate={c} — three derivations, no majority vote available; the "
                f"instrument is wrong before the migration is"]
    if fp.get("missing"):
        return [f"{len(fp['missing'])} headline(s) enumerated with no footprint captured: "
                f"{fp['missing'][:8]}"]
    return []


def write_hashes(target: str) -> str:
    lines = []
    for root, _, files in sorted(os.walk(target)):
        for f in sorted(files):
            if f == "SHA256SUMS":
                continue
            p = os.path.join(root, f)
            h = hashlib.sha256(open(p, "rb").read()).hexdigest()
            lines.append(f"{h}  {os.path.relpath(p, target)}")
    body = "\n".join(lines) + "\n"
    open(os.path.join(target, "SHA256SUMS"), "w").write(body)
    return hashlib.sha256(body.encode()).hexdigest()


def freeze(target: str) -> None:
    for root, dirs, files in os.walk(target):
        for f in files:
            os.chmod(os.path.join(root, f), stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
        for d in dirs:
            os.chmod(os.path.join(root, d), 0o555)
    os.chmod(target, 0o555)


def verify(target: str) -> int:
    sums = os.path.join(target, "SHA256SUMS")
    if not os.path.exists(sums):
        print(f"[NOT_FROZEN] {target} has no SHA256SUMS — nothing to verify against")
        return 1
    bad = []
    for line in open(sums):
        want, rel = line.split("  ", 1)
        p = os.path.join(target, rel.strip())
        if not os.path.exists(p):
            bad.append(f"MISSING {rel.strip()}")
        elif hashlib.sha256(open(p, "rb").read()).hexdigest() != want:
            bad.append(f"CHANGED {rel.strip()}")
    print(f"{target}: {len(open(sums).readlines())} files hashed")
    for b in bad:
        print(f"  {b}")
    print("BASELINE INTEGRITY: " + ("PASS — the before is the before"
                                    if not bad else "FAIL — the baseline moved under the migration"))
    return 1 if bad else 0


# BUMP_PLAN.md Amendment 4. A gate can fail for two reasons that are not the same reason: it found
# something wrong with US, or it could not testify at all. Before this, `fails` was every non-zero
# exit, so the acceptance instrument had words for CONVICTED and ACQUITTED and none for UNMEASURABLE
# -- the same asymmetry the reason-code registry had, one layer up, surfacing the moment a gate broke
# in a way no re-run could repair (stop 5: no Lean4Lean build at v4.26.0 can replay `Init.Core`).
#
# THE NO-LAUNDERING CLAUSE IS THE POINT. An exit that does not halt the migration is the exit every
# future instrument hiccup will drift toward, until REPLAY_FAIL arrives dressed as INSTRUMENT_UNUSABLE
# and the weakest verdict is also the cheapest to claim. Three properties prevent that, and none is
# sufficient alone:
#   1. VOID binds to signatures the gate emits ABOUT ITSELF -- never to an exit code, never to
#      anything the operator supplies on the command line.
#   2. The authorising amendment is cited and lands in verdict.json. A void nobody signed for does
#      not exist; one that someone signed for names them.
#   3. Subject-defect verdicts are PERMANENTLY INELIGIBLE. There is no flag, for anyone, that turns
#      REPLAY_FAIL or a footprint drift into a void.
# The weaker acceptance is therefore expensive to claim, and that expense IS the mechanism. A bar
# that can be lowered cheaply is not a bar.
VOID_CODES = ("[INSTRUMENT_UNUSABLE]", "[INSTRUMENT_ABSENT]",
              "[INSTRUMENT_UNVALIDATED]", "[VERSION_MISMATCH]", "[CHECKER_ABSENT]",
              "[CHECKER_VERSION_MISMATCH]")

def declared_code(out: str) -> str | None:
    """The reason code the gate DECLARED, read from its structured verdict — never from its prose.

    CLASSIFY BY DECLARATION, NOT BY SUBSTRING. The first version of this function searched the whole
    output for the token, and misfiled a genuine `INSTRUMENT_UNUSABLE` as a subject failure because
    the gate's *explanatory text* contains the sentence "and REPLAY_FAIL is the most expensive
    verdict here". The gate was warning about the very mistake the reader then made — which is the
    third time on this route that a classifier has been fooled by text that merely mentions a verdict.

    Two shapes, both LINE-ANCHORED, matching how the gates actually emit:
        `<NAME> GATE: FAIL [CODE -- ...]`   the summary, when the gate reached its summary
        `[CODE] ...`                        an early exit, printed at line start, no summary reached
    A code appearing anywhere else is discussion, and discussion is not a verdict.
    """
    summary = None
    for line in out.splitlines():
        s = line.strip()
        if " GATE:" in s:
            summary = s                      # last summary line wins; gates print exactly one
        elif s.startswith("[") and "]" in s and not summary:
            m = re.match(r"\[([A-Z_]+)\]", s)
            if m:
                return m.group(1)
    if summary:
        m = re.search(r"\[([A-Z_]+)", summary)
        return m.group(1) if m else None      # `GATE: FAIL` with no code = a verdict about US
    return None


def classify_failures(codes: dict[str, int], outs: dict[str, str]) -> tuple[list[str], dict[str, str]]:
    """Split non-zero gates into genuine FAILS and instrument VOIDs, by what the gate DECLARED.

    Anything that is not an explicitly declared void code is a FAIL. That default direction is
    load-bearing: an unrecognised failure must never drift toward the exit that does not halt.
    """
    fails, voids = [], {}
    for name, _, _ in GATES:
        if codes.get(name, 0) == 0:
            continue
        code = declared_code(outs.get(name, ""))
        if code and f"[{code}]" in VOID_CODES:
            voids[name] = code
        else:
            fails.append(name)
    return fails, voids


def compare(cur: dict, base_dir: str, void_ok: dict[str, str] | None = None) -> int:
    base = json.load(open(os.path.join(base_dir, "verdict.json")))
    print(f"\n{'='*78}\nCOMPARE  {base['toolchain']}  ->  {cur['toolchain']}\n{'='*78}")

    code, out = sh([PY, "tools/axiom_ledger/footprint_snapshot.py", "--diff",
                    os.path.join(base_dir, "footprints.json"),
                    os.path.join(SNAPS, cur["label"], "footprints.json")])
    print(out.strip())

    # AUDITED AMENDMENTS. A count that was WRONG must be correctable without either rewriting a frozen
    # baseline or disabling this comparison -- so `snapshots/count_amendments.json` records from/to plus
    # the evidence, and a MATCHING entry is reported as amended rather than as drift. Anything unlisted
    # still halts the stop; this is an audit trail, not an override flag.
    amend_path = os.path.join(SNAPS, "count_amendments.json")
    amendments = json.load(open(amend_path)) if os.path.exists(amend_path) else {}
    drift, amended = [], []
    for k in COUNTS:
        b, c = base["counts"].get(k), cur["counts"].get(k)
        if b == c:
            continue
        match = next((a for a in amendments.get(k, []) if a.get("from") == b and a.get("to") == c), None)
        if match:
            amended.append((k, b, c, match))
        else:
            drift.append(f"{k}: {b} -> {c}")
    print(f"\ncount equality vs baseline: {'PASS' if not drift else 'FAIL'}")
    for d in drift:
        print(f"  ~ {d}  (UNLISTED -- no amendment on file)")
    for k, b, c, a in amended:
        print(f"  ~ {k}: {b} -> {c}  AMENDED {a['date']}: {a['reason'][:80]}...")
        print(f"      not_a_drift: {a.get('not_a_drift', '')[:96]}")

    # A voided gate must be counted ONCE, as a void. The first version defaulted `fails` to "every
    # non-zero exit" whenever the key was absent -- and the key is absent precisely when there are no
    # fails, so a cleanly-voided stop recomputed the void back into `fails` and halted itself while
    # printing the citation that authorised it. Read the classification from the snapshot when the
    # snapshot HAS one; only fall back for records written before Amendment 4 existed.
    if "voids" in cur or "fails" in cur:
        fails, voids = cur.get("fails", []), cur.get("voids", {})
    else:
        fails, voids = [n for n, _, _ in GATES if cur["gates"][n] != 0], {}
    void_ok = void_ok or {}
    print(f"gates green: {'PASS' if not fails else 'FAIL — ' + ', '.join(fails)}")

    # A void halts unless its authorising amendment is cited. Citing it does not make the criterion
    # green -- it records that the hole is known, named, and signed for.
    unjustified = [g for g in voids if g not in void_ok]
    for g, reason in sorted(voids.items()):
        cite = void_ok.get(g)
        print(f"gate VOID: {g} — {reason}" +
              (f"   [{cite} cited]" if cite else "   UNJUSTIFIED — cite the authorising amendment"))

    ok = code == 0 and not drift and not fails and not unjustified
    print(f"\n{'='*78}")
    if ok:
        print("STOP ACCEPTED — same theorems, same axioms, same trust boundary, newer kernel.")
        # GRADED acceptance. Stops measured by different-sized instruments do not get the same word:
        # flattening that difference claims an equivalence nobody measured. ONE acceptance path, so
        # the grade can never diverge from the exit code -- the first version gave the graded branch
        # its own prints and no `return 0`, and it printed ACCEPTED while returning 1. A verdict and
        # its exit code disagreeing is worse than either being wrong, because each is someone's
        # evidence: the log says accepted, the CI says halted, and both are quoting this function.
        for g, reason in sorted(voids.items()):
            crit = next((c for n, c, _ in GATES if n == g), "?")
            print(f"  GRADE: criterion {crit} UNMEASURED — {reason}, {void_ok[g]} cited.")
        if voids:
            print("  This acceptance permanently carries the shape of its evidence. It is upgradeable")
            print("  as new-evidence-about-old-stops if the instrument question is later answered —")
            print("  which is possible ONLY because the grade preserved what was missing.")
        print("This stop is now a fallback position: commit it before touching the next pin.")
        # ARCHIVE BEFORE HYGIENE: the next stop's `lake clean` destroys this tree, and with it the
        # only thing that can answer "did X get slower across this stop". Reminder, not a gate.
        prof = os.path.join(SNAPS, "timing", cur["toolchain"].split(":")[-1] + ".json")
        if not os.path.exists(prof):
            print("\n[NO TIMING BASELINE for this pin] Before advancing, run:")
            print("    python3 tools/migration/timing_profile.py")
            print("  The next `lake clean` destroys this tree. Stop 1 learned that the hard way:")
            print("  correct hygiene deleted the only tree that could answer whether a tactic got")
            print("  slower, turning a diff into a scheduled excavation.")
        return 0
    print("STOP HALTED — this is a FINDING, not a diff to accept.")
    print("  The step does not advance until every delta above is ATTRIBUTED: which change in")
    print("  which version caused it, written into the migration log. Two intermediates of")
    print("  drift is a searchable window; accepting it silently is how a migration becomes a mess.")
    return 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", help="stop name, e.g. v4.16.0 (writes snapshots/<label>/)")
    ap.add_argument("--compare-to", help="a frozen baseline directory to accept against")
    ap.add_argument("--freeze", action="store_true", help="hash + chmod read-only when done")
    ap.add_argument("--verify", help="re-check a frozen directory's SHA256SUMS and exit")
    # BUMP_PLAN.md Amendment 4. Repeatable: --void-ok lean4lean_replay=Amendment-3
    ap.add_argument("--void-ok", action="append", default=[], metavar="GATE=AMENDMENT",
                    help="accept a gate's INSTRUMENT VOID, citing the amendment that authorises it. "
                         "Cannot apply to a subject-defect verdict (REPLAY_FAIL, footprint drift).")
    a = ap.parse_args()
    void_ok = dict(kv.split("=", 1) for kv in a.void_ok if "=" in kv)

    if a.verify:
        return verify(a.verify)
    if not a.label:
        ap.error("--label is required unless --verify is given")

    target = os.path.join(SNAPS, a.label)
    if os.path.exists(os.path.join(target, "SHA256SUMS")):
        print(f"[FROZEN] {target} is already frozen. A stop is captured once; re-capturing would")
        print("         overwrite the record it exists to preserve. Pick a new --label.")
        return 1
    logs = os.path.join(target, "logs")
    os.makedirs(logs, exist_ok=True)

    toolchain = open(os.path.join(FOUND, "lean-toolchain")).read().strip()
    lock = open(os.path.join(FOUND, "TOOLCHAIN.lock")).read().split()
    print(f"CHECKPOINT {a.label}   pin={toolchain}   lock={lock[0]} @ {lock[1] if len(lock)>1 else '?'}\n")

    codes, outs = run_gates(logs)
    fp = capture_footprints(target, logs)
    counts, errs = parse_counts(outs)
    errs += cross_derive_57(fp, counts)

    fails, voids = classify_failures(codes, outs)
    verdict = {"label": a.label, "captured_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
               "toolchain": toolchain, "lock": lock,
               "gates": codes, "counts": counts,
               "footprints": {"enumerated": fp.get("enumerated"), "captured": fp.get("captured"),
                              "missing": fp.get("missing", [])},
               "instrument_errors": errs}
    # Amendment 4 fields are appended AFTER the pre-existing ones and only when non-empty, so a stop
    # with no voids serialises byte-identically to what the unmodified instrument wrote. The
    # amendment's own acceptance criterion depends on that.
    if fails:
        verdict["fails"] = fails
    if voids:
        verdict["voids"] = voids
        verdict["voids_cited"] = {g: void_ok[g] for g in voids if g in void_ok}
    open(os.path.join(target, "verdict.json"), "w").write(json.dumps(verdict, indent=1) + "\n")

    print("\ncounts (each parsed from the gate that derived it):")
    for k, (_, _, label) in COUNTS.items():
        print(f"  {label:<34} {counts[k]}")
    print(f"  {'headline count, 3 derivations':<34} "
          f"{fp.get('enumerated')} / {fp.get('captured')} / {counts['headline_footprints']}"
          f"  {'AGREE' if not errs else 'see instrument errors'}")

    if errs:
        print("\nINSTRUMENT FAILURE — comparison NOT attempted:")
        for e in errs:
            print(f"  * {e}")
        return 1

    rc = compare(verdict, a.compare_to, void_ok) if a.compare_to else 0
    if a.compare_to is None:
        print("\nno --compare-to: captured as a reference point, nothing accepted or rejected.")

    if a.freeze:
        h = write_hashes(target)
        freeze(target)
        print(f"\nFROZEN  {target}\n  SHA256SUMS digest: {h}")
        print("  read-only on disk; `--verify` re-checks it. Note that later stops diff against the")
        print("  v4.14.0 BASELINE, not against this -- chaining comparisons through intermediates")
        print("  would let a drift launder itself across two of them.")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
