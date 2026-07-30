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
    ("ledger", 3, [PY, "tools/axiom_ledger/check_ledger.py"]),
    ("derivable", 4, [PY, "tools/axiom_ledger/check_derivable.py"]),
    ("sorry_audit", 5, ["lake", "env", "lean", "tools/sorry_audit.lean"]),
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


def compare(cur: dict, base_dir: str) -> int:
    base = json.load(open(os.path.join(base_dir, "verdict.json")))
    print(f"\n{'='*78}\nCOMPARE  {base['toolchain']}  ->  {cur['toolchain']}\n{'='*78}")

    code, out = sh([PY, "tools/axiom_ledger/footprint_snapshot.py", "--diff",
                    os.path.join(base_dir, "footprints.json"),
                    os.path.join(SNAPS, cur["label"], "footprints.json")])
    print(out.strip())

    drift = [f"{k}: {base['counts'][k]} -> {cur['counts'][k]}"
             for k in COUNTS if base["counts"].get(k) != cur["counts"].get(k)]
    print(f"\ncount equality vs baseline: {'PASS' if not drift else 'FAIL'}")
    for d in drift:
        print(f"  ~ {d}")

    fails = [n for n, _, _ in GATES if cur["gates"][n] != 0]
    print(f"gates green: {'PASS' if not fails else 'FAIL — ' + ', '.join(fails)}")

    ok = code == 0 and not drift and not fails
    print(f"\n{'='*78}")
    if ok:
        print("STOP ACCEPTED — same theorems, same axioms, same trust boundary, newer kernel.")
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
    a = ap.parse_args()

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

    verdict = {"label": a.label, "captured_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
               "toolchain": toolchain, "lock": lock,
               "gates": codes, "counts": counts,
               "footprints": {"enumerated": fp.get("enumerated"), "captured": fp.get("captured"),
                              "missing": fp.get("missing", [])},
               "instrument_errors": errs}
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

    rc = compare(verdict, a.compare_to) if a.compare_to else 0
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
