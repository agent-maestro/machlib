#!/usr/bin/env python3
"""prose_counts_check.py — every tracked number in prose must equal what the corpus measures.

WHY THIS EXISTS (2026-09-05). CLAUDE.md has carried the policy "no count in prose may be written
from memory; run the gate, read its number, paste it" since 2026-08-31, and the policy was still
being broken by the documents that stated it: what_is_proven.md said the trusted base was 260
axioms for ten weeks after the ledger said 243, CLAUDE.md's architecture paragraph was sixteen
files and eighty theorems stale, and two earlier revisions of CLAUDE.md carried theorem counts
nobody could reproduce. A policy nothing checks is a wish. This gate checks it.

WHAT IT CHECKS. `tools/prose_counts.json` registers claims: a prose file, a regex whose capture
group is the number as written, and a source. Sources are evaluated once against the live tree —
a shell command run from foundations/ (the theorem-count command, the aggregator, the obligations
ledger, the axiom ledger), a pattern over a generated or measured artifact (AXIOM_MANIFEST.md,
the close-rate remeasurement), or a sum of other sources. Thousands separators are ignored.

VERDICTS. Every claim prints OK / DRIFT / UNAVAILABLE with both values, so the figures are visible
even when nothing is wrong. Exit 0 iff every claim is OK; exit 1 if any claim drifted; exit 2 if
any source or claim could not be evaluated and none drifted — UNAVAILABLE is not a pass.

WHAT IT CANNOT SEE. Only registered numbers. A figure typed into a document without a claim here
is exactly as unchecked as before; adding the number and the claim in the same change is the
discipline. It also cannot tell a correct number that names the wrong thing.

SELF-TEST (`--self-test`, in-memory, never writes into the tree): (1) a doctored copy of README.md
in a temp dir must FAIL; (2) an unmodified copy must PASS; (3) a registry whose source command
fails must report UNAVAILABLE, not PASS. All three must hold or the gate reports itself broken.
"""
from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent          # foundations/tools
FOUNDATIONS = HERE.parent                       # foundations/
ROOT = FOUNDATIONS.parent                       # repo root
REGISTRY = HERE / "prose_counts.json"

WORDS = {
    "zero": "0", "one": "1", "two": "2", "three": "3", "four": "4", "five": "5", "six": "6",
    "seven": "7", "eight": "8", "nine": "9", "ten": "10", "eleven": "11", "twelve": "12",
    "thirteen": "13", "fourteen": "14", "fifteen": "15", "sixteen": "16", "seventeen": "17",
    "eighteen": "18", "nineteen": "19", "twenty": "20",
}


def norm(s: str) -> str:
    """Strip thousands separators (space, NBSP, thin space, comma) so `7 568` == `7568`."""
    return re.sub(r"[\s  ,]", "", s)


class Sources:
    """Lazily evaluated, cached sources. A source yields a tuple of captured strings."""

    def __init__(self, registry: dict, foundations: Path, root: Path):
        self.defs = registry["sources"]
        self.foundations = foundations
        self.root = root
        self.cache: dict[str, tuple[tuple[str, ...] | None, str | None]] = {}

    def get(self, name: str) -> tuple[tuple[str, ...] | None, str | None]:
        if name in self.cache:
            return self.cache[name]
        src = self.defs.get(name)
        if src is None:
            res = (None, f"source '{name}' is not registered")
        else:
            res = self._eval(src)
        self.cache[name] = res
        return res

    def _eval(self, src: dict) -> tuple[tuple[str, ...] | None, str | None]:
        kind = src.get("kind")
        if kind == "shell":
            try:
                p = subprocess.run(src["cmd"], shell=True, cwd=self.foundations,
                                   capture_output=True, text=True, timeout=900)
            except Exception as e:  # noqa: BLE001 — any failure to run is UNAVAILABLE
                return None, f"could not run: {e}"
            out = p.stdout + p.stderr
            m = re.search(src["extract"], out, re.M)
            if not m:
                tail = out.strip().splitlines()[-1] if out.strip() else "(no output)"
                return None, f"rc {p.returncode}, extract pattern found nothing; last line: {tail[:120]}"
            return tuple(norm(g) for g in m.groups()), None
        if kind == "file":
            path = self.root / src["file"]
            if not path.exists():
                return None, f"{src['file']} does not exist"
            m = re.search(src["pattern"], path.read_text(encoding="utf-8"), re.M)
            if not m:
                return None, f"pattern found nothing in {src['file']}"
            return tuple(norm(g) for g in m.groups()), None
        if kind == "sum":
            total = 0
            for part in src["of"]:
                vals, err = self.get(part)
                if err or not vals:
                    return None, f"summand '{part}' unavailable: {err}"
                try:
                    total += int(vals[0])
                except ValueError:
                    return None, f"summand '{part}' is not an integer: {vals[0]}"
            return (str(total),), None
        return None, f"unknown source kind '{kind}'"


def prose_value(claim: dict, root: Path) -> tuple[str | None, str | None]:
    path = root / claim["file"]
    if not path.exists():
        return None, f"{claim['file']} does not exist"
    text = path.read_text(encoding="utf-8")
    m = re.search(claim["pattern"], text, re.M)
    if not m:
        return None, f"claim pattern found nothing in {claim['file']}"
    raw = m.group(1).strip()
    if claim.get("words"):
        raw = WORDS.get(raw.lower(), raw)
    return norm(raw), None


def check(registry: dict, root: Path, foundations: Path, emit=print,
          source_root: Path = ROOT) -> int:
    """Returns 0 (all OK), 1 (any DRIFT), or 2 (nothing drifted but something UNAVAILABLE).

    `root` is where the PROSE is read from (the temp copy under self-test); `source_root` and
    `foundations` are where the MEASUREMENTS come from, and they always point at the real tree —
    a doctored copy must be judged against what the corpus actually says, not against itself."""
    sources = Sources(registry, foundations, source_root)
    ok = drift = unavailable = 0
    for claim in registry["claims"]:
        cid = claim["id"]
        got, err = prose_value(claim, root)
        if err:
            unavailable += 1
            emit(f"  UNAVAILABLE {cid}: {err}")
            continue
        vals, serr = sources.get(claim["source"])
        if serr or vals is None:
            unavailable += 1
            emit(f"  UNAVAILABLE {cid}: source '{claim['source']}': {serr}")
            continue
        idx = int(claim.get("group", 1)) - 1
        if idx >= len(vals):
            unavailable += 1
            emit(f"  UNAVAILABLE {cid}: source '{claim['source']}' has no group {idx + 1}")
            continue
        want = vals[idx]
        if got == want:
            ok += 1
            emit(f"  OK          {cid} = {want}")
        else:
            drift += 1
            emit(f"  DRIFT       {cid}: prose says {got}, corpus says {want}  ({claim['file']})")
    total = ok + drift + unavailable
    if drift:
        emit(f"PROSE-COUNTS DRIFT — {drift} of {total} tracked figures differ from the corpus"
             + (f"; {unavailable} unavailable" if unavailable else ""))
        return 1
    if unavailable:
        emit(f"PROSE-COUNTS UNAVAILABLE — {unavailable} of {total} tracked figures could not be checked; "
             f"{ok} match")
        return 2
    emit(f"PROSE-COUNTS OK — {total} tracked figures match the corpus")
    return 0


def self_test(registry: dict) -> int:
    """Three canaries, in a temp dir, never touching the tree. Exit 0 iff all three behave."""
    print("=== PROSE-COUNTS SELFTEST ===")
    tmp = Path(tempfile.mkdtemp(prefix="prose_counts_selftest_"))
    try:
        # Stage the prose files the registry names into the temp root.
        files = sorted({c["file"] for c in registry["claims"]})
        for f in files:
            dst = tmp / f
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / f, dst)
        readme_claims = [c for c in registry["claims"] if c["file"] == "README.md"]
        if not readme_claims:
            print("  selftest cannot run: no README.md claims registered")
            return 1
        # Canary 1 (must FIRE): doctor the first README figure.
        target = readme_claims[0]
        text = (tmp / "README.md").read_text(encoding="utf-8")
        m = re.search(target["pattern"], text, re.M)
        if not m:
            print(f"  selftest cannot run: pattern for {target['id']} found nothing in the copy")
            return 1
        doctored = text[:m.start(1)] + "999999" + text[m.end(1):]
        (tmp / "README.md").write_text(doctored, encoding="utf-8")
        sink: list[str] = []
        rc1 = check(registry, tmp, FOUNDATIONS, emit=sink.append)
        fired = rc1 == 1 and any(l.startswith("  DRIFT") and target["id"] in l for l in sink)
        print(f"  canary 1 (doctored README must FAIL): rc={rc1} {'FIRES' if fired else 'SILENT — BROKEN'}")
        # Canary 2 (must stay SILENT): restore the copy.
        (tmp / "README.md").write_text(text, encoding="utf-8")
        sink = []
        rc2 = check(registry, tmp, FOUNDATIONS, emit=sink.append)
        silent = rc2 == 0
        print(f"  canary 2 (control copy must PASS):    rc={rc2} {'SILENT' if silent else 'FIRES — BROKEN'}")
        if rc2 != 0:
            for l in sink:
                if not l.startswith("  OK"):
                    print("    " + l)
        # Canary 3 (must be UNAVAILABLE, not PASS): a source whose command fails.
        broken = json.loads(json.dumps(registry))
        broken["sources"]["theorems_core"] = {"kind": "shell", "cmd": "false", "extract": "(\\d+)"}
        broken["claims"] = [c for c in broken["claims"] if c["source"] == "theorems_core"]
        sink = []
        rc3 = check(broken, tmp, FOUNDATIONS, emit=sink.append)
        unavailable = rc3 == 2
        print(f"  canary 3 (dead source must be UNAVAILABLE): rc={rc3} {'UNAVAILABLE' if unavailable else 'WRONG VERDICT — BROKEN'}")
        good = fired and silent and unavailable
        print("PROSE-COUNTS SELFTEST " + ("PASS — 1 specimen fires, 1 control silent, 1 dead source unavailable"
                                          if good else "FAIL"))
        return 0 if good else 1
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main(argv: list[str]) -> int:
    if not REGISTRY.exists():
        print(f"PROSE-COUNTS UNAVAILABLE — {REGISTRY} not found")
        return 2
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    if "--self-test" in argv:
        return self_test(registry)
    print("=== prose counts vs corpus ===")
    return check(registry, ROOT, FOUNDATIONS)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
