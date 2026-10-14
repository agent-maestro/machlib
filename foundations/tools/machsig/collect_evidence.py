#!/usr/bin/env python3
"""Gather the Lean-side evidence transition.py reads (policies, statements, axiom history).

    python3 tools/machsig/collect_evidence.py --evidence DIR --old-root OLD/foundations \
        --new-root NEW/foundations --old-rev 23e0d047 --new-rev c3046961

Expects DIR to hold already: sigs_23e0d047.jsonl and sigs_new.jsonl (regen.py at each root) and the
four legacy baseline files (see transition.py). Adds policy_*.json, statements_*.json and
axiom_history.json. Each probe reads the BUILT environment of its root; build both first.

Everything here is deterministic given the two trees and the git history, so a reviewer can rebuild
the evidence and get the same sha256 values the report prints.
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import probe  # noqa: E402
import transition  # noqa: E402


def dump(p: Path, obj) -> None:
    p.write_text(json.dumps(obj, sort_keys=True, indent=1) + "\n")


def pickaxe(root: Path, name: str, old_rev: str, new_rev: str) -> list[dict]:
    short = name.split(".")[-1]
    rx = r"axiom +" + re.escape(short) + r"([^A-Za-z0-9_'.!?]|$)"
    r = subprocess.run(["git", "log", "--format=%H%x09%ad%x09%s", "--date=short", "--pickaxe-regex", "-S", rx,
                        f"{old_rev}..{new_rev}", "--", "MachLib", "MachLib.lean", "CertcomLibm.lean"],
                       cwd=root, capture_output=True, text=True, check=True)
    out = []
    for ln in r.stdout.splitlines():
        h, d, s = ln.split("\t", 2)
        out.append({"commit": h, "date": d, "subject": s})
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--evidence", required=True, type=Path)
    ap.add_argument("--old-root", required=True, type=Path)
    ap.add_argument("--new-root", required=True, type=Path)
    ap.add_argument("--old-rev", required=True)
    ap.add_argument("--new-rev", required=True)
    a = ap.parse_args(argv)
    d = a.evidence
    for side, root in (("23e0d047", a.old_root), ("new", a.new_root)):
        pol = probe.policy(root)
        # tools/sorry_audit.lean's allowedSorry, read as text: a list of backticked names
        sa = (root / "tools" / "sorry_audit.lean").read_text()
        block = sa.split("def allowedSorry", 1)[1].split("]", 1)[0]
        allowed = sorted(set(re.findall(r"^\s*`([A-Za-z0-9_.']+)", block, re.M)))
        dump(d / f"policy_{side}.json", {"known": pol["known"], "trusted": pol["trusted"], "allowed_sorry": allowed})
        print(f"policy {side}: known {len(pol['known'])}, trusted {len(pol['trusted'])} "
              f"(AxiomLedger rc {pol['axiom_ledger_rc']})")
    ev = {k: d / v for k, v in transition.EVIDENCE.items() if (d / v).is_file()}
    t = transition.build(ev)
    need_old = sorted(r["theorem"] for r in t["rows"] if r["old"] is not None)
    need_new = sorted(r["theorem"] for r in t["rows"] if r["new"] is not None)
    need_old += sorted(set(t["moved_axioms"]["axiom_then_not_now"]))
    need_new += sorted(set(t["moved_axioms"]["axiom_now_not_then"]) | set(t["moved_axioms"]["now_theorem"])
                       | set(t["moved_axioms"]["now_definition"]))
    dump(d / "statements_23e0d047.json", probe.statements(a.old_root, need_old))
    dump(d / "statements_new.json", probe.statements(a.new_root, need_new))
    print(f"statements: {len(set(need_old))} old, {len(set(need_new))} new")
    moved = sorted(set(t["moved_axioms"]["axiom_then_not_now"]) | set(t["moved_axioms"]["axiom_now_not_then"]))
    hist = {n: pickaxe(a.new_root, n, a.old_rev, a.new_rev) for n in moved}
    # the commits that touched each source file holding a theorem a person must read (packet A, B, C1)
    read_rows = [r for r in t["rows"] if r["kind"] in ("removed", "restated")
                 or r.get("explained_by_discharge") is False]
    files = sorted({(r.get("module") or "").replace(".", "/") + ".lean" for r in read_rows if r.get("module")})
    fh = {}
    for f in files:
        out = subprocess.run(["git", "log", "--format=%H%x09%ad%x09%s", "--date=short", f"{a.old_rev}..{a.new_rev}",
                              "--", f], cwd=a.new_root, capture_output=True, text=True, check=True).stdout
        fh[f] = [dict(zip(("commit", "date", "subject"), ln.split("\t", 2))) for ln in out.splitlines()]
    hist = {"axioms": hist, "files": fh}
    dump(d / "axiom_history.json", hist)
    hist = hist["axioms"]
    print(f"axiom history: {len(moved)} axioms whose status changed, "
          f"{sum(1 for v in hist.values() if v)} traced to a commit")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
