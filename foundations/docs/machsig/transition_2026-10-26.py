#!/usr/bin/env python3
"""Transition report for the 2026-10-26 rebaseline: five derivable axioms proved.

    cd foundations && python3 docs/machsig/transition_2026-10-26.py

Old side: the LAST REVIEWED baseline on master, the step-7 landing (merged in 37edde55), read with
`git show OLD_REV:...`. New side: the committed `tools/machsig/trust_baseline.json` this report is
cited from. Writes `docs/machsig/transition_2026-10-26.json` (the gate binds its `binding` and
`gate_transition` blocks) and `docs/machsig/TRANSITION_2026-10-26.md` (for the reviewer).

`gate_transition` is the gate's own function, imported, so the machine block cannot disagree with the
gate's recompute. Everything else is a classification of those rows against the one change this
transition is meant to carry, with each claim stated as a check that can fail:

  C1  no theorem is restated, redefined or removed;
  C2  no axiom is restated or new; exactly the five converted axioms are gone;
  C3  policy: `known` loses exactly the five; `trusted` and `allowed_sorry` do not change;
  C4  every theorem row lost at least one of the five, and nothing else left it;
  C5  every axiom that entered a footprint is trusted, and is in the footprint of one of the five
      new theorems it replaced (so it entered through that proof, and from nowhere else);
  C6  every new row is one of the five theorems, one of their two private helpers, or a theorem that
      already exists at OLD_REV but is missing from the old baseline (added on master after the
      landing, which the gate accepts as INFO without rebaselining); all of them on trusted axioms;
  C7  each of the five theorems has EXACTLY the type of the axiom it replaces: its type, serialized by a
      copy of the gate's `serExpr` (evidence-2026-10-26/statement_probe.lean, run on the new tree), hashes
      to master's pin for that axiom; the copy reproduces four unchanged axioms' pins in the new baseline
      (so it IS the gate's serializer), and two near-miss names are absent. The gate itself cannot see a
      conversion that restates: it sees one axiom gone and one theorem new.

Deterministic: no clock, no environment; every collection is sorted.
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

FOUND = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FOUND / "tools" / "machsig"))
import trust_gate  # noqa: E402  (the gate's own transition and digest)

OLD_REV = "f572de8aae1ce2af53779055b1664b252df28d1a"
BASE = "tools/machsig/trust_baseline.json"
FIVE = {
    "MachLib.Real.exp_gt_two_x": "MachLib.Real.exp_gt_two_x",
    "MachLib.Real.sqrt_one": "MachLib.Real.sqrt_one",
    "MachLib.Real.tanh_zero": "MachLib.Real.tanh_zero",
    "MachLib.Real.u_le_one": "MachLib.Real.u_le_one",
    "MachLib.exp_tangent_line_strict": "MachLib.exp_tangent_line_strict",
}
HELPERS = {
    "_private.MachLib.SinNotInEMLDepth2Sweep.0.MachLib.Real.two_x_lt_exp_of_lt_one",
    "_private.MachLib.SinNotInEMLDepth2Sweep.0.MachLib.Real.two_x_lt_exp_of_pos",
}
PROBE = FOUND / "docs" / "machsig" / "evidence-2026-10-26" / "statement_probe.tsv"
CONTROLS = ["MachLib.Real.tanh_neg", "MachLib.Real.u_lt_one", "MachLib.Real.sqrt_zero", "MachLib.Real.exp_gt_one_plus_self"]
ABSENT = ["MachLib.Real.Real.tanh_zero", "MachLib.Real.exp_tangent_line_strict"]
OUT_JSON = FOUND / "docs" / "machsig" / "transition_2026-10-26.json"
OUT_MD = FOUND / "docs" / "machsig" / "TRANSITION_2026-10-26.md"


def short(a: str) -> str:
    for p in ("MachLib.Real.", "MachLib.", "Certcom."):
        if a.startswith(p):
            return "`" + a[len(p):] + "`"
    return "`" + a + "`"


def footprint(doc: dict, name: str) -> list[str]:
    t = doc["theorems"][name]
    return doc["axiom_sets"][t["set"]]


def main() -> int:
    old = json.loads(subprocess.run(["git", "show", f"{OLD_REV}:foundations/{BASE}"], cwd=FOUND,
                                    capture_output=True, text=True, check=True).stdout)
    new = json.loads((FOUND / BASE).read_text())
    gt = trust_gate.gate_transition(old, new)
    rows = gt["theorems"]
    five = set(FIVE)
    trusted = set(new["policy"]["trusted"])
    # the axioms each converted theorem's proof now rests on
    proof_fp = {n: set(footprint(new, n)) for n in five}

    kinds: dict[str, int] = {}
    for r in rows:
        kinds[r[1]] = kinds.get(r[1], 0) + 1
    checks = {}
    checks["C1"] = not any(r[1] in ("restated", "redefined", "removed", "malformed") for r in rows)
    checks["C2"] = (gt["axioms"].get("restated") == [] and gt["axioms"].get("new") == []
                    and set(gt["axioms"].get("gone", [])) == five)
    pol = gt["policy"]
    checks["C3"] = (set(pol["known"]["removed"]) == five and pol["known"]["added"] == []
                    and pol["trusted"] == {"added": [], "removed": []}
                    and pol["allowed_sorry"] == {"added": [], "removed": []})
    old_rows = [r for r in rows if r[1] != "new"]
    bad4 = [r[0] for r in old_rows if not (set(r[5]) & five) or not set(r[5]) <= five]
    checks["C4"] = not bad4
    bad5 = []
    for r in old_rows:
        via = set().union(*(proof_fp[a] for a in set(r[5]) & five)) if set(r[5]) & five else set()
        if not set(r[4]) <= trusted or not set(r[4]) <= via:
            bad5.append(r[0])
    checks["C5"] = not bad5
    new_rows = sorted(r[0] for r in rows if r[1] == "new")
    since_landing = {}
    for n in sorted(set(new_rows) - five - HELPERS):
        hit = subprocess.run(["git", "grep", "-n", "-E", rf"^(private )?theorem {n.split('.')[-1]}\b", OLD_REV,
                              "--", "MachLib"], cwd=FOUND, capture_output=True, text=True)
        since_landing[n] = hit.stdout.strip().splitlines()
    checks["C6"] = (five | HELPERS <= set(new_rows)
                    and all(len(v) == 1 for v in since_landing.values())
                    and all(set(footprint(new, n)) <= trusted | {"propext", "Classical.choice", "Quot.sound"}
                            for n in new_rows))

    probe = {}
    for ln in PROBE.read_text().splitlines():
        f = ln.split("\t")
        probe[f[0]] = {"kind": f[1]} if len(f) == 2 else \
            {"kind": f[1], "module": f[2], "ser_sha256": hashlib.sha256(f[4][len("SER="):].encode()).hexdigest()}
    c7 = {n: {"kind": probe.get(n, {}).get("kind"), "module": probe.get(n, {}).get("module"),
              "ser_sha256": probe.get(n, {}).get("ser_sha256"), "master_axiom_pin": old["axiom_statements"].get(n)}
          for n in sorted(five)}
    checks["C7"] = (all(v["kind"] == "theorem" and v["ser_sha256"] == v["master_axiom_pin"] for v in c7.values())
                    and all(probe.get(n, {}).get("kind") == "axiom"
                            and probe[n]["ser_sha256"] == new["axiom_statements"].get(n) for n in CONTROLS)
                    and all(probe.get(n, {}).get("kind") == "ABSENT" for n in ABSENT))

    by_axiom = {a: sorted(r[0] for r in old_rows if a in r[5]) for a in sorted(five)}
    entered = {}
    for r in old_rows:
        for a in r[4]:
            entered[a] = entered.get(a, 0) + 1
    doc = {
        "schema": "machsig-transition/v3",
        "binding": {
            "old_baseline_file": f"{BASE} at {OLD_REV} (master)",
            "old_baseline_role": "the LAST REVIEWED baseline at the anchor: the step-7 landing, brought onto "
                                 "master by the merge commit 37edde55",
            "old_baseline_sha256": trust_gate.baseline_content_digest(old),
            "new_baseline_sha256": trust_gate.baseline_content_digest(new),
            "new_sources_commit": new["provenance"]["machlib_commit"],
        },
        "gate_transition": gt,
        "change": "five derivable axioms proved: " + ", ".join(sorted(five)),
        "row_kinds": dict(sorted(kinds.items())),
        "rows_by_converted_axiom": by_axiom,
        "entered_axioms_count": dict(sorted(entered.items())),
        "proof_footprints": {n: sorted(proof_fp[n]) for n in sorted(five)},
        "new_rows": new_rows,
        "new_rows_added_on_master_since_the_landing": since_landing,
        "checks": checks,
        "statement_identity": c7,
        "statement_probe_sha256": hashlib.sha256(PROBE.read_bytes()).hexdigest(),
        "check_failures": {"C4": bad4, "C5": bad5},
    }
    OUT_JSON.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")

    lines = [
        "# Transition 2026-10-26: five derivable axioms proved",
        "",
        "Generated by `docs/machsig/transition_2026-10-26.py` (deterministic; rerun it to reproduce). The gate binds",
        "`binding` and `gate_transition` in `transition_2026-10-26.json`; this file is the reviewer's view of the same rows.",
        "",
        f"- Old baseline: `{BASE}` at `{OLD_REV[:8]}` (master), the last reviewed baseline (step 7, merged in `37edde55`),",
        f"  content `{doc['binding']['old_baseline_sha256'][:23]}...`",
        f"- New baseline: sources at `{doc['binding']['new_sources_commit'][:8]}`, content `{doc['binding']['new_baseline_sha256'][:23]}...`",
        f"- Theorem rows: {len(rows)} ({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))})",
        "",
        "## The change",
        "",
        "`exp_tangent_line_strict`, `exp_gt_two_x`, `tanh_zero`, `sqrt_one`, `u_le_one` were axioms; each is now a",
        "theorem of the same name and statement, proved from trusted axioms. Every theorem that used one of them now",
        "rests on the axioms that proof uses instead. That is a SWAP in the gate's terms (an axiom entered), which is",
        "why this needs a reviewed rebaseline.",
        "",
        "## Checks (each can fail; all must hold)",
        "",
        "| | check | holds |",
        "|---|---|---|",
    ]
    desc = {
        "C1": "no theorem restated, redefined or removed",
        "C2": "no axiom restated or new; exactly the five gone",
        "C3": "policy: `known` loses exactly the five; `trusted` and `allowed_sorry` unchanged",
        "C4": "every theorem row lost at least one of the five, and nothing else",
        "C5": "every entered axiom is trusted and in the replacing proof's footprint",
        "C6": "new rows = the five + two private helpers + theorems already at the old revision, all on trusted axioms",
        "C7": "each of the five has exactly its old axiom's type (gate serializer, master's pins)",
    }
    for k in sorted(checks):
        lines.append(f"| {k} | {desc[k]} | {'yes' if checks[k] else '**NO**'} |")
    lines += ["", "## New rows that are not this change", "",
              "Theorems added on master after the landing. New theorems pass the gate as INFO, so no baseline",
              "recorded them; a report is NET from the last reviewed baseline, so they appear here. Each is found",
              f"at `{OLD_REV[:8]}` and rests on trusted axioms only.", ""]
    for n, v in since_landing.items():
        lines.append(f"- `{n}`: {'; '.join(v)}")
    lines += ["", "## Rows per converted axiom", "", "| axiom | theorems whose footprint lost it |", "|---|---|"]
    for a in sorted(five):
        lines.append(f"| `{a}` | {len(by_axiom[a])} |")
    lines += ["", "## What each proof rests on (the axioms that can enter)", ""]
    for n in sorted(five):
        lines.append(f"- `{n}`: {len(proof_fp[n])} axioms, all trusted: "
                     + ", ".join(short(a) for a in sorted(proof_fp[n])))
    lines += ["", "## Every row", "", "| theorem | kind | axioms before -> after | left | entered |", "|---|---|---|---|---|"]
    for r in rows:
        left = ", ".join(short(a) for a in r[5])
        lines.append(f"| `{r[0]}` | {r[1]} | {r[2]} -> {r[3]} | {left} | {len(r[4])} |")
    OUT_MD.write_text("\n".join(lines) + "\n")
    print(f"rows {len(rows)} {kinds}; checks " + " ".join(f"{k}={'ok' if v else 'FAIL'}" for k, v in sorted(checks.items())))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
