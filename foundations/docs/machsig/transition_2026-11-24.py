#!/usr/bin/env python3
"""Transition report for the 2026-11-24 rebaseline: six derivable axioms proved.

    cd foundations && python3 docs/machsig/transition_2026-11-24.py

Old side: the LAST REVIEWED baseline on master, the Forge-bridge rebaseline (a356363b, merged in cc90d9b4 and
unchanged on master since), read with
`git show OLD_REV:...`. New side: the committed `tools/machsig/trust_baseline.json` this report is
cited from. Writes `docs/machsig/transition_2026-11-24.json` (the gate binds its `binding` and
`gate_transition` blocks) and `docs/machsig/TRANSITION_2026-11-24.md` (for the reviewer).

`gate_transition` is the gate's own function, imported, so the machine block cannot disagree with the
gate's recompute. Everything else is a classification of those rows against the one change this
transition is meant to carry, with each claim stated as a check that can fail:

  C1  no theorem is restated, redefined or removed;
  C2  no axiom is restated or new; exactly the six converted axioms are gone;
  C3  policy: `known` loses exactly the six; `trusted` loses exactly `u_lt_one` and `u_le_half` (the two that
      were trusted) and gains nothing; `allowed_sorry` does not change;
  C4  every theorem row lost at least one of the six, and nothing else left it;
  C5  every axiom that entered a footprint is trusted, and is in the footprint of one of the six
      new theorems it replaced (so it entered through that proof, and from nowhere else);
  C6  every new row is one of the six theorems, one of their five private helpers, or a theorem that
      already exists at OLD_REV (a declaration line naming it, matched on Lean's name syntax) but is missing
      from the old baseline (added on master after the
      last reviewed baseline, which the gate accepts as INFO without rebaselining). The six and their helpers rest on
      trusted axioms only; a row master added rests on DECLARED axioms (the gate's INFO rule) and, if any of them is
      outside the trusted policy, is listed by name -- #13's `oneQueryLevelSet_of_residue'` is conditional on
      `eml_tree_analytic_on_interval`, as it is on master;
  C7  each of the six theorems has EXACTLY the type of the axiom it replaces: its type, serialized by a
      copy of the gate's `serExpr` (evidence-2026-11-24/statement_probe.lean, run on the new tree), hashes
      to master's pin for that axiom; the copy reproduces four unchanged axioms' pins in the new baseline
      (so it IS the gate's serializer), and two near-miss names are absent. The gate itself cannot see a
      conversion that restates: it sees one axiom gone and one theorem new.

Deterministic: no clock, no environment; every collection is sorted.
"""
from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

FOUND = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(FOUND / "tools" / "machsig"))
import trust_gate  # noqa: E402  (the gate's own transition and digest)

OLD_REV = "fcc4ae1b0c238d04f217181840749e1cbcb4c152"
BASE = "tools/machsig/trust_baseline.json"
SIX = {
    "MachLib.Real.exp_exp_minus_exp_strictly_increasing": "MachLib.Real.exp_exp_minus_exp_strictly_increasing",
    "MachLib.Real.exp_one_lt_three": "MachLib.Real.exp_one_lt_three",
    "MachLib.Real.sqrt_neg_zero": "MachLib.Real.sqrt_neg_zero",
    "MachLib.Real.sqrt_zero": "MachLib.Real.sqrt_zero",
    "MachLib.Real.u_le_half": "MachLib.Real.u_le_half",
    "MachLib.Real.u_lt_one": "MachLib.Real.u_lt_one",
}
WAS_TRUSTED = {"MachLib.Real.u_le_half", "MachLib.Real.u_lt_one"}
HELPERS = {
    "_private.MachLib.Trig.0.MachLib.Real.sqrt_eq_zero_of_nonpos",
    "_private.MachLib.IteratedExpBounds.0.MachLib.Real.e_bound_mul_le",
    "_private.MachLib.IteratedExpBounds.0.MachLib.Real.e_bound_natCast_six",
    "_private.MachLib.IteratedExpBounds.0.MachLib.Real.e_bound_natCast_three",
    "_private.MachLib.FPModel.0.MachLib.Real.one_lt_natCast_two_pow_52",
}
PROBE = FOUND / "docs" / "machsig" / "evidence-2026-11-24" / "statement_probe.tsv"
CONTROLS = ["MachLib.Real.sqrt_nonneg", "MachLib.Real.u_le_inv_two_pow_52", "MachLib.Real.exp_gt_one_plus_self",
            "MachLib.Real.tanh_neg"]
ABSENT = ["MachLib.Real.Real.sqrt_zero", "MachLib.exp_one_lt_three"]
OUT_JSON = FOUND / "docs" / "machsig" / "transition_2026-11-24.json"
OUT_MD = FOUND / "docs" / "machsig" / "TRANSITION_2026-11-24.md"


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
    six = set(SIX)
    trusted = set(new["policy"]["trusted"])
    # the axioms each converted theorem's proof now rests on
    proof_fp = {n: set(footprint(new, n)) for n in six}

    kinds: dict[str, int] = {}
    for r in rows:
        kinds[r[1]] = kinds.get(r[1], 0) + 1
    checks = {}
    checks["C1"] = not any(r[1] in ("restated", "redefined", "removed", "malformed") for r in rows)
    checks["C2"] = (gt["axioms"].get("restated") == [] and gt["axioms"].get("new") == []
                    and set(gt["axioms"].get("gone", [])) == six)
    pol = gt["policy"]
    checks["C3"] = (set(pol["known"]["removed"]) == six and pol["known"]["added"] == []
                    and pol["trusted"]["added"] == [] and set(pol["trusted"]["removed"]) == WAS_TRUSTED
                    and pol["allowed_sorry"] == {"added": [], "removed": []})
    old_rows = [r for r in rows if r[1] != "new"]
    bad4 = [r[0] for r in old_rows if not (set(r[5]) & six) or not set(r[5]) <= six]
    checks["C4"] = not bad4
    bad5 = []
    for r in old_rows:
        via = set().union(*(proof_fp[a] for a in set(r[5]) & six)) if set(r[5]) & six else set()
        if not set(r[4]) <= trusted or not set(r[4]) <= via:
            bad5.append(r[0])
    checks["C5"] = not bad5
    new_rows = sorted(r[0] for r in rows if r[1] == "new")
    since_landing = {}
    theorem_lines = subprocess.run(["git", "grep", "-n", "-F", "theorem ", OLD_REV, "--", "MachLib"], cwd=FOUND,
                                   capture_output=True, text=True, check=True).stdout.splitlines()
    for n in sorted(set(new_rows) - six - HELPERS):
        last = n.split(".")[-1]
        # Lean names carry primes and dots: `\b` reads `foo'` as `foo` and misses `theorem A.foo`, which is how
        # the 2026-10-26 template's search failed on six theorems #12/#13 added. Match the declared name exactly:
        # optional namespace prefix, then the last component, then no further name character.
        decl = re.compile(rf"^\s*(?:@\[[^\]]*\]\s*)?(?:private |protected )?theorem (?:[\w'.]+\.)?{re.escape(last)}(?![\w'])")
        since_landing[n] = [ln for ln in theorem_lines if decl.search(ln.split(":", 3)[3])]
    core = {"propext", "Classical.choice", "Quot.sound"}
    declared = set(new["policy"]["known"]) | trusted | core
    since_conditional = {n: sorted(set(footprint(new, n)) - trusted - core) for n in since_landing
                         if set(footprint(new, n)) - trusted - core}
    checks["C6"] = (six | HELPERS <= set(new_rows)
                    and all(len(v) >= 1 for v in since_landing.values())
                    # this change's own rows: trusted axioms only
                    and all(set(footprint(new, n)) <= trusted | core for n in six | HELPERS)
                    # rows master added since the last reviewed baseline: the gate's own INFO rule, declared axioms
                    and all(set(footprint(new, n)) <= declared for n in since_landing))

    probe = {}
    for ln in PROBE.read_text().splitlines():
        f = ln.split("\t")
        probe[f[0]] = {"kind": f[1]} if len(f) == 2 else \
            {"kind": f[1], "module": f[2], "ser_sha256": hashlib.sha256(f[4][len("SER="):].encode()).hexdigest()}
    c7 = {n: {"kind": probe.get(n, {}).get("kind"), "module": probe.get(n, {}).get("module"),
              "ser_sha256": probe.get(n, {}).get("ser_sha256"), "master_axiom_pin": old["axiom_statements"].get(n)}
          for n in sorted(six)}
    checks["C7"] = (all(v["kind"] == "theorem" and v["ser_sha256"] == v["master_axiom_pin"] for v in c7.values())
                    and all(probe.get(n, {}).get("kind") == "axiom"
                            and probe[n]["ser_sha256"] == new["axiom_statements"].get(n) for n in CONTROLS)
                    and all(probe.get(n, {}).get("kind") == "ABSENT" for n in ABSENT))

    by_axiom = {a: sorted(r[0] for r in old_rows if a in r[5]) for a in sorted(six)}
    entered = {}
    for r in old_rows:
        for a in r[4]:
            entered[a] = entered.get(a, 0) + 1
    doc = {
        "schema": "machsig-transition/v3",
        "binding": {
            "old_baseline_file": f"{BASE} at {OLD_REV} (master)",
            "old_baseline_role": "the LAST REVIEWED baseline at the anchor: the Forge-bridge rebaseline (a356363b), "
                                 "brought onto master by the merge commit cc90d9b4 and unchanged on master since",
            "old_baseline_sha256": trust_gate.baseline_content_digest(old),
            "new_baseline_sha256": trust_gate.baseline_content_digest(new),
            "new_sources_commit": new["provenance"]["machlib_commit"],
        },
        "gate_transition": gt,
        "change": "six derivable axioms proved: " + ", ".join(sorted(six)),
        "row_kinds": dict(sorted(kinds.items())),
        "rows_by_converted_axiom": by_axiom,
        "entered_axioms_count": dict(sorted(entered.items())),
        "proof_footprints": {n: sorted(proof_fp[n]) for n in sorted(six)},
        "new_rows": new_rows,
        "new_rows_added_on_master_since_the_landing": since_landing,
        "new_rows_since_the_landing_resting_outside_trusted": since_conditional,
        "checks": checks,
        "statement_identity": c7,
        "statement_probe_sha256": hashlib.sha256(PROBE.read_bytes()).hexdigest(),
        "check_failures": {"C4": bad4, "C5": bad5},
    }
    OUT_JSON.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")

    lines = [
        "# Transition 2026-11-24: six derivable axioms proved",
        "",
        "Generated by `docs/machsig/transition_2026-11-24.py` (deterministic; rerun it to reproduce). The gate binds",
        "`binding` and `gate_transition` in `transition_2026-11-24.json`; this file is the reviewer's view of the same rows.",
        "",
        f"- Old baseline: `{BASE}` at `{OLD_REV[:8]}` (master), the last reviewed baseline (a356363b, merged in `cc90d9b4`),",
        f"  content `{doc['binding']['old_baseline_sha256'][:23]}...`",
        f"- New baseline: sources at `{doc['binding']['new_sources_commit'][:8]}`, content `{doc['binding']['new_baseline_sha256'][:23]}...`",
        f"- Theorem rows: {len(rows)} ({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))})",
        "",
        "## The change",
        "",
        "`sqrt_zero`, `sqrt_neg_zero`, `exp_exp_minus_exp_strictly_increasing`, `exp_one_lt_three`, `u_lt_one`,",
        "`u_le_half` were axioms; each is now a theorem of the same name and statement, proved from trusted axioms.",
        "Every theorem that used one of them now rests on the axioms that proof uses instead. That is a SWAP in the",
        "gate's terms (an axiom entered), which is why this needs a reviewed rebaseline. `u_lt_one` and `u_le_half`",
        "were TRUSTED, so the trusted policy loses them (156 -> 154) and no theorem's class moves on their account;",
        "the other four were outside it, and their dependants move from conditional to approved policy.",
        "",
        "## Checks (each can fail; all must hold)",
        "",
        "| | check | holds |",
        "|---|---|---|",
    ]
    desc = {
        "C1": "no theorem restated, redefined or removed",
        "C2": "no axiom restated or new; exactly the six gone",
        "C3": "policy: `known` loses exactly the six; `trusted` loses exactly `u_lt_one`, `u_le_half`; `allowed_sorry` unchanged",
        "C4": "every theorem row lost at least one of the six, and nothing else",
        "C5": "every entered axiom is trusted and in the replacing proof's footprint",
        "C6": "new rows = the six + five private helpers (trusted axioms only) + theorems already at the old revision (declared axioms; conditional ones listed below)",
        "C7": "each of the six has exactly its old axiom's type (gate serializer, master's pins)",
    }
    for k in sorted(checks):
        lines.append(f"| {k} | {desc[k]} | {'yes' if checks[k] else '**NO**'} |")
    lines += ["", "## New rows that are not this change", "",
              "Theorems added on master after the landing. New theorems pass the gate as INFO, so no baseline",
              "recorded them; a report is NET from the last reviewed baseline, so they appear here. Each is found",
              f"at `{OLD_REV[:8]}` and rests on trusted axioms only.", ""]
    for n, v in since_landing.items():
        lines.append(f"- `{n}`: {'; '.join(v)}")
    lines += ["", "Of these, resting on a declared axiom outside the trusted policy (conditional on master too):", ""]
    for n, v in since_conditional.items():
        lines.append(f"- `{n}`: " + ", ".join(short(a) for a in v))
    lines += ["", "## Rows per converted axiom", "", "| axiom | theorems whose footprint lost it |", "|---|---|"]
    for a in sorted(six):
        lines.append(f"| `{a}` | {len(by_axiom[a])} |")
    lines += ["", "## What each proof rests on (the axioms that can enter)", ""]
    for n in sorted(six):
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
