#!/usr/bin/env python3
"""Transition report for the second 2026-10-27 rebaseline: the two false Forge-bridge axioms removed.

    cd foundations && python3 docs/machsig/transition_2026-10-27b.py

Old side: the LAST REVIEWED baseline on master, merged in 89e6855b (pull request #10), read with
`git show OLD_REV:...`. New side: the committed `tools/machsig/trust_baseline.json` this report is cited from.
Writes `docs/machsig/transition_2026-10-27b.json` (the gate binds its `binding` and `gate_transition` blocks) and
`docs/machsig/TRANSITION_2026-10-27b.md` (for the reviewer).

`gate_transition` is the gate's own function, imported. The change (owner's ruling F2 of
OWNER_RULINGS_2026-10-27_implicit.md): `interval_scale_unit_lit_le` and `interval_weight_sum_le` are removed;
`interval_add_scale`, proved through the second, takes `j + k ≤ 1`; `ForgeBridgeControls` refutes all three old
statements. Each claim is a check that can fail:

  C1  RESTATED: exactly `interval_add_scale` is restated, and its new statement is EXACTLY `ExpectedNewIntervalAddScale`
      (the old one with `j ≤ 1`, `k ≤ 1` replaced by `j + k ≤ 1`), by a copy of the gate's statement serializer
      (`evidence-2026-10-27b/statement_probe.lean`); no row is removed, redefined or malformed;
  C2  AXIOMS: exactly the two bridge axioms are gone (the probe also finds neither in the environment); none is
      restated or new;
  C3  POLICY: `known` loses exactly the two and gains none; `trusted` and `allowed_sorry` do not change;
  C4  only the two removed axioms left any footprint, and every axiom that entered one is trusted;
  C5  the controls refute EXACTLY the old statements: `OldUnitLitLeStatement` and `OldWeightSumLeStatement` serialize to
      master's pins of the two axioms, `OldIntervalAddScaleStatement` to master's digest of the old `interval_add_scale`;
  C6  the new rows are exactly `ForgeBridgeControls`'s declarations (three refutations, their private helpers), all
      on trusted axioms;
  C7  the probe's two serializer copies reproduce unchanged declarations' pins and digests (four axioms, three
      theorems), so they ARE the gate's serializers.

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

OLD_REV = "89e6855bbe9e13c243b2fd3b2f8527a3f623563b"
BASE = "tools/machsig/trust_baseline.json"
P = "MachLib.Real."
REMOVED = {P + "interval_scale_unit_lit_le", P + "interval_weight_sum_le"}
RESTATED = {P + "interval_add_scale"}
CTRL_NS = P + "ForgeBridgeControls."
CTRL_PRIV = "_private.MachLib.ForgeBridgeControls."
REFUTATIONS = {CTRL_NS + "unit_lit_le_false", CTRL_NS + "weight_sum_le_false",
               CTRL_NS + "old_interval_add_scale_false"}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PROBE = FOUND / "docs" / "machsig" / "evidence-2026-10-27b" / "statement_probe.tsv"
OUT_JSON = FOUND / "docs" / "machsig" / "transition_2026-10-27b.json"
OUT_MD = FOUND / "docs" / "machsig" / "TRANSITION_2026-10-27b.md"


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def short(a: str) -> str:
    for p in ("MachLib.Real.", "MachLib.", "Certcom."):
        if a.startswith(p):
            return "`" + a[len(p):] + "`"
    return "`" + a + "`"


def footprint(doc: dict, name: str) -> list[str]:
    return doc["axiom_sets"][doc["theorems"][name]["set"]]


def read_probe() -> dict:
    out = {"defval": {}, "thm": {}, "gone": {}, "ctrl_ax": {}, "ctrl_thm": {}}
    for ln in PROBE.read_text().splitlines():
        f = ln.split("\t")
        if f[0] == "DEFVAL":
            out["defval"][f[1]] = {"pin": sha(f[2]), "d": sha(f[3])[:32]}
        elif f[0] == "THM":
            out["thm"][f[1]] = {"kind": f[2], "d": sha(f[3])[:32]}
        elif f[0] == "GONE":
            out["gone"][f[1]] = f[2] == "true"
        elif f[0] == "CTRL_AX":
            out["ctrl_ax"][f[1]] = sha(f[2])
        elif f[0] == "CTRL_THM":
            out["ctrl_thm"][f[1]] = sha(f[2])[:32]
    return out


def main() -> int:
    old = json.loads(subprocess.run(["git", "show", f"{OLD_REV}:foundations/{BASE}"], cwd=FOUND,
                                    capture_output=True, text=True, check=True).stdout)
    new = json.loads((FOUND / BASE).read_text())
    gt = trust_gate.gate_transition(old, new)
    rows = gt["theorems"]
    probe = read_probe()
    trusted_new = set(new["policy"]["trusted"])
    kinds: dict[str, int] = {}
    for r in rows:
        kinds[r[1]] = kinds.get(r[1], 0) + 1
    checks, fails = {}, {}

    restated = sorted(r[0] for r in rows if r[1] == "restated")
    exp = probe["defval"].get(P + "ExpectedNewIntervalAddScale", {}).get("d")
    newd = probe["thm"].get(P + "interval_add_scale", {})
    checks["C1"] = (set(restated) == RESTATED and newd.get("kind") == "theorem" and newd.get("d") == exp
                    and new["theorems"][P + "interval_add_scale"]["d"] == exp
                    and not any(r[1] in ("removed", "redefined", "malformed") for r in rows))
    ax = gt["axioms"]
    checks["C2"] = (set(ax.get("gone", [])) == REMOVED and ax.get("restated") == [] and ax.get("new") == []
                    and all(probe["gone"].get(n) is False for n in REMOVED))
    pol = gt["policy"]
    checks["C3"] = (set(pol["known"]["removed"]) == REMOVED and pol["known"]["added"] == []
                    and pol["trusted"] == {"added": [], "removed": []}
                    and pol["allowed_sorry"] == {"added": [], "removed": []})
    old_rows = [r for r in rows if r[1] != "new"]
    bad4 = [r[0] for r in old_rows if not set(r[5]) <= REMOVED or not set(r[4]) <= trusted_new | STANDARD]
    checks["C4"] = not bad4
    fails["C4"] = bad4
    dv = probe["defval"]
    checks["C5"] = (dv.get(CTRL_NS + "OldUnitLitLeStatement", {}).get("pin")
                    == old["axiom_statements"].get(P + "interval_scale_unit_lit_le")
                    and dv.get(CTRL_NS + "OldWeightSumLeStatement", {}).get("pin")
                    == old["axiom_statements"].get(P + "interval_weight_sum_le")
                    and dv.get(CTRL_NS + "OldIntervalAddScaleStatement", {}).get("d")
                    == old["theorems"][P + "interval_add_scale"]["d"])
    new_rows = sorted(r[0] for r in rows if r[1] == "new")
    bad6 = [n for n in new_rows if not (n.startswith(CTRL_NS) or n.startswith(CTRL_PRIV))
            or not set(footprint(new, n)) <= trusted_new | STANDARD]
    checks["C6"] = REFUTATIONS <= set(new_rows) and not bad6
    fails["C6"] = bad6
    checks["C7"] = (len(probe["ctrl_ax"]) == 4 and len(probe["ctrl_thm"]) == 3
                    and all(v == new["axiom_statements"].get(n) == old["axiom_statements"].get(n)
                            for n, v in probe["ctrl_ax"].items())
                    and all(v == new["theorems"].get(n, {}).get("d") == old["theorems"].get(n, {}).get("d")
                            for n, v in probe["ctrl_thm"].items()))

    doc = {
        "schema": "machsig-transition/v3",
        "binding": {
            "old_baseline_file": f"{BASE} at {OLD_REV} (master)",
            "old_baseline_role": "the LAST REVIEWED baseline at the anchor: the implicit-function rebaseline, brought "
                                 "onto master by the merge commit 89e6855b (pull request #10)",
            "old_baseline_sha256": trust_gate.baseline_content_digest(old),
            "new_baseline_sha256": trust_gate.baseline_content_digest(new),
            "new_sources_commit": new["provenance"]["machlib_commit"],
        },
        "gate_transition": gt,
        "change": "the two false Forge-bridge axioms removed (interval_scale_unit_lit_le, interval_weight_sum_le); "
                  "interval_add_scale restated with j + k <= 1; ForgeBridgeControls refutes the three old statements",
        "row_kinds": dict(sorted(kinds.items())),
        "restated_theorems": restated,
        "new_rows": new_rows,
        "checks": checks,
        "check_failures": fails,
        "statement_probe_sha256": hashlib.sha256(PROBE.read_bytes()).hexdigest(),
    }
    OUT_JSON.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")

    desc = {
        "C1": "exactly `interval_add_scale` restated, to exactly its intended statement (gate serializer)",
        "C2": "exactly the two bridge axioms gone (and absent from the environment); none restated or new",
        "C3": "policy: `known` loses exactly the two; `trusted`, `allowed_sorry` unchanged",
        "C4": "only the two removed axioms left any footprint; every entering axiom is trusted",
        "C5": "the three control propositions are EXACTLY the old statements (master's pins and digest)",
        "C6": "new rows = `ForgeBridgeControls`'s declarations, all on trusted axioms",
        "C7": "the probe's serializer copies reproduce unchanged pins and digests",
    }
    lines = [
        "# Transition 2026-10-27 (b): the two false Forge-bridge axioms removed",
        "",
        "Generated by `docs/machsig/transition_2026-10-27b.py` (deterministic; rerun it to reproduce). The gate binds",
        "`binding` and `gate_transition` in `transition_2026-10-27b.json`; this file is the reviewer's view of the same rows.",
        "",
        f"- Old baseline: `{BASE}` at `{OLD_REV[:8]}` (master), the last reviewed baseline (merged in pull request #10),",
        f"  content `{doc['binding']['old_baseline_sha256'][:23]}...`",
        f"- New baseline: sources at `{doc['binding']['new_sources_commit'][:8]}`, content `{doc['binding']['new_baseline_sha256'][:23]}...`",
        f"- Theorem rows: {len(rows)} ({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))})",
        "",
        "## The change",
        "",
        "`interval_scale_unit_lit_le` (`0 < k → 0 < k → k ≤ 1`) and `interval_weight_sum_le` (`j, k ∈ (0, 1] → j + k ≤ 1`)",
        "were false: each docstring stated the condition that would make it true, and neither type had it. Both are removed.",
        "`interval_add_scale`, whose old statement was false too, takes `j + k ≤ 1`. The two `ForgeTest` theorems that used",
        "them prove their literal facts directly. `ForgeBridgeControls` refutes all three old statements.",
        "",
        "## Checks (each can fail; all must hold)",
        "",
        "| | check | holds |",
        "|---|---|---|",
    ]
    for k in sorted(checks):
        lines.append(f"| {k} | {desc[k]} | {'yes' if checks[k] else '**NO**'} |")
    lines += ["", "## Every row", "", "| theorem | kind | axioms before -> after | left | entered |", "|---|---|---|---|---|"]
    for r in rows:
        lines.append(f"| `{r[0]}` | {r[1]} | {r[2]} -> {r[3]} | {', '.join(short(a) for a in r[5])} | "
                     f"{', '.join(short(a) for a in r[4])} |")
    OUT_MD.write_text("\n".join(lines) + "\n")
    print(f"rows {len(rows)} {kinds}; checks " + " ".join(f"{k}={'ok' if v else 'FAIL'}" for k, v in sorted(checks.items())))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
