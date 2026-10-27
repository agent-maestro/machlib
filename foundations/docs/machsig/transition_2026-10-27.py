#!/usr/bin/env python3
"""Transition report for the 2026-10-27 rebaseline: the implicit-function repair, two conversions, thirteen trusted.

    cd foundations && python3 docs/machsig/transition_2026-10-27.py

Old side: the LAST REVIEWED baseline on master, merged in 2431d705 (pull request #9), read with
`git show OLD_REV:...`. New side: the committed `tools/machsig/trust_baseline.json` this report is cited from.
Writes `docs/machsig/transition_2026-10-27.json` (the gate binds its `binding` and `gate_transition` blocks) and
`docs/machsig/TRANSITION_2026-10-27.md` (for the reviewer).

`gate_transition` is the gate's own function, imported, so the machine block cannot disagree with the gate's
recompute. The change has four parts (the owner's rulings, OWNER_RULINGS_2026-10-27_implicit.md), and each claim
about them is a check that can fail:

  C1  RESTATED THEOREMS: every restated row is a theorem whose new statement, with its one binder named `hcont`
      (concluding `ContinuousAt`) removed, has EXACTLY its old statement digest, by a copy of the gate's statement
      serializer (`evidence-2026-10-27/statement_probe.lean`); and no row is removed, redefined or malformed;
  C2  AXIOMS: exactly `hasDerivAt_implicit_local` is restated, and with its one `ContinuousAt` hypothesis removed has
      EXACTLY master's pin (the gate's axiom serializer); none is new; exactly the two converted axioms
      (`HasDerivAt2_sub`, `hasDerivAt_implicit`) are gone;
  C3  POLICY: `trusted` gains exactly the thirteen axioms that remain of the fifteen the owner approved, loses none;
      `known` loses exactly the two converted axioms and gains none; `allowed_sorry` does not change;
  C4  every axiom that entered an existing theorem's footprint is trusted under the new policy, and only the two
      converted axioms left any footprint;
  C5  the new rows are exactly the controls module's declarations, the two continuity helpers and the two converted
      theorems, all on trusted axioms (under the new policy);
  C6  the controls refute EXACTLY the old statements: `OldImplicitStatement` and `OldImplicitLocalStatement` serialize
      to master's pins of the old implicit axioms, `OldCurveCountStatement` to master's digest of the old
      `khovanskii_rolle_count_curve`; the three refutations are new rows;
  C7  the probe's two serializer copies reproduce unchanged declarations' pins and digests (four axioms, three
      theorems), so they ARE the gate's serializers;
  C8  each converted axiom is now a THEOREM of exactly its axiom's type: `HasDerivAt2_sub`'s type serializes to master's
      pin; `hasDerivAt_implicit`'s to the restated pin in the unreviewed baseline of `UNREVIEWED_REV` (the review's
      object), and with its one `ContinuousAt` hypothesis removed to master's pin.

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

OLD_REV = "2431d7056bdc43f4a923544c8d4b0499814acb00"
UNREVIEWED_REV = "1c8cb712"
BASE = "tools/machsig/trust_baseline.json"
P = "MachLib.Real."
RESTATED_AXIOMS = {P + "hasDerivAt_implicit_local"}
CONVERTED = {P + "HasDerivAt2_sub", P + "hasDerivAt_implicit"}
TRUSTED_ADDED = {P + n for n in [
    "HasDerivAt2", "HasDerivAt2_projX", "HasDerivAt2_projY", "HasDerivAt2_const", "HasDerivAt2_add",
    "HasDerivAt2_mul", "HasDerivAt2_scomp", "HasDerivAt2_comp",
    "hasDerivAt_implicit_local",
    "floor", "floor_le", "lt_floor_add_one", "floor_zero"]}
CONTROLS_NS = P + "BivariateImplicitControls."
CONTROLS_PRIV = "_private.MachLib.BivariateImplicitControls."
HELPERS = {P + "continuousAt_const_sub", P + "continuousAt_congr_fun"}
REFUTATIONS = {CONTROLS_NS + "implicit_without_continuity_inconsistent",
               CONTROLS_NS + "implicit_local_without_continuity_inconsistent", CONTROLS_NS + "old_curve_count_false"}
OLD_CURVE_COUNT = "MachLib.MultiVarMod.TwoExp.khovanskii_rolle_count_curve"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
PROBE = FOUND / "docs" / "machsig" / "evidence-2026-10-27" / "statement_probe.tsv"
OUT_JSON = FOUND / "docs" / "machsig" / "transition_2026-10-27.json"
OUT_MD = FOUND / "docs" / "machsig" / "TRANSITION_2026-10-27.md"


def sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


def short(a: str) -> str:
    for p in ("MachLib.Real.", "MachLib.MultiVarMod.TwoExp.", "MachLib.", "Certcom."):
        if a.startswith(p):
            return "`" + a[len(p):] + "`"
    return "`" + a + "`"


def footprint(doc: dict, name: str) -> list[str]:
    return doc["axiom_sets"][doc["theorems"][name]["set"]]


def read_probe() -> dict:
    out = {"thm": {}, "ax": {}, "defval": {}, "ctrl_ax": {}, "ctrl_thm": {}, "conv": {}}
    for ln in PROBE.read_text().splitlines():
        f = ln.split("\t")
        if f[0] == "STRIP_THM":
            out["thm"][f[1]] = {"removed": int(f[2]), "used": int(f[3]), "d": sha(f[4])[:32]}
        elif f[0] == "STRIP_AX":
            out["ax"][f[1]] = {"removed": int(f[2]), "used": int(f[3]), "pin": sha(f[4])}
        elif f[0] == "DEFVAL":
            out["defval"][f[1]] = {"pin": sha(f[2]), "d": sha(f[3])[:32]}
        elif f[0] == "CONV":
            out["conv"][f[1]] = {"kind": f[2], "removed": int(f[3]), "used": int(f[4]), "pin": sha(f[5]),
                                 "stripped_pin": sha(f[6])}
        elif f[0] == "CTRL_AX":
            out["ctrl_ax"][f[1]] = sha(f[2])
        elif f[0] == "CTRL_THM":
            out["ctrl_thm"][f[1]] = sha(f[2])[:32]
    return out


def main() -> int:
    old = json.loads(subprocess.run(["git", "show", f"{OLD_REV}:foundations/{BASE}"], cwd=FOUND,
                                    capture_output=True, text=True, check=True).stdout)
    unreviewed = json.loads(subprocess.run(["git", "show", f"{UNREVIEWED_REV}:foundations/{BASE}"], cwd=FOUND,
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

    # C1
    restated = sorted(r[0] for r in rows if r[1] == "restated")
    bad1 = [n for n in restated
            if not (probe["thm"].get(n, {}).get("removed") == 1 and probe["thm"][n]["used"] == 0
                    and probe["thm"][n]["d"] == old["theorems"][n]["d"])]
    bad1 += [r[0] for r in rows if r[1] in ("removed", "redefined", "malformed")]
    checks["C1"] = bool(restated) and not bad1
    fails["C1"] = bad1
    # C2
    ax = gt["axioms"]
    bad2 = [n for n in sorted(RESTATED_AXIOMS)
            if not (probe["ax"].get(n, {}).get("removed") == 1 and probe["ax"][n]["used"] == 0
                    and probe["ax"][n]["pin"] == old["axiom_statements"].get(n))]
    checks["C2"] = (set(ax.get("restated", [])) == RESTATED_AXIOMS and ax.get("new") == []
                    and set(ax.get("gone", [])) == CONVERTED and not bad2)
    fails["C2"] = bad2
    # C3
    pol = gt["policy"]
    checks["C3"] = (set(pol["trusted"]["added"]) == TRUSTED_ADDED and pol["trusted"]["removed"] == []
                    and pol["known"]["added"] == [] and set(pol["known"]["removed"]) == CONVERTED
                    and pol["allowed_sorry"] == {"added": [], "removed": []})
    # C4
    old_rows = [r for r in rows if r[1] != "new"]
    bad4 = [r[0] for r in old_rows if not set(r[4]) <= trusted_new | STANDARD or not set(r[5]) <= CONVERTED]
    checks["C4"] = not bad4
    fails["C4"] = bad4
    # C5
    new_rows = sorted(r[0] for r in rows if r[1] == "new")
    expected_new = lambda n: (n.startswith(CONTROLS_NS) or n.startswith(CONTROLS_PRIV)  # noqa: E731
                              or n in HELPERS or n in CONVERTED)
    bad5 = [n for n in new_rows if not expected_new(n)
            or not set(footprint(new, n)) <= trusted_new | STANDARD]
    checks["C5"] = (REFUTATIONS | HELPERS | CONVERTED <= set(new_rows)) and not bad5
    fails["C5"] = bad5
    # C6
    dv_imp = probe["defval"].get(CONTROLS_NS + "OldImplicitStatement", {})
    dv_loc = probe["defval"].get(CONTROLS_NS + "OldImplicitLocalStatement", {})
    dv_cc = probe["defval"].get(CONTROLS_NS + "OldCurveCountStatement", {})
    checks["C6"] = (dv_imp.get("pin") == old["axiom_statements"].get(P + "hasDerivAt_implicit")
                    and dv_loc.get("pin") == old["axiom_statements"].get(P + "hasDerivAt_implicit_local")
                    and dv_cc.get("d") == old["theorems"][OLD_CURVE_COUNT]["d"]
                    and REFUTATIONS <= set(new_rows))
    # C7
    checks["C7"] = (len(probe["ctrl_ax"]) == 4 and len(probe["ctrl_thm"]) == 3
                    and all(v == new["axiom_statements"].get(n) == old["axiom_statements"].get(n)
                            for n, v in probe["ctrl_ax"].items())
                    and all(v == new["theorems"].get(n, {}).get("d") == old["theorems"].get(n, {}).get("d")
                            for n, v in probe["ctrl_thm"].items()))

    # C8
    cs, ci = probe["conv"].get(P + "HasDerivAt2_sub", {}), probe["conv"].get(P + "hasDerivAt_implicit", {})
    checks["C8"] = (cs.get("kind") == "theorem" and cs.get("removed") == 0
                    and cs.get("pin") == old["axiom_statements"].get(P + "HasDerivAt2_sub")
                    and ci.get("kind") == "theorem" and ci.get("removed") == 1 and ci.get("used") == 0
                    and ci.get("pin") == unreviewed["axiom_statements"].get(P + "hasDerivAt_implicit")
                    and ci.get("stripped_pin") == old["axiom_statements"].get(P + "hasDerivAt_implicit")
                    and not (CONVERTED & set(new["axiom_statements"])))

    entered: dict[str, int] = {}
    for r in old_rows:
        for a in r[4]:
            entered[a] = entered.get(a, 0) + 1
    by_namespace: dict[str, int] = {}
    for n in restated:
        ns = n.rsplit(".", 1)[0]
        by_namespace[ns] = by_namespace.get(ns, 0) + 1
    doc = {
        "schema": "machsig-transition/v3",
        "binding": {
            "old_baseline_file": f"{BASE} at {OLD_REV} (master)",
            "old_baseline_role": "the LAST REVIEWED baseline at the anchor: the 2026-10-26 rebaseline, brought onto "
                                 "master by the merge commit 2431d705 (pull request #9)",
            "old_baseline_sha256": trust_gate.baseline_content_digest(old),
            "new_baseline_sha256": trust_gate.baseline_content_digest(new),
            "new_sources_commit": new["provenance"]["machlib_commit"],
        },
        "gate_transition": gt,
        "change": "hasDerivAt_implicit_local restated with ContinuousAt yc x and hasDerivAt_implicit made a theorem of "
                  "it (the old statements were false); 110 two-exp theorems gained hcont; HasDerivAt2_sub made a "
                  "theorem; thirteen axioms admitted to trustedFootprint on the owner's approval (HasDerivAt2, seven "
                  "of its rules, the local implicit form, floor and its three laws)",
        "row_kinds": dict(sorted(kinds.items())),
        "restated_theorems": restated,
        "entered_axioms_count": dict(sorted(entered.items())),
        "new_rows": new_rows,
        "checks": checks,
        "check_failures": fails,
        "statement_probe_sha256": hashlib.sha256(PROBE.read_bytes()).hexdigest(),
    }
    OUT_JSON.write_text(json.dumps(doc, indent=1, sort_keys=True) + "\n")

    desc = {
        "C1": "every restated theorem is its old statement plus one `hcont : … ContinuousAt …` binder (gate serializer)",
        "C2": "exactly `hasDerivAt_implicit_local` restated (old pin plus one `ContinuousAt`); the two converted axioms gone",
        "C3": "policy: `trusted` gains exactly the thirteen; `known` loses exactly the two converted; `allowed_sorry` unchanged",
        "C4": "every axiom entering an existing footprint is trusted; only the two converted axioms left any",
        "C5": "new rows = the controls module + two continuity helpers + the two converted theorems, all on trusted axioms",
        "C6": "the three control propositions are EXACTLY the two old axioms and the old curve-count statement",
        "C7": "the probe's serializer copies reproduce unchanged pins and digests",
        "C8": "each converted axiom is a theorem of exactly its axiom's type (master's pin; the restated pin)",
    }
    lines = [
        "# Transition 2026-10-27: the implicit-function repair, two conversions, thirteen axioms trusted",
        "",
        "Generated by `docs/machsig/transition_2026-10-27.py` (deterministic; rerun it to reproduce). The gate binds",
        "`binding` and `gate_transition` in `transition_2026-10-27.json`; this file is the reviewer's view of the same rows.",
        "",
        f"- Old baseline: `{BASE}` at `{OLD_REV[:8]}` (master), the last reviewed baseline (merged in pull request #9),",
        f"  content `{doc['binding']['old_baseline_sha256'][:23]}...`",
        f"- New baseline: sources at `{doc['binding']['new_sources_commit'][:8]}`, content `{doc['binding']['new_baseline_sha256'][:23]}...`",
        f"- Theorem rows: {len(rows)} ({', '.join(f'{k} {v}' for k, v in sorted(kinds.items()))})",
        "",
        "## The change",
        "",
        "1. `hasDerivAt_implicit` and `hasDerivAt_implicit_local` asked nothing of the curve `yc` but the curve identity,",
        "   and were false: `BivariateImplicitControls` derives `False` from each old statement, and `old_curve_count_false`",
        "   refutes the old `khovanskii_rolle_count_curve`. The local axiom now takes `ContinuousAt yc x`, and every theorem",
        "   that passed the curve identity on gained `hcont`.",
        "2. On the owner's ruling F1, two axioms the review found derivable are theorems of the same name and type:",
        "   `HasDerivAt2_sub` and the global `hasDerivAt_implicit` (of the local form). They leave every footprint they were",
        "   in, for the axioms their proofs use.",
        "3. The owner admitted thirteen axioms to `trustedFootprint`, each witnessed in monogate-lean",
        "   (`MachLibRealModelBivariate.lean`; the bridge reports 108/108 registered witnesses, 156 of 156 trusted",
        "   accounted for): " + ", ".join(short(a) for a in sorted(TRUSTED_ADDED)) + ".",
        "",
        "## Checks (each can fail; all must hold)",
        "",
        "| | check | holds |",
        "|---|---|---|",
    ]
    for k in sorted(checks):
        lines.append(f"| {k} | {desc[k]} | {'yes' if checks[k] else '**NO**'} |")
    lines += ["", "## Restated theorems by namespace", "", "| namespace | theorems |", "|---|---|"]
    for m, c in sorted(by_namespace.items()):
        lines.append(f"| `{m}` | {c} |")
    lines += ["", "## Axioms entering existing footprints", "", "| axiom | rows |", "|---|---|"]
    for a, c in sorted(entered.items()):
        lines.append(f"| {short(a)} | {c} |")
    lines += ["", "## New rows", ""] + [f"- `{n}`" for n in new_rows]
    lines += ["", "## Every row", "", "| theorem | kind | axioms before -> after | entered |", "|---|---|---|---|"]
    for r in rows:
        lines.append(f"| `{r[0]}` | {r[1]} | {r[2]} -> {r[3]} | {', '.join(short(a) for a in r[4])} |")
    OUT_MD.write_text("\n".join(lines) + "\n")
    print(f"rows {len(rows)} {kinds}; checks " + " ".join(f"{k}={'ok' if v else 'FAIL'}" for k, v in sorted(checks.items())))
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    raise SystemExit(main())
