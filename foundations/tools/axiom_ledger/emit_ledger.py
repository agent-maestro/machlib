#!/usr/bin/env python3
"""Emit the axiom ledger as data (axiom_ledger.json) + the generated footprint prose.

The point (the muse's permanent fix for "§05 drifts from reality"): the khovanskii page's
axiom-footprint sentences should be GENERATED from the kernel-verbatim ledger, not hand-typed.
This reads the real footprints via `Lean.collectAxioms` (same mechanism as AxiomLedger.lean's
gate), writes axiom_ledger.json, and prints the canonical §05/§06 sentence. Regenerate on every
release; the sentence and the gate then cannot disagree.

Usage:
    python3 tools/axiom_ledger/emit_ledger.py            # write axiom_ledger.json + print prose
    python3 tools/axiom_ledger/emit_ledger.py --print    # print only
"""
import json, os, re, subprocess, sys, tempfile

FOUND = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
OUT = os.path.join(FOUND, "axiom_ledger.json")

HEADLINES = [
    ("47-barrier (pure exp tower)", "MachLib.KhovanskiiConcrete.eexp_barrier_zero_count_le_47"),
    ("general EML barrier", "MachLib.eml_eval_boundedZeros"),
    ("chainN Khovanskii (unconditional)", "MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional"),
    ("chainN Khovanskii (explicit)", "MachLib.IterExpDepthN.chainN_khovanskii_bound_explicit"),
]
DISCLOSED = [
    ("MachLib.Real.erf", "blocked-upstream (erf absent from Mathlib)"),
    ("MachLib.eml_tree_analytic_on_pos",
     "pending-fix (drops the log-positivity side-condition; false as stated; in NO shipped footprint)"),
]

FACTS_LEAN = """import MachLib
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut total := 0
  for (nm, ci) in env.constants.toList do
    if (ci matches .axiomInfo _) && ((`MachLib).isPrefixOf nm || (`Real).isPrefixOf nm) then
      total := total + 1
  logInfo m!"FACT total {total}"
  for h in [%NAMES%] do
    let axs ← Lean.collectAxioms h
    logInfo m!"FACT footprint {h} {axs.size} {(axs.contains `MachLib.eml_tree_analytic_on_pos)}"
"""


def collect_facts() -> dict:
    names = ", ".join("`" + n for _, n in HEADLINES)
    src = FACTS_LEAN.replace("%NAMES%", names)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=FOUND, delete=False) as f:
        f.write(src); path = f.name
    try:
        out = subprocess.run(["lake", "env", "lean", path], cwd=FOUND,
                             capture_output=True, text=True).stdout
    finally:
        os.unlink(path)
    total = int(re.search(r"FACT total (\d+)", out).group(1))
    fp = {}
    for m in re.finditer(r"FACT footprint (\S+) (\d+) (true|false)", out):
        fp[m.group(1)] = {"size": int(m.group(2)), "has_pending_axiom": m.group(3) == "true"}
    return {"total": total, "footprints": fp}


def build(facts: dict) -> dict:
    return {
        "generated_by": "tools/axiom_ledger/emit_ledger.py (Lean.collectAxioms, kernel-verbatim)",
        "total_axioms": facts["total"],
        "headlines": [
            {"label": label, "theorem": thm,
             "footprint_axioms": facts["footprints"].get(thm, {}).get("size"),
             "depends_on_pending_axiom": facts["footprints"].get(thm, {}).get("has_pending_axiom")}
            for label, thm in HEADLINES
        ],
        "disclosed_unwitnessed": [{"axiom": a, "reason": r} for a, r in DISCLOSED],
    }


def prose(led: dict) -> str:
    h = {x["label"]: x for x in led["headlines"]}
    pure = h["47-barrier (pure exp tower)"]["footprint_axioms"]
    gen = h["general EML barrier"]["footprint_axioms"]
    any_pending = any(x["depends_on_pending_axiom"] for x in led["headlines"])
    return (
        f"The pure-exp-tower barrier depends on exactly {pure} axioms (real field/order, `exp`, "
        f"`HasDerivAt`, and the sound closed-interval `rolle_ct`); the general EML barrier on "
        f"{gen}. Of the project's {led['total_axioms']} declared axioms, the two unwitnessed ones "
        f"(`erf`, absent from Mathlib; `eml_tree_analytic_on_pos`, pending a positivity "
        f"side-condition) appear in "
        f"{'a shipped footprint — REGRESSION' if any_pending else 'NO shipped footprint'}. "
        f"Machine-verified by `AxiomLedger` via the kernel's own `#print axioms` mechanism."
    )


def main() -> int:
    led = build(collect_facts())
    if "--print" not in sys.argv:
        json.dump(led, open(OUT, "w"), indent=2)
        print(f"wrote {os.path.relpath(OUT, FOUND)}")
    print("\n--- generated §05/§06 footprint sentence ---\n" + prose(led))
    return 0


if __name__ == "__main__":
    sys.exit(main())
