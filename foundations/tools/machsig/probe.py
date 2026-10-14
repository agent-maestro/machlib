#!/usr/bin/env python3
"""Small Lean probes for MachSig REVIEW tooling (transition.py, targeted_check.py). Not part of the
extractor: nothing here decides what a signature says, so it is outside identity.EXTRACTOR_FILES.

  policy(root)               AxiomLedger.lean's live knownAxioms and trustedFootprint, read the way
                             tools/theorem_ledger/ledger.py reads them: AxiomLedger.lean's own text
                             with a probe appended, so no list is copied.
  statements(root, names)    each theorem's pretty-printed statement and source position.
  print_axioms(root, names)  the literal `#print axioms` output for each theorem -- the command a
                             reader would type -- parsed into sets. This is the targeted check: it
                             goes through Lean's front end, not through extract.lean.

Every probe runs under tools/capped_lean.sh with `lake env lean` from `root` (a foundations/ dir),
so it reads that tree's built environment. Build the tree first.
"""
from __future__ import annotations

import json
import re
import subprocess
import tempfile
from pathlib import Path

POLICY_PROBE = r'''

open Lean in
#eval IO.println ("MACHSIG_POLICY " ++ (Json.mkObj [
  ("known", toJson (AxiomLedger.knownAxioms.map (·.toString))),
  ("trusted", toJson (AxiomLedger.trustedFootprint.map (·.toString)))]).compress)
'''

STATEMENT_PROBE = r'''import MachLib
open Lean Elab Command Meta

set_option pp.oneline false
run_cmd Command.liftTermElabM do
  let names ← IO.FS.lines "@@NAMES@@"
  let env ← getEnv
  for s in names do
    if s.isEmpty then continue
    let n := s.toName
    match env.find? n with
    | none => IO.println ("MACHSIG_STMT " ++ (Json.mkObj [("n", Json.str s), ("missing", Json.bool true)]).compress)
    | some ci =>
      let fmt ← ppExpr ci.type
      let mod := match env.getModuleIdxFor? n with
        | some i => (env.header.moduleNames[i.toNat]!).toString
        | none => "<current>"
      let rng ← findDeclarationRanges? n
      let line := match rng with
        | some r => r.range.pos.line
        | none => 0
      IO.println ("MACHSIG_STMT " ++ (Json.mkObj [("n", Json.str s), ("type", Json.str (toString fmt)),
        ("module", Json.str mod), ("line", toJson line)]).compress)
'''


def _run_lean(root: Path, text: str, timeout: int = 3600) -> tuple[int, str]:
    with tempfile.TemporaryDirectory(prefix="machsig-probe-") as td:
        f = Path(td) / "Probe.lean"
        f.write_text(text)
        cmd = ["lake", "env", "lean", str(f)]
        capped = root / "tools" / "capped_lean.sh"
        if capped.is_file():
            cmd = ["bash", str(capped), *cmd]
        r = subprocess.run(cmd, cwd=root, capture_output=True, text=True, timeout=timeout)
        return r.returncode, r.stdout + r.stderr


def policy(root: Path) -> dict:
    rc, out = _run_lean(root, (root / "AxiomLedger.lean").read_text() + POLICY_PROBE)
    for ln in out.splitlines():
        if ln.startswith("MACHSIG_POLICY "):
            j = json.loads(ln[len("MACHSIG_POLICY "):])
            return {"known": sorted(set(j["known"])), "trusted": sorted(set(j["trusted"])),
                    "axiom_ledger_rc": rc}
    raise RuntimeError(f"policy probe printed no MACHSIG_POLICY line (rc {rc}): {out[-800:]}")


def statements(root: Path, names: list[str]) -> dict:
    with tempfile.TemporaryDirectory(prefix="machsig-names-") as td:
        nf = Path(td) / "names.txt"
        nf.write_text("\n".join(sorted(set(names))) + "\n")
        rc, out = _run_lean(root, STATEMENT_PROBE.replace("@@NAMES@@", str(nf)))
    res = {}
    for ln in out.splitlines():
        if ln.startswith("MACHSIG_STMT "):
            j = json.loads(ln[len("MACHSIG_STMT "):])
            res[j["n"]] = j
    if rc != 0 or len(res) != len(set(names)):
        raise RuntimeError(f"statement probe rc {rc}, {len(res)}/{len(set(names))} names: {out[-800:]}")
    return res


# Names may end in an apostrophe (`log_nonpos_of_le_one'`), so the name is the shortest run of
# non-space characters that is followed by "' depends" / "' does not" -- not "anything up to a quote".
AX_LINE = re.compile(r"'(\S+?)' (depends on axioms: \[(.*?)\]|does not depend on any axioms)", re.S)


def print_axioms(root: Path, names: list[str]) -> dict:
    """{name: sorted axiom list} from the literal `#print axioms`, for every name."""
    body = "import MachLib\nset_option format.width 1000000\n" + \
        "".join(f"#print axioms {n}\n" for n in sorted(set(names)))
    rc, out = _run_lean(root, body)
    res = {}
    for m in AX_LINE.finditer(out):
        if m.group(3) is None:
            res[m.group(1)] = []
        else:
            res[m.group(1)] = sorted(a.strip() for a in m.group(3).replace("\n", " ").split(",") if a.strip())
    if rc != 0 or len(res) != len(set(names)):
        raise RuntimeError(f"#print axioms probe rc {rc}, parsed {len(res)}/{len(set(names))}: {out[-800:]}")
    return res
