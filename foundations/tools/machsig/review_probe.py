#!/usr/bin/env python3
"""Lean probes used only by REVIEW tooling (targeted_check.py), kept out of probe.py on purpose:
probe.py is an extractor file (regen.py reads the declared policy through it), so anything added
there changes the extractor digest and makes every signature set stale. Nothing here decides what a
signature says.
"""
from __future__ import annotations

import tempfile
from pathlib import Path

from probe import _run_lean


REACH_PROBE = r'''import MachLib
open Lean Elab Command Meta

/- Independent of extract_trust.lean's edge rule: Lean's own ConstantInfo.getUsedConstantsAsSet, which
   also follows theorem PROOFS, so it reaches a SUPERSET of what the closure digest covers. A pair the
   superset walk cannot reach is a pair the digest got wrong. -/
run_cmd Command.liftTermElabM do
  let env ← getEnv
  let pairs ← IO.FS.lines "@@PAIRS@@"
  for ln in pairs do
    match ln.splitOn "|" with
    | [t, c] =>
      let target := c.toName
      let mut seen : NameSet := {}
      let mut stack : Array Name := match env.find? t.toName with
        | some ci => ci.type.getUsedConstants
        | none => #[]
      let mut hit := false
      while !stack.isEmpty && !hit do
        let n := stack.back!
        stack := stack.pop
        if seen.contains n then continue
        seen := seen.insert n
        if n == target then hit := true
        match env.find? n with
        | some ci => for m in ci.getUsedConstantsAsSet.toList do
            if !seen.contains m then stack := stack.push m
        | none => pure ()
      IO.println s!"MACHSIG_REACH\t{t}\t{c}\t{hit}"
    | _ => pure ()
'''


def reaches(root: Path, pairs: list[tuple[str, str]]) -> dict:
    """{(theorem, constant): bool}: does the theorem's statement reach the constant through Lean's own
    used-constant relation (definitions AND proofs)?"""
    with tempfile.TemporaryDirectory(prefix="machsig-pairs-") as td:
        pf = Path(td) / "pairs.txt"
        pf.write_text("\n".join(f"{a}|{b}" for a, b in sorted(set(pairs))) + "\n")
        rc, out = _run_lean(root, REACH_PROBE.replace("@@PAIRS@@", str(pf)))
    res = {}
    for ln in out.splitlines():
        if ln.startswith("MACHSIG_REACH\t"):
            _, a, b, h = ln.split("\t")
            res[(a, b)] = h == "true"
    if rc != 0 or len(res) != len(set(pairs)):
        raise RuntimeError(f"reach probe rc {rc}, {len(res)}/{len(set(pairs))}: {out[-800:]}")
    return res


def print_decls(root: Path, names: list[str]) -> dict:
    """{name: the text `#print name` gives}: Lean's own rendering of a declaration, body included."""
    body = "import MachLib\nset_option pp.proofs true\nset_option pp.explicit true\nset_option pp.funBinderTypes true\n" + "".join(
        f"#eval IO.println \"@@MACHSIG_DECL {n}\"\n#print {n}\n" for n in sorted(set(names)))
    rc, out = _run_lean(root, body)
    res, cur, buf = {}, None, []
    for ln in out.splitlines():
        if ln.startswith("@@MACHSIG_DECL "):
            if cur is not None:
                res[cur] = "\n".join(buf).strip()
            cur, buf = ln[len("@@MACHSIG_DECL "):].strip(), []
        elif cur is not None:
            buf.append(ln)
    if cur is not None:
        res[cur] = "\n".join(buf).strip()
    if rc != 0 or len(res) != len(set(names)):
        raise RuntimeError(f"#print probe rc {rc}, {len(res)}/{len(set(names))}: {out[-800:]}")
    return res
