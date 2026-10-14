#!/usr/bin/env python3
"""Regenerate the MachSig signature set for THIS tree, bound to the identity it was extracted from.

    python3 tools/machsig/regen.py          # from foundations/

WHY A DRIVER (2026-10-13). The documented chain was four commands run by hand
(extract_statement.lean, extract.lean, census.py, sig.py sigs). Nothing tied their output to the
tree they ran on, so a signature set extracted on 2026-09-03 was read by the trust gate for forty
days as if it described every later tree. This driver is now the only way to produce a set the gate
accepts: sig.py refuses raw extractions that do not carry the identity recorded here.

WHAT IT DOES, IN ORDER, AND WHY EACH STEP
  1. records the live identity (tools/machsig/identity.py): content digest of the Lean sources,
     extractor digest, commit, toolchain;
  2. `lake build` -- `lake env lean` loads whatever .olean files exist and does not check them
     against the sources, so extracting without building can read a stale environment;
  3. runs both Lean extractors (under tools/capped_lean.sh: this machine has been taken down by an
     unbounded elaboration before) into temporary files;
  4. recomputes the identity and REFUSES if anything moved while Lean ran -- the output would
     describe a tree that no longer exists;
  5. publishes the raw files with artifacts/machsig_extraction.json (identity + raw digests), then
     runs census.py --no-report and sig.py sigs.

v0.4 (2026-10-13): a third extractor, extract_trust.lean (axiom statements, the theorem population,
the definition-closure graph), and the declared POLICY -- AxiomLedger's knownAxioms and
trustedFootprint (probe.policy, AxiomLedger.lean's own text plus a probe) and sorry_audit.lean's
allowedSorry -- recorded in the identity, because the gate now judges every footprint against it.
MACHSIG_RUN_ID, when set (check_all.sh and CI set it), is recorded too: the gate then refuses a set
some other run produced, and without it prints that its verdict is advisory.

It writes only under artifacts/ (gitignored), so it is safe inside check_all.sh's tree freeze.

EXIT STATUS: 0 signature set written; 1 a step failed or the tree moved (nothing published);
2 UNAVAILABLE (no git, no lake).
"""
from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import identity  # noqa: E402
import probe  # noqa: E402

FOUND = identity.FOUND
ART = FOUND / "artifacts"
CAPPED = FOUND / "tools" / "capped_lean.sh"
EXTRACTORS = (("tools/machsig/extract_statement.lean", "machsig_stmt_raw.tsv", "machsig_stmt.err"),
              ("tools/machsig/extract_trust.lean", "machsig_trust_raw.tsv", "machsig_trust.err"),
              ("tools/machsig/extract.lean", "machsig_raw.tsv", "machsig_raw.err"))
ID_KEYS = ("machlib_commit", "content_digest", "extractor_digest", "lean_toolchain")


def run(cmd: list[str], out: Path | None = None, err: Path | None = None) -> int:
    o = open(out, "wb") if out else subprocess.DEVNULL
    e = open(err, "wb") if err else subprocess.DEVNULL
    try:
        return subprocess.run(cmd, cwd=FOUND, stdout=o, stderr=e).returncode
    finally:
        for fh in (o, e):
            if fh not in (subprocess.DEVNULL,):
                fh.close()


def capped(*cmd: str) -> list[str]:
    return ["bash", str(CAPPED), *cmd] if CAPPED.is_file() else list(cmd)


def main(argv: list[str]) -> int:
    if shutil.which("lake") is None:
        print("REGEN UNAVAILABLE -- `lake` is not on PATH")
        return 2
    try:
        pre = identity.live_identity(FOUND)
    except identity.Unavailable as e:
        print(f"REGEN UNAVAILABLE -- {e}")
        return 2
    ART.mkdir(exist_ok=True)
    print(f"regen: commit {pre['machlib_commit'][:12]}  sources {pre['content_digest'][:23]}...  "
          f"extractor {pre['extractor_digest'][:23]}...  {pre['lean_toolchain']}")
    if not pre["sources_clean"]:
        print(f"regen: NOTE -- {len(pre['dirty_source_paths'])} uncommitted source path(s); the set will "
              "describe the bytes on disk, and trust_gate.py --update will refuse to baseline it.")
    timings = {}
    t0 = time.monotonic()
    rc = run(capped("lake", "build"), ART / "machsig_build.log", ART / "machsig_build.log.err")
    timings["lake build"] = time.monotonic() - t0
    if rc != 0:
        print(f"REGEN FAILED -- `lake build` exit {rc} (see artifacts/machsig_build.log)")
        return 1
    r = subprocess.run(["lake", "env", "lean", "--version"], cwd=FOUND, capture_output=True, text=True)
    lean_version = (r.stdout or r.stderr).strip().splitlines()[0] if r.returncode == 0 else ""
    if not lean_version:
        print("REGEN UNAVAILABLE -- `lake env lean --version` failed")
        return 2
    for src, out, err in EXTRACTORS:
        t0 = time.monotonic()
        rc = run(capped("lake", "env", "lean", src), ART / (out + ".tmp"), ART / err)
        timings[src] = time.monotonic() - t0
        if rc != 0:
            print(f"REGEN FAILED -- {src} exit {rc} (see artifacts/{err}); nothing published")
            return 1
    t0 = time.monotonic()
    try:
        pol = probe.policy(FOUND)
        policy = {"known": pol["known"], "trusted": pol["trusted"], "allowed_sorry": probe.allowed_sorry(FOUND),
                  "axiom_ledger_rc": pol["axiom_ledger_rc"]}
    except (RuntimeError, OSError) as e:
        print(f"REGEN FAILED -- could not read the declared axiom policy: {e}")
        return 1
    timings["policy probe"] = time.monotonic() - t0
    post = identity.live_identity(FOUND)
    moved = [k for k in ID_KEYS if pre[k] != post[k]]
    if moved:
        print(f"REGEN REFUSED -- the tree changed while Lean ran ({', '.join(moved)}): "
              f"{identity.changed_files(pre['content_files'], post['content_files'])}. Nothing published.")
        for _, out, _ in EXTRACTORS:
            (ART / (out + ".tmp")).unlink(missing_ok=True)
        return 1
    raw = {}
    for _, out, _ in EXTRACTORS:
        os.replace(ART / (out + ".tmp"), ART / out)
        raw[out] = identity.sha256_file(ART / out)
    ident = {k: pre[k] for k in pre}
    ident.update({"schema": "machsig-extraction/v2", "lean_version": lean_version, "raw": raw, "policy": policy,
                  "run_id": os.environ.get("MACHSIG_RUN_ID") or None})
    tmp = ART / "machsig_extraction.json.tmp"
    tmp.write_text(json.dumps(ident, sort_keys=True, indent=1) + "\n")
    tmp.replace(ART / "machsig_extraction.json")
    for step in (["census.py", "--no-report"], ["sig.py", "sigs"]):
        t0 = time.monotonic()
        rc = subprocess.run([sys.executable, str(FOUND / "tools" / "machsig" / step[0]), *step[1:]],
                            cwd=FOUND).returncode
        timings[step[0]] = time.monotonic() - t0
        if rc != 0:
            print(f"REGEN FAILED -- {step[0]} exit {rc}")
            return 1
    print("regen: timings  " + "  ".join(f"{k} {v:.1f}s" for k, v in timings.items()))
    print(f"REGEN OK -- artifacts/machsig_signatures.jsonl bound to {pre['machlib_commit'][:12]} "
          f"({pre['content_digest'][:23]}...)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
