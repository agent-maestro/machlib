#!/usr/bin/env bash
# scripts/check_aggregator.sh — fail if a foundation module is UNREACHABLE
# from the aggregator root, so the "module exists but `lake build` never
# sees it" failure mode cannot silently recur.
#
# Why this exists:
#
# `lake build` builds `MachLib` = MachLib.lean + its TRANSITIVE imports.
# A `MachLib/**.lean` outside that cone is never built, never gated — it
# can break or grow a `sorry` unnoticed. This is a STATIC check (import
# lines only, no compilation), so it has no false positives from
# isolated-elaboration ambiguity (`lake env lean <file>` is NOT
# equivalent to `lake build` and must not be used as a per-file gate).
#
# ── 2026-08-10: TWO SCOPE DEFECTS FIXED. Both made the gate pass
#    truthfully about a set much smaller than the one it described.
#
#  (1) MAXDEPTH. The loop was `find MachLib -maxdepth 1`, so only
#      TOP-LEVEL modules were ever examined — while the header claimed
#      to cover "any .lean under MachLib/". 308 of 922 files live in
#      subdirectories and were invisible.

#
#  (2) ISLANDS — the deeper one. Reachability was tested as "is this
#      module imported by ANY .lean under MachLib/". That is not
#      reachability. A cluster of modules that import each other, which
#      nothing in the aggregator's cone imports, passes trivially: every
#      member is imported by a sibling. MachLib/Applications/ is exactly
#      such an island (12 modules), and four more top-level modules
#      turned out to be satellites of already-allowlisted orphans —
#      documented as entry points, with their members left unnamed.
#
#      The check is now a genuine transitive closure from MachLib.lean.
#
#      Applications/ RESOLVED the same day rather than left allow-listed:
#      the five broken modules failed on three `apply le_min` sites, in
#      files that `open MachLib.Real` AND
#      `open …AerospaceActuatorGuardBandRate (le_min …)`. Both `le_min`s
#      are the SAME theorem — identical statement and proof, and the local
#      one's docstring says "GLB intro for MachLib.Real.min" — so
#      qualifying is semantically neutral, not a guess. All 12 build and
#      are now in the aggregator.
#
#      Reachable modules: 616 of 922 (604 + the 12 folded-in Applications).
#
# Usage (from foundations/):   bash scripts/check_aggregator.sh
# Exit codes:  0 = clean   1 = a new unreachable module appeared

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

exec python3 - "--gate-path=${BASH_SOURCE[0]}" "$@" <<'PYEOF'
import os, re, sys, glob

# ── MachLib/Discovered/ is DELIBERATELY outside the aggregator: each file
#    is self-contained (defines its own constants) and they cannot be
#    imported together. Excluded by prefix rather than allow-listed 294
#    times.
#
#    2026-08-10: this note used to say "has its own harness,
#    scripts/closerate.sh" and stop there, which OVERCLAIMED — closerate
#    is a MEASUREMENT harness (it reports a close-rate, not pass/fail) and
#    CI does not run it. Those 294 files were outside every automated
#    check. `scripts/check_discovered_compiles.sh` is the minimum honest
#    guard and is now wired into CI; closerate.sh remains a manual sweep.
EXCLUDED_PREFIXES = ("MachLib.Discovered.",)

# ── Unreachable modules known at the 2026-08-10 audit. All BUILD; none
#    contains a real `sorry` (every `sorry` match under these paths was
#    checked individually and is prose in a docstring).
KNOWN_UNREACHABLE = {
    # --- top-level orphans documented at the 2026-06-26 audit (8)
    "MachLib.CatVision",
    "MachLib.ChainExp2NatMeasure",
    "MachLib.ChainExp2WFRPrecondInstance",
    "MachLib.GammaBarrier",
    "MachLib.LambertWFunctionalEquation",
    "MachLib.PolynomialCanonicalDegreeLemmas",
    "MachLib.Seal",
    "MachLib.Test",
    # --- satellites of those orphans, found 2026-08-10 by transitive
    #     closure. Each is imported ONLY by a module in the list above, so
    #     the old "imported by someone" test passed them.
    #     LambertWAsymptotics carries 7 theorems and 2 axioms that are
    #     therefore NOT in the axiom ledger (unreachable ⇒ not in the
    #     environment ⇒ nothing can depend on them).
    "MachLib.ChainExp2ListMeasuredInstance",
    "MachLib.InnerKhovanskiiExpListMeasured",
    "MachLib.InnerKhovanskiiExpWFRPrecond",
    "MachLib.LambertWAsymptotics",
}

# TEST SEAM, env-gated and used only by --selftest: lets the rot canary add an entry that is
# already reachable, so the stale-allowlist branch can be made to FIRE without editing this file.
# Nothing sets this in normal operation; it is named in the selftest output so it cannot hide.
KNOWN_UNREACHABLE |= {m for m in os.environ.get("AGG_SELFTEST_EXTRA", "").split() if m}

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.]+)")

def mod_of(path):
    return "MachLib." + path[len("MachLib/"):-len(".lean")].replace("/", ".")

def imports_of(path):
    out = []
    try:
        with open(path, encoding="utf-8", errors="replace") as fh:
            for line in fh:
                m = IMPORT_RE.match(line)
                if m:
                    out.append(m.group(1))
    except OSError:
        pass
    return out

# ── SELF-TEST ──────────────────────────────────────────────────────────────────────────────
# This gate produced "772 of 1078 reachable", a number copied into CLAUDE.md, with NO proof it
# could ever fail. Two canaries and a control, each re-invoking the REAL gate as a subprocess --
# testing a reimplementation of the decision would test the copy, not the gate.
if "--selftest" in sys.argv[1:]:
    import subprocess, tempfile
    gate = next((a.split("=", 1)[1] for a in sys.argv[1:] if a.startswith("--gate-path=")), None)
    if not gate:
        print("[selftest] FAIL: gate path not passed through", file=sys.stderr)
        sys.exit(1)

    def run(env_extra=None):
        env = dict(os.environ)
        if env_extra:
            env["AGG_SELFTEST_EXTRA"] = env_extra
        r = subprocess.run(["bash", gate], capture_output=True, text=True, env=env)
        return r.returncode, (r.stdout + r.stderr)

    orphan = "MachLib/_SelfTestOrphan.lean"
    failures = []
    try:
        with open(orphan, "w", encoding="utf-8") as fh:
            fh.write("-- transient, written and removed by check_aggregator.sh --selftest\n"
                     "namespace MachLib\nend MachLib\n")
        rc, out = run()
        fired = rc != 0 and "_SelfTestOrphan" in out
        print("   canary 1 (an unreachable, unallowlisted module is named)  %s"
              % ("FIRES" if fired else "SILENT — GATE IS BLIND"))
        if not fired:
            failures.append("unreachable module not detected")
    finally:
        if os.path.exists(orphan):
            os.remove(orphan)

    rc, out = run()
    quiet = rc == 0
    print("   canary 2 (control: clean tree passes)                      %s"
          % ("SILENT" if quiet else "FIRES — FALSE POSITIVE"))
    if not quiet:
        failures.append("clean tree rejected")

    rc, out = run(env_extra="MachLib.PolyLowestTerms")
    rot = rc != 0 and "STALE ALLOWLIST" in out
    print("   canary 3 (a stale allowlist entry is a FAILURE, not a note) %s"
          % ("FIRES" if rot else "SILENT — ROT IS UNGUARDED"))
    if not rot:
        failures.append("allowlist rot not detected")

    if failures:
        print("[check-aggregator] SELFTEST FAIL: " + "; ".join(failures), file=sys.stderr)
        sys.exit(1)
    print("[check-aggregator] SELFTEST PASS — all three specimens discriminate.")
    sys.exit(0)

files = {mod_of(f): f for f in glob.glob("MachLib/**/*.lean", recursive=True)}
if not files:
    print("[check-aggregator] FAIL: no modules found — wrong working directory?",
          file=sys.stderr)
    sys.exit(1)

# transitive closure from the aggregator root
seen, stack = set(), [m for m in imports_of("MachLib.lean") if m in files]
while stack:
    m = stack.pop()
    if m in seen:
        continue
    seen.add(m)
    stack.extend(i for i in imports_of(files[m]) if i in files and i not in seen)

new = sorted(
    m for m in set(files) - seen
    if not m.startswith(EXCLUDED_PREFIXES) and m not in KNOWN_UNREACHABLE
)

if new:
    for m in new:
        print(f"[check-aggregator] NEW UNREACHABLE: {files[m]}", file=sys.stderr)
        print(f"[check-aggregator]   → add 'import {m}' to MachLib.lean (or to a module",
              file=sys.stderr)
        print("[check-aggregator]     the aggregator already reaches), or it ships ungated.",
              file=sys.stderr)
        print("[check-aggregator]   NOTE: being imported by a sibling is NOT enough — an",
              file=sys.stderr)
        print("[check-aggregator]     island of mutually-importing modules is unreachable.",
              file=sys.stderr)
    print(f"[check-aggregator] FAIL: {len(new)} module(s) unreachable from MachLib.lean.",
          file=sys.stderr)
    sys.exit(1)

# ALLOWLIST ROT IS A FAILURE, NOT A NOTE (2026-08-31). It printed a note and then exited 0, so a
# stale entry could sit here forever. That is the same "standing licence" hazard `sorry_audit.lean`
# hard-fails on in BOTH directions -- and it rots in the direction that feels safe: someone wires a
# module in, nobody prunes the allowlist, and the entry silently re-licenses the next orphan with
# that name. Same suite, same hazard, opposite discipline until now.
stale = sorted(m for m in KNOWN_UNREACHABLE if m in seen or m not in files)
if stale:
    for m in stale:
        why = "now reachable" if m in seen else "no longer exists"
        print(f"[check-aggregator] STALE ALLOWLIST: {m} — {why}; remove it from "
              f"KNOWN_UNREACHABLE.", file=sys.stderr)
    print(f"[check-aggregator] FAIL: {len(stale)} allowlist entr(ies) no longer needed. "
          f"An unneeded licence is a licence for the next orphan.", file=sys.stderr)
    sys.exit(1)

print(f"[check-aggregator] PASS: {len(seen)} of {len(files)} modules reachable from "
      f"MachLib.lean by transitive closure; {len(KNOWN_UNREACHABLE)} documented "
      f"unreachable; Discovered/ excluded (guarded separately by "
      f"check_discovered_compiles.sh).")
sys.exit(0)
PYEOF
