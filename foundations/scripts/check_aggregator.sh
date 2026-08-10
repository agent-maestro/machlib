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

exec python3 - "$@" <<'PYEOF'
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

stale = sorted(m for m in KNOWN_UNREACHABLE if m in seen or m not in files)
if stale:
    print("[check-aggregator] NOTE: allowlist entries now reachable or deleted — "
          "remove them: " + ", ".join(stale), file=sys.stderr)

print(f"[check-aggregator] PASS: {len(seen)} of {len(files)} modules reachable from "
      f"MachLib.lean by transitive closure; {len(KNOWN_UNREACHABLE)} documented "
      f"unreachable; Discovered/ excluded (guarded separately by "
      f"check_discovered_compiles.sh).")
sys.exit(0)
PYEOF
