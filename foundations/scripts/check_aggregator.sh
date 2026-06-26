#!/usr/bin/env bash
# scripts/check_aggregator.sh — fail if a foundation module is ORPHANED
# (reachable from nothing), so the "module exists but `lake build` never
# sees it" failure mode cannot silently recur.
#
# Why this exists:
#
# `lake build` builds `MachLib` = MachLib.lean + its TRANSITIVE imports.
# A `MachLib/*.lean` that neither the aggregator nor any other module
# imports is never built, never gated — it can break or grow a `sorry`
# unnoticed. An audit found a cluster of such orphans. This is a STATIC
# check (grep only — no compilation), so it has no false positives from
# isolated-elaboration ambiguity (`lake env lean <file>` is NOT
# equivalent to `lake build` and must not be used as a per-file gate).
#
# A module is "reachable" if any .lean under MachLib/ imports it. The
# allowlist below freezes the orphans known at audit time (2026-06-26);
# a NEW orphan — a module reachable from nothing and not allow-listed —
# fails the gate. Shrink the allowlist as orphans are folded into the
# aggregator or deleted.
#
# Usage (from foundations/):
#   bash scripts/check_aggregator.sh
#
# Exit codes:
#   0  no un-allowlisted orphan modules
#   1  a new orphan module appeared (printed)

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

# Known orphans at audit time — exist + compile clean, but reachable
# from nothing. Documented here rather than silently un-gated. TODO:
# fold into the aggregator (resolving any isolated-elaboration ambiguity)
# or delete; then remove from this list.
KNOWN_ORPHANS="CatVision ChainExp2NatMeasure ChainExp2WFRPrecondInstance \
GammaBarrier LambertWFunctionalEquation PolynomialCanonicalDegreeLemmas \
Seal Test"

new_orphan=0
while IFS= read -r f; do
    mod="$(basename "$f" .lean)"
    # Reachable if ANY .lean under MachLib imports `MachLib.<mod>`.
    if grep -rqE "^import MachLib\.${mod}\b" MachLib.lean MachLib/*.lean 2>/dev/null; then
        continue
    fi
    case " $KNOWN_ORPHANS " in
        *" $mod "*) continue ;;  # known + documented
    esac
    echo "[check-aggregator] NEW ORPHAN: MachLib/${mod}.lean is imported by nothing" >&2
    echo "[check-aggregator]   → add 'import MachLib.${mod}' to MachLib.lean (or to a" >&2
    echo "[check-aggregator]     module the aggregator reaches), or it ships ungated." >&2
    new_orphan=1
done < <(find MachLib -maxdepth 1 -name '*.lean' | sort)

if [[ "$new_orphan" -ne 0 ]]; then
    echo "[check-aggregator] FAIL: an un-allowlisted orphan module appeared." >&2
    exit 1
fi
echo "[check-aggregator] PASS: every foundation module is reachable (or a documented orphan)."
exit 0
