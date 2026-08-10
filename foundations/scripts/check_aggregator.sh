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
# 2026-08-10 — MAXDEPTH BLIND SPOT FIXED. This script iterated
# `find MachLib -maxdepth 1`, so it only ever checked TOP-LEVEL modules,
# while its own description claims to check "any .lean under MachLib/".
# An orphan in a subdirectory could never fail it. Found by counting:
# 922 .lean files under MachLib/, 614 top-level, and the gate green.
# It now walks the whole tree, with two documented exclusions below.
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

# MachLib/Discovered/ is DELIBERATELY out of the aggregator: each file is
# self-contained (defines its own constants) and they cannot be imported
# together. It is the Forge @verify(lean) corpus and has its own harness,
# `scripts/closerate.sh`. Excluded here rather than allow-listed 294 times.
EXCLUDED_DIRS="MachLib/Discovered"

# Subdirectory orphans known at the 2026-08-10 audit. The Applications/
# cluster is reachable from nothing AND five of its twelve modules do not
# build — `apply le_min` is ambiguous between `MachLib.Real.le_min` and the
# namespace-local `AerospaceActuatorGuardBandRate.le_min`. That is exactly
# the "isolated-elaboration ambiguity" this script's header anticipated.
# These are aerospace actuator guard proofs; resolving the ambiguity is a
# semantic decision, not a rename, so it is left to a deliberate pass.
#   BUILDS : GuardedActuatorCommand ActuatorCommandWithinBand
#            ActuatorCommandBandWithRateLimit ButlerVolmerKhovanskii
#            DischargeVoltageSafety PlasmaConcentrationNonneg
#            SpringCriticallyDamped
#   BROKEN : ActuatorCommandWithJerkLimit ActuatorCommandWithSnapLimit
#            ActuatorCommandWithCrackleLimit DegradedModeSwitcher
#            FaultDetectionAndIsolationGuard
KNOWN_SUBDIR_ORPHANS="MachLib.Applications.ActuatorCommandBandWithRateLimit \
MachLib.Applications.ActuatorCommandWithCrackleLimit \
MachLib.Applications.ActuatorCommandWithJerkLimit \
MachLib.Applications.ActuatorCommandWithSnapLimit \
MachLib.Applications.ActuatorCommandWithinBand \
MachLib.Applications.ButlerVolmerKhovanskii \
MachLib.Applications.DegradedModeSwitcher \
MachLib.Applications.DischargeVoltageSafety \
MachLib.Applications.FaultDetectionAndIsolationGuard \
MachLib.Applications.GuardedActuatorCommand \
MachLib.Applications.PlasmaConcentrationNonneg \
MachLib.Applications.SpringCriticallyDamped"

new_orphan=0
while IFS= read -r f; do
    # skip deliberately-separate trees
    skip=0
    for d in $EXCLUDED_DIRS; do
        case "$f" in "$d"/*) skip=1 ;; esac
    done
    [[ "$skip" -eq 1 ]] && continue

    # MachLib/A/B/Foo.lean -> MachLib.A.B.Foo
    rel="${f#MachLib/}"; rel="${rel%.lean}"
    mod="MachLib.${rel//\//.}"
    short="$(basename "$f" .lean)"

    # Reachable if ANY .lean under MachLib imports it (recursive).
    if grep -rqE "^import ${mod//./\\.}\b" MachLib.lean MachLib/ 2>/dev/null; then
        continue
    fi
    case " $KNOWN_ORPHANS " in
        *" $short "*) continue ;;          # known top-level, documented
    esac
    case " $KNOWN_SUBDIR_ORPHANS " in
        *" $mod "*) continue ;;            # known subdirectory, documented
    esac
    echo "[check-aggregator] NEW ORPHAN: ${f} is imported by nothing" >&2
    echo "[check-aggregator]   → add 'import ${mod}' to MachLib.lean (or to a" >&2
    echo "[check-aggregator]     module the aggregator reaches), or it ships ungated." >&2
    new_orphan=1
done < <(find MachLib -name '*.lean' | sort)

if [[ "$new_orphan" -ne 0 ]]; then
    echo "[check-aggregator] FAIL: an un-allowlisted orphan module appeared." >&2
    exit 1
fi
echo "[check-aggregator] PASS: every module under MachLib/ is reachable (or a documented orphan); Discovered/ excluded (own harness: scripts/closerate.sh)."
exit 0
