#!/usr/bin/env bash
# Run every MachLib gate and measurement harness, and EXIT NON-ZERO IF ANY OF THEM FAILS.
#
# WHY THIS EXISTS (2026-08-30). There was no single runner; sessions assembled one inline as a
# `{ gate1; gate2; ... }` block. Such a block exits with the status of its LAST command, so a run
# in which the claim audit failed reported `exit 0` — the failure was visible only because the
# audit's own verdict line happened to be printed and read. That is the same family as
# `gate | tail`, which reads `tail`'s status: A COMPOSITE'S EXIT CODE IS NOT ITS GATES'.
#
# Rules this script follows, each one a defect paid for previously:
#   * every gate's rc is captured IMMEDIATELY, before any pipe or echo can overwrite `$?`;
#   * nothing is piped in a way that discards a status — output goes to a file, then is read;
#   * UNAVAILABLE is distinguished from FAIL (exit 2), because "could not run" is not "passed";
#   * the summary names every non-passing gate, so a scrolled-off failure cannot hide;
#   * `--selftest` proves the runner CONDUCTS a failure to its own exit code.
#
# Usage:  tools/check_all.sh [--selftest]
#         cd foundations && tools/check_all.sh

set -u

HERE="$(cd "$(dirname "$0")/.." && pwd)"   # foundations/
cd "$HERE" || exit 2

OUT="$(mktemp -d)"
trap 'rm -rf "$OUT"' EXIT

FAILED=()
UNAVAIL=()
PASSED=()

# run NAME COMMAND...
#   Captures rc immediately. rc 0 = pass, rc 2 = unavailable, anything else = fail.
run() {
  local name="$1"; shift
  if ! command -v "${1}" >/dev/null 2>&1 && [ ! -e "${1}" ]; then
    UNAVAIL+=("$name (runner '${1}' not found)")
    return
  fi
  "$@" >"$OUT/$name.log" 2>&1
  local rc=$?
  case "$rc" in
    0) PASSED+=("$name") ;;
    2) UNAVAIL+=("$name (rc 2)") ;;
    *) FAILED+=("$name (rc $rc)") ;;
  esac
  # Surface the gate's own verdict line. The window is deliberately wide: several gates print
  # detail AFTER their verdict (the obligations ledger prints two count lines below its OK), so a
  # `tail -n 3` window silently dropped them. Cosmetic — SUMMARY decides pass/fail from the captured
  # rc, never from this text — but a comment that overstates what it does is how a gate's scope
  # drifts from its description.
  grep -hE "OBLIGATION-LEDGER|CLAIM-AUDIT|WITNESS-AUDIT|HYPOTHESIS-AUDIT|ABSENCE-AUDIT|SORRY-AUDIT|check-[a-z]+\]|AxiomLedger" \
    "$OUT/$name.log" | tail -n 2 || true
}

SELFTEST=0
if [ "${1:-}" = "--selftest" ]; then
  # Inject one passing and one failing gate, then fall through to the REAL summary and exit path.
  # Testing the accumulator alone would not catch the defect this script exists for: the bug was
  # never in detecting a failure, it was in the failure reaching the exit code.
  SELFTEST=1
  echo "=== SELFTEST: an injected failing gate must drive this script's own exit code ==="
  run "canary-pass" true
  run "canary-fail" false
else
  echo "=== MachLib: all gates + measurement harnesses ==="
  run "build"        lake build
  run "aggregator"   bash scripts/check_aggregator.sh
  run "consistency"  bash scripts/check_consistency_model.sh
  run "axiom-ledger" lake env lean AxiomLedger.lean
  run "obligations"  bash tools/check_obligations.sh
  run "discovered"   bash scripts/check_discovered_compiles.sh 4
  run "claims"       python3 tools/claim_audit/claim_audit.py
  run "witness"      python3 tools/witness_audit.py
  run "hypothesis"   python3 tools/hypothesis_audit.py
  run "absence"      python3 tools/absence_audit.py
  run "sorry"        lake env lean tools/sorry_audit.lean
fi

echo
echo "=== SUMMARY ==="
echo "passed:      ${#PASSED[@]}  (${PASSED[*]:-none})"
if [ ${#UNAVAIL[@]} -gt 0 ]; then
  echo "UNAVAILABLE: ${#UNAVAIL[@]}"
  for u in "${UNAVAIL[@]}"; do echo "   - $u"; done
fi
if [ ${#FAILED[@]} -gt 0 ]; then
  echo "FAILED:      ${#FAILED[@]}"
  for f in "${FAILED[@]}"; do
    echo "   - $f"
    echo "     ---- last 12 lines ----"
    sed 's/^/     /' "$OUT/${f%% *}.log" | tail -n 12
  done
  exit 1
fi
if [ ${#UNAVAIL[@]} -gt 0 ]; then
  echo "VERDICT: gates green, but ${#UNAVAIL[@]} could not run — treat as UNKNOWN, not PASS."
  exit 2
fi
echo "VERDICT: all ${#PASSED[@]} green."
exit 0
