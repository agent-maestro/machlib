#!/usr/bin/env bash
# MachLib obligations-ledger gate. The named-obligation table at the end of
# MachLib/EMLDepthTameness.lean records, per obligation, whether it is open or discharged.
# "Discharged" was always machine-checkable; "open" was not — absence of a proof is not a
# theorem — so the column was hand-maintained and could rot silently.
#
# This gate checks BOTH directions against the corpus: exit 0 = every row matches; 1 = a row
# marked open is in fact discharged (stale), or a row marked discharged names a theorem that
# does not conclude it; 2 = the ledger could not be read (UNAVAILABLE, not a pass).
# Runs the canary self-test too. CI-ready.
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"   # foundations/
cd "$HERE" || exit 2
exec python3 tools/obligation_ledger_check.py --self-test
