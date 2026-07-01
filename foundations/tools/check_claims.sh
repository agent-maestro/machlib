#!/usr/bin/env bash
# MachLib claim-audit gate. Exit 0 = every registered prose claim ("proven",
# "no sorryAx", "dirty-axiom-free", …) matches the actual #print axioms footprint of
# the theorem it cites; non-zero = a headline outran its trail. Runs the canary
# self-test too (proves the gate goes red on a known violation). CI-ready.
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"   # foundations/
cd "$HERE" || exit 2
exec python3 tools/claim_audit/claim_audit.py --self-test
