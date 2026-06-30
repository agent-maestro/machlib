#!/usr/bin/env bash
# MachLib sorryAx regression gate. Exit 0 = no hidden sorries (only the documented allowlist);
# non-zero = a NON-allowlisted sorryAx appeared (e.g. the all-`try` mach_ring silently swallowed an
# unclosable goal into a green-compiling sorry). CI-ready.
set -u
HERE="$(cd "$(dirname "$0")/.." && pwd)"   # foundations/
cd "$HERE" || exit 2
exec lake env lean tools/sorry_audit.lean
