#!/usr/bin/env bash
# Consistency-model gate.
#
# `MachLib.Model.intModel` witnesses that the flagship axiom closure has a model
# in ℤ — hence is consistent (cannot prove False), hence the flagship results are
# not vacuous. That argument only holds if `intModel` is a GENUINE EXTERNAL model:
# it must depend on NONE of MachLib's own axioms (only Lean's core axioms). If a
# future edit accidentally makes `intModel` use a `MachLib.Real.*` axiom, the
# model becomes circular and the consistency claim silently collapses.
#
# This gate re-derives `#print axioms intModel` and fails if any `MachLib.Real`
# axiom appears. Run from the `foundations/` dir (or via the build system).
set -euo pipefail
cd "$(dirname "$0")/.."

LEAN="$(command -v lean || echo "$HOME/.elan/toolchains/leanprover--lean4---v4.14.0/bin/lean")"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cat > "$TMP/check.lean" <<'EOF'
import MachLib.CoreModel
open MachLib.Model
#print axioms intModel
EOF

OUT="$(env LEAN_PATH=./.lake/build/lib LD_LIBRARY_PATH= "$LEAN" "$TMP/check.lean" -R . 2>&1)"

if echo "$OUT" | grep -q "MachLib\.Real"; then
  echo "[check-consistency] FAIL: intModel depends on a MachLib axiom — the consistency"
  echo "                    model is CIRCULAR. The flagship closure is no longer proven"
  echo "                    consistent by an external (ℤ) model. Offending axioms:"
  echo "$OUT" | grep "MachLib\.Real" | sed 's/^/                      /'
  exit 1
fi

if ! echo "$OUT" | grep -q "intModel.*depends on axioms"; then
  echo "[check-consistency] FAIL: could not read intModel's axiom set:"
  echo "$OUT"
  exit 1
fi

echo "[check-consistency] PASS: intModel is a genuine external (ℤ) model of the flagship"
echo "                    closure — Lean-core axioms only, no MachLib axiom. The"
echo "                    flagship results' axiom base is machine-checked consistent."
