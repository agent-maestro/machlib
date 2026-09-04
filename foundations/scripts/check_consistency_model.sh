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
# This gate re-derives `#print axioms intModel` and fails if ANY axiom outside
# Lean's own core appears. Run from the `foundations/` dir (or via the build system).
#
# ── 2026-08-10: PREDICATE WIDENED TO MATCH THE STATED INTENT. The check was
#    `grep -q "MachLib\.Real"`, but the paragraph above says intModel "must
#    depend on NONE of MachLib's own axioms (only Lean's core axioms)". Those
#    are different sets: `Certcom.*` (22 IEEE-754 floor axioms),
#    `MachLib.IsAnalyticOnReals` and `MachLib.analytic_*` are all project
#    axioms that the old pattern did not match. A future edit pulling one of
#    them into intModel would have made the model circular with the gate
#    still green. Now: allowlist Lean core, fail on everything else.
#
#    Optional arg: a declaration name to check instead of intModel, so the
#    gate can be exercised on a firing specimen through its real code path.
set -euo pipefail
cd "$(dirname "$0")/.."

LEAN="$(command -v lean || echo "$HOME/.elan/toolchains/leanprover--lean4---v4.14.0/bin/lean")"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
DECL="${1:-MachLib.Model.intModel}"
cat > "$TMP/check.lean" <<EOF
import MachLib
#print axioms $DECL
EOF

# Lake nests the olean tree under lib/lean/ since the v4.32.2 bump; older layouts
# put it directly in lib/. Accept either, and FAIL LOUDLY if lean itself errors —
# a gate that cannot run is not a gate that passed.
if [ "${SELFTEST:-}" = "1" ]; then
  fail=0
  CORE_OUT="MachLib.intModel depends on axioms: [propext, Classical.choice, Quot.sound]"
  PROJ_OUT="MachLib.intModel depends on axioms: [propext, MachLib.Real.addR, Quot.sound]"

  # `set -e` is active: a bare failing command would abort this block before the test, so each
  # specimen is run inside `if !` where a non-zero status is expected rather than fatal.
  # It is not enough that this FIRES: an earlier draft seeded output without "intModel" and fired on
  # the PARSE branch instead, which would have passed a did-it-go-red test while proving nothing
  # about the subset check. So the specimen asserts WHICH branch convicted.
  c1out="$(MACHLIB_CONSISTENCY_SEED_OUT="$PROJ_OUT" SELFTEST= bash "${BASH_SOURCE[0]}" 2>&1 || true)"
  if printf '%s' "$c1out" | grep -q "NON-CORE axiom"
  then echo "[check-consistency] selftest canary 1 (a PROJECT axiom) FIRES on the subset branch"
  else echo "[check-consistency] selftest canary 1 BROKEN - a project axiom passed" >&2; fail=1; fi

  if ! MACHLIB_CONSISTENCY_SEED_OUT="no axiom list here" SELFTEST= bash "${BASH_SOURCE[0]}" >/dev/null 2>&1
  then echo "[check-consistency] selftest canary 2 (unparseable output) FIRES"
  else echo "[check-consistency] selftest canary 2 BROKEN - unparseable output passed" >&2; fail=1; fi

  if MACHLIB_CONSISTENCY_SEED_OUT="$CORE_OUT" SELFTEST= bash "${BASH_SOURCE[0]}" >/dev/null 2>&1
  then echo "[check-consistency] selftest canary 3 (control: core-only) stays SILENT"
  else echo "[check-consistency] selftest canary 3 BROKEN - core-only convicted" >&2; fail=1; fi

  [ "$fail" -eq 0 ] && echo "[check-consistency] SELFTEST PASS - 2 specimens fire, 1 control silent"
  exit "$fail"
fi

LIB="./.lake/build/lib/lean"
[ -d "$LIB" ] || LIB="./.lake/build/lib"

# TEST SEAM, env-gated, used only by --selftest: supply the `#print axioms` output directly, so the
# PARSER and the subset DECISION run without invoking Lean. The expensive half of this gate is
# producing that line; the half that can be wrong is reading it. Nothing sets this in normal use.
if [ -n "${MACHLIB_CONSISTENCY_SEED_OUT+x}" ]; then
  OUT="$MACHLIB_CONSISTENCY_SEED_OUT"
elif ! OUT="$(env LEAN_PATH="$LIB" LD_LIBRARY_PATH= "$LEAN" "$TMP/check.lean" -R . 2>&1)"; then
  echo "[check-consistency] FAIL: could not RUN the check (lean exited non-zero)."
  echo "                    LEAN=$LEAN  LEAN_PATH=$LIB"
  echo "$OUT" | sed 's/^/                      /'
  exit 1
fi

# Lean's own trust base. ANYTHING else is a project axiom and makes the model
# non-external. Kept explicit so widening it is a deliberate, reviewable act.
LEAN_CORE="propext Classical.choice Quot.sound sorryAx Quot.lcInv \
Lean.ofReduceBool Lean.ofReduceNat Lean.trustCompiler isScalarObj \
lcAny lcCast lcErased lcProof lcUnreachable lcVoid"

FOUND="$(printf '%s' "$OUT" | tr -d '\n' | sed -n 's/.*depends on axioms: \[\([^]]*\)\].*/\1/p' \
         | tr ',' '\n' | sed 's/^ *//; s/ *$//' | grep -v '^$')"

if [ -z "$FOUND" ]; then
  echo "[check-consistency] FAIL: could not parse an axiom list out of #print axioms."
  echo "$OUT" | sed 's/^/                      /'
  exit 1
fi

OFFENDING=""
while IFS= read -r ax; do
  case " $LEAN_CORE " in *" $ax "*) continue ;; esac
  OFFENDING="$OFFENDING $ax"
done <<< "$FOUND"

if [ -n "$OFFENDING" ]; then
  echo "[check-consistency] FAIL: $DECL depends on a NON-CORE axiom — the consistency"
  echo "                    model is CIRCULAR. The flagship closure is no longer proven"
  echo "                    consistent by an external (ℤ) model. Offending axioms:"
  for ax in $OFFENDING; do echo "                      $ax"; done
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
