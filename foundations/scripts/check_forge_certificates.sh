#!/usr/bin/env bash
# scripts/check_forge_certificates.sh — every Forge proof-carrying certificate must CHECK.
#
# WHY THIS EXISTS (2026-09-01).
#
# Forge's numerical-stability pass emits Lean files into foundations/ForgeCheck/, each headed
# "PROOF-CARRYING" and each asserting an accuracy bound with its assumptions pinned. They arrived in
# this tree untracked and UNREFERENCED BY ANY GATE. Nothing checked the proof they carry.
#
# One of the first three did not typecheck. Its failure mode -- `relBound <= (inf : Real)`, where
# `inf` is Python's float('inf') formatted straight into a Lean numeral -- is one FORGE ITSELF HAD
# ALREADY FIXED (`_required_literal` returns a finite stand-in). So the artifact was older than its
# generator, and being ungated it never said so. Forge's own source comments the same discovery
# twice: "Nothing noticed for as long as no checker could read the artifact."
#
# That is the seam this gate seals. It does NOT extend the certificates' scope, verify their
# assumptions, or claim the bounds are true -- only that each file the generator emitted is one Lean
# can actually check. A proof-carrying artifact nobody checks is a claim, not a proof.
#
# DISCIPLINE, each item paid for elsewhere in this repo:
#   * a KNOWN_BROKEN entry is a licence, so ROT FAILS IN BOTH DIRECTIONS -- an entry whose file now
#     checks, or no longer exists, fails the gate (sorry_audit.lean, 2026-07-29; ported to
#     check_aggregator.sh and check_discovered_compiles.sh, 2026-08-31);
#   * --selftest carries a firing specimen AND a control, because a gate with no specimen is
#     unvalidated (feedback_gate_specimen_discipline);
#   * every rc is captured immediately, before any pipe can overwrite $? (check_all.sh's reason for
#     existing).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"   # foundations/
cd "$HERE" || exit 2

DIR="ForgeCheck"

# Certificates known not to check, with the reason and the remedy. NOT a licence to leave them
# broken: each entry names what must happen for it to be removed.
#
#   norm2_q16_16_dag.lean -- emits `relBound <= (inf : Real)` from an UNBOUNDED relative-error
#     contract. Forge's _required_literal already returns "1000000000.0" for non-finite bounds, so
#     this artifact PREDATES the fix. Remedy: REGENERATE from the current generator. Do not hand-edit
#     a generated file.
KNOWN_BROKEN="norm2_q16_16_dag.lean"

# TEST SEAM, env-gated, used only by --selftest so the rot branch can be made to FIRE without
# editing this file. Nothing sets it in normal operation and it is echoed in the selftest output.
KNOWN_BROKEN="$KNOWN_BROKEN ${FORGECERT_SELFTEST_EXTRA:-}"

# ── SELF-TEST ──────────────────────────────────────────────────────────────────────────────────
# A firing specimen, a control, and the rot branch. Each re-invokes the REAL gate as a subprocess:
# testing a reimplementation of the decision would test the copy, not the gate.
if [ "${1:-}" = "--selftest" ]; then
  fail=0
  canary="$DIR/_selftest_broken_cert.lean"
  cat > "$canary" <<'CANEOF'
-- transient, written and removed by check_forge_certificates.sh --selftest
theorem forge_cert_selftest_canary : (1 : Nat) = 1 := by
  exact this_tactic_does_not_exist
CANEOF
  out="$(bash "${BASH_SOURCE[0]}" 2>&1)"; rc=$?
  rm -f "$canary"
  if [ "$rc" -ne 0 ] && printf '%s' "$out" | grep -q "_selftest_broken_cert"; then
    echo "   canary 1 (a certificate that does not check is NAMED)      FIRES"
  else
    echo "   canary 1 (a certificate that does not check is NAMED)      SILENT — GATE IS BLIND"
    fail=1
  fi

  out="$(bash "${BASH_SOURCE[0]}" 2>&1)"; rc=$?
  if [ "$rc" -eq 0 ]; then
    echo "   canary 2 (control: the real tree passes)                   SILENT"
  else
    echo "   canary 2 (control: the real tree passes)                   FIRES — FALSE POSITIVE"
    fail=1
  fi

  out="$(FORGECERT_SELFTEST_EXTRA=norm2rel_q16_16_dag.lean bash "${BASH_SOURCE[0]}" 2>&1)"; rc=$?
  if [ "$rc" -ne 0 ] && printf '%s' "$out" | grep -q "STALE ALLOWLIST"; then
    echo "   canary 3 (a stale allowlist entry FAILS, not notes)        FIRES"
  else
    echo "   canary 3 (a stale allowlist entry FAILS, not notes)        SILENT — ROT UNGUARDED"
    fail=1
  fi

  if [ "$fail" -ne 0 ]; then
    echo "[check-forge-cert] SELFTEST FAIL — a specimen did not discriminate." >&2
    exit 1
  fi
  echo "[check-forge-cert] SELFTEST PASS — all three specimens discriminate."
  exit 0
fi

if [ ! -d "$DIR" ]; then
  echo "[check-forge-cert] SKIP: no $DIR/ in this tree — nothing emitted to check." >&2
  exit 0
fi
if ! command -v lake >/dev/null 2>&1; then
  echo "[check-forge-cert] FAIL: no \`lake\` on PATH — a gate that cannot run is not a gate." >&2
  exit 2
fi

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
: > "$TMP/failures"
total=0

for f in "$DIR"/*.lean; do
  [ -e "$f" ] || continue
  total=$((total + 1))
  if ! timeout 900 lake env lean "$f" > "$TMP/out" 2>&1; then
    basename "$f" >> "$TMP/failures"
  fi
done

new_broken=0
while IFS= read -r b; do
  case " $KNOWN_BROKEN " in *" $b "*) continue ;; esac
  if [ "$new_broken" -eq 0 ]; then
    echo "[check-forge-cert] FAIL: certificate(s) that do not check:" >&2
  fi
  echo "[check-forge-cert]   · $b" >&2
  new_broken=$((new_broken + 1))
done < "$TMP/failures"

if [ "$new_broken" -gt 0 ]; then
  echo "[check-forge-cert] $new_broken proof-carrying certificate(s) carry no proof." >&2
  exit 1
fi

# ALLOWLIST ROT FAILS -- an entry that now checks, or that no longer exists, is a standing licence.
stale=""
for k in $KNOWN_BROKEN; do
  if [ ! -f "$DIR/$k" ]; then
    echo "[check-forge-cert] STALE ALLOWLIST: $k — no longer exists; remove it." >&2
    stale="$stale $k"
  elif ! grep -qxF "$k" "$TMP/failures" 2>/dev/null; then
    echo "[check-forge-cert] STALE ALLOWLIST: $k — now checks; remove it (regenerated?)." >&2
    stale="$stale $k"
  fi
done
if [ -n "$stale" ]; then
  echo "[check-forge-cert] FAIL: allowlist entr(ies) no longer needed:$stale" >&2
  exit 1
fi

nk="$(printf '%s' "$KNOWN_BROKEN" | wc -w | tr -d ' ')"
echo "[check-forge-cert] PASS: $((total - nk)) of $total Forge certificates check; \
$nk documented stale (predates a generator fix; REGENERATE, do not edit)."
exit 0
