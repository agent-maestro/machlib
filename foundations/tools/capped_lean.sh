#!/usr/bin/env bash
# capped_lean.sh — run a Lean/lake invocation inside a memory-capped transient scope.
#
# WHY THIS EXISTS. On 2026-09-08 this machine went unresponsive and was power-cycled by hand
# (`systemd-logind: Power key pressed short`, 15:02). It was not a kernel panic and nothing was
# OOM-killed at the time; the box simply ran out of headroom and stopped responding. The journal
# is unambiguous about the cause: in THIRTEEN DAYS of uptime there were exactly two days with any
# memory pressure at all — Sep 05 (598 events, ending with VSCode OOM-killed) and Sep 08 (608
# events, starting 14:35:04 and ending with the power press 27 minutes later). Both are days this
# corpus was being worked on. No other day produced a single event.
#
# THE MECHANISM, MEASURED. A single `lake env lean` on ONE emitted Forge artifact
# (`examples/multimodal_reflex.eml`, 206 lines) peaks at **3.4 GB RSS**. Adding ONE `mach_linarith`
# arm to ONE theorem's closer alternation takes it to **7.8 GB** — and it still only reaches the
# heartbeat timeout rather than a conclusion, because a wide `first | … |` alternation pays for
# every arm that fails. The obvious next move when a proof times out is to RAISE `maxHeartbeats`,
# which buys the grinding tactic more time to allocate. That is the loaded gun: the budget that
# bounds the search is measured in heartbeats, and **nothing bounds the memory**.
#
# This is the same shape as the tactic gotchas already in CLAUDE.md — `mach_mpoly` GRINDS rather
# than fails on a literal `-0`, and a normalisation blow-up presents as a long run, not an error.
# What is new is that the blow-up is not confined to the build: it takes the desktop with it.
#
# WHAT THIS DOES. Runs the command in a systemd transient scope with `MemoryMax` and no swap, so a
# runaway elaboration is killed by ITS OWN cgroup, leaving the rest of the machine alone. The cap
# is per-invocation, so parallel harnesses (`check_discovered_compiles.sh 4`) multiply it — size it
# accordingly.
#
# USAGE
#     tools/capped_lean.sh lake env lean Foo.lean          # default cap
#     tools/capped_lean.sh --cap 24G lake build            # explicit
#     MACHLIB_LEAN_CAP=32G tools/capped_lean.sh lake build # via environment
#     tools/capped_lean.sh --selftest                      # both verdicts, ~1 min
#
# EXIT STATUS is the command's own, except that a cgroup OOM kill surfaces as 137/143 and is
# reported explicitly — a killed run must never be mistaken for a failed proof, which is the
# "instrument that can only return one value" trap this corpus already pays for in five costumes.
#
# HONEST DEGRADATION. Without `systemd-run`, or without a delegated cgroup, this cannot cap
# anything. It then says so on stderr and runs the command UNCAPPED rather than refusing — but it
# says so every time, because a guard that silently stops guarding is worse than no guard.
set -uo pipefail

CAP="${MACHLIB_LEAN_CAP:-16G}"

die() { printf '%s\n' "$*" >&2; exit 2; }

have_scope() {
  command -v systemd-run >/dev/null 2>&1 || return 1
  systemd-run --user --scope -p MemoryMax=64M --quiet -- true >/dev/null 2>&1
}

run_capped() {
  local cap="$1"; shift
  if have_scope; then
    systemd-run --user --scope -p MemoryMax="$cap" -p MemorySwapMax=0 --quiet -- "$@"
    local rc=$?
    if [ "$rc" -eq 137 ] || [ "$rc" -eq 143 ]; then
      printf 'capped_lean: KILLED AT THE %s CAP — this is a resource verdict, NOT a proof verdict.\n' "$cap" >&2
      printf 'capped_lean: the elaboration exceeded its memory budget; do not read it as "the theorem is false".\n' >&2
    fi
    return $rc
  fi
  printf 'capped_lean: UNCAPPED — no usable `systemd-run --user --scope` here.\n' >&2
  printf 'capped_lean: a runaway elaboration can still take the machine down. Watch it.\n' >&2
  "$@"
}

selftest() {
  echo "=== CAPPED-LEAN SELFTEST ==="
  if ! have_scope; then
    echo "  UNAVAILABLE — no usable transient scope; the guard cannot be demonstrated here."
    echo "CAPPED-LEAN SELFTEST UNAVAILABLE"
    return 2
  fi
  # canary 1 — a hog above the cap must be KILLED
  run_capped 64M python3 -c 'b=bytearray(512*1024*1024); print(len(b))' >/dev/null 2>&1
  local rc1=$?
  local k1="SILENT — BROKEN"; { [ $rc1 -eq 137 ] || [ $rc1 -eq 143 ] || [ $rc1 -eq 1 ]; } && k1="KILLS"
  echo "  canary 1 (512M hog under a 64M cap must be KILLED):  rc=$rc1 $k1"
  # canary 2 — a control below the cap must SURVIVE
  run_capped 512M python3 -c 'b=bytearray(16*1024*1024); print(len(b))' >/dev/null 2>&1
  local rc2=$?
  local k2="FIRES — BROKEN"; [ $rc2 -eq 0 ] && k2="SURVIVES"
  echo "  canary 2 (16M control under a 512M cap must PASS):   rc=$rc2 $k2"
  # canary 3 — the exit status of an ordinary failure must pass through unchanged
  run_capped 512M sh -c 'exit 3' >/dev/null 2>&1
  local rc3=$?
  local k3="MANGLED — BROKEN"; [ $rc3 -eq 3 ] && k3="PASSES THROUGH"
  echo "  canary 3 (a plain exit 3 must reach the caller):     rc=$rc3 $k3"
  if [ "$k1" = "KILLS" ] && [ "$k2" = "SURVIVES" ] && [ "$k3" = "PASSES THROUGH" ]; then
    echo "CAPPED-LEAN SELFTEST PASS — 1 hog killed, 1 control survived, 1 status preserved"
    return 0
  fi
  echo "CAPPED-LEAN SELFTEST FAIL"
  return 1
}

[ $# -eq 0 ] && die "usage: capped_lean.sh [--cap SIZE] <command...>   |   --selftest"
case "${1:-}" in
  --selftest) selftest; exit $? ;;
  --cap) [ $# -ge 2 ] || die "--cap needs a size"; CAP="$2"; shift 2 ;;
esac
[ $# -eq 0 ] && die "capped_lean.sh: no command given"
run_capped "$CAP" "$@"
