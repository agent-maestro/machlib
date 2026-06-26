#!/usr/bin/env bash
# Close-rate harness for the Forge @verify(lean) corpus (MachLib/Discovered/).
#
# Each Discovered file is self-contained (defines its own consts), so they cannot
# be co-imported — compile each INDEPENDENTLY via `lake env lean`. The emitter
# always writes a `first | mach_positivity | … | sorry` cascade, so the textual
# `sorry` is just a fallback; the TRUE close-rate is which cascades actually fall
# through, surfaced as a `declaration uses 'sorry'` warning per obligation.
#
# Output: per-file status + a summary (closed / sorry / error over all theorems).
set -uo pipefail
cd "$(dirname "$0")/.."   # foundations/
DISC=MachLib/Discovered
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT

ls "$DISC"/*.lean | xargs -P "$(nproc)" -I{} bash -c '
  f="{}"; out=$(lake env lean "$f" 2>&1)
  base=$(basename "$f")
  thms=$(grep -cE "^theorem " "$f")
  if echo "$out" | grep -qE ": error:"; then
    echo "ERROR 0 $thms $base"
  else
    s=$(echo "$out" | grep -cE "uses .sorry.")
    echo "OK $s $thms $base"
  fi
' > "$TMP/results.txt"

awk '
  { status=$1; sorry=$2; thms=$3; file=$4
    files++; total_thms+=thms
    if (status=="ERROR") { err_files++; err_thms+=thms }
    else { ok_files++; sorry_thms+=sorry; closed_thms += (thms - sorry) }
  }
  END {
    printf "\n=== Forge @verify(lean) close-rate (MachLib/Discovered) ===\n"
    printf "files:     %d  (%d compiled, %d build-error)\n", files, ok_files, err_files
    printf "theorems:  %d  (%d in compiled files, %d in error files)\n", total_thms, total_thms-err_thms, err_thms
    printf "CLOSED:    %d\n", closed_thms
    printf "sorry:     %d\n", sorry_thms
    if (total_thms-err_thms > 0)
      printf "close-rate (of compiled): %.1f%%  (%d/%d)\n", 100*closed_thms/(total_thms-err_thms), closed_thms, total_thms-err_thms
  }
' "$TMP/results.txt"
echo "--- build-error (stale) files ---"
grep '^ERROR' "$TMP/results.txt" | awk '{print "  "$4}' | head
