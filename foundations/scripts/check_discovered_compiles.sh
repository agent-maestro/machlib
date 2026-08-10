#!/usr/bin/env bash
# scripts/check_discovered_compiles.sh — every MachLib/Discovered/ file still compiles.
#
# Why this exists:
#
# MachLib/Discovered/ is the Forge `@verify(lean)` corpus: 294 self-contained
# files, ~749 theorems. Each defines its own constants, so they CANNOT be
# imported together and are deliberately outside the aggregator.
#
# The consequence, found during the 2026-08-10 gate-scope sweep, is that they
# were outside EVERY automated check:
#
#   * `lake build`      builds the aggregator cone; Discovered/ is not in it.
#   * `sorry_audit`     walks the ENVIRONMENT after `import MachLib`; a module
#                       nothing imports contributes no declarations to it.
#   * `check_aggregator` excludes the tree by prefix (correctly — they cannot
#                       be imported together).
#   * `closerate.sh`    does compile them, but is a MEASUREMENT harness (it
#                       reports a close-rate, 77.1% at the last sweep) and is
#                       NOT run by CI.
#
# So 294 files could rot silently. This is the minimum honest guard: not "are
# the obligations discharged" (that is closerate's job, and the answer is
# deliberately not 100%), just "does every file still compile".
#
# Cost: ~46 s at -P6 (4 min of CPU). 
#
# ⚠ I predicted this gate would be green on introduction, from a 49-file
#   sample that compiled 49/49. THE FULL RUN FOUND 4 FAILURES — the sample
#   (every 6th file) missed all of them. Extrapolating a pass rate from a
#   sample is exactly the estimate that keeps being wrong in this repo; the
#   whole point of a gate is that it runs the whole population.
#
# The 4 are Forge-GENERATED files, so hand-patching them would diverge from
# the generator. They are allow-listed with their exact errors below, which
# doubles as the bug list for the next Forge run. New breakage fails loudly.
#
# Usage (from foundations/):   bash scripts/check_discovered_compiles.sh [jobs]
# Exit codes:  0 = every file compiles   1 = at least one does not

set -uo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.." || exit 1

JOBS="${1:-4}"
DISC="MachLib/Discovered"

# Known-broken at the 2026-08-10 audit, with the actual first error. These are
# emitted by Forge; fix the GENERATOR, then delete the entry here.
#   mul_mat4.lean:37    `mul_mat4_cell_components` has already been declared
#                       (the same theorem emitted twice)
#   vec3.lean:140       tactic `simp` failed with a nested error
#   shadow_pcf.lean:78  (deterministic) timeout at `isDefEq`, 200000 heartbeats
#   autopilot.lean:45   (deterministic) timeout at `isDefEq`, 200000 heartbeats
KNOWN_BROKEN="MachLib/Discovered/mul_mat4.lean \
MachLib/Discovered/vec3.lean \
MachLib/Discovered/shadow_pcf.lean \
MachLib/Discovered/autopilot.lean"

if [ ! -d "$DISC" ]; then
  echo "[check-discovered] FAIL: $DISC not found — wrong working directory?" >&2
  exit 1
fi

LEAN="$(command -v lean || true)"
if [ -z "$LEAN" ]; then
  echo "[check-discovered] FAIL: no \`lean\` on PATH — a gate that cannot run is not" >&2
  echo "                   a gate that passed." >&2
  exit 1
fi

# Lake nests the olean tree under lib/lean/ since the v4.32.2 bump; older
# layouts put it directly in lib/. Accept either, and fail loudly if neither
# exists rather than compiling against nothing.
LIB="./.lake/build/lib/lean"
[ -d "$LIB" ] || LIB="./.lake/build/lib"
if [ ! -d "$LIB" ]; then
  echo "[check-discovered] FAIL: no olean tree at ./.lake/build/lib{,/lean} —" >&2
  echo "                   run \`lake build\` first." >&2
  exit 1
fi

TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
export LEAN LIB TMP

find "$DISC" -name '*.lean' -print0 \
  | xargs -0 -n1 -P "$JOBS" bash -c '
      f="$0"
      if ! env LEAN_PATH="$LIB" LD_LIBRARY_PATH= timeout 300 "$LEAN" "$f" -R . \
             >"$TMP/$(echo "$f" | tr / _).log" 2>&1; then
        echo "$f" >> "$TMP/failures"
      fi
    '

total="$(find "$DISC" -name '*.lean' | wc -l | tr -d ' ')"

new_broken=0
if [ -s "$TMP/failures" ]; then
  while IFS= read -r f; do
    case " $KNOWN_BROKEN " in *" $f "*) continue ;; esac
    if [ "$new_broken" -eq 0 ]; then
      echo "[check-discovered] FAIL: newly-broken Discovered file(s):" >&2
    fi
    echo "                     $f" >&2
    grep -m2 "error" "$TMP/$(echo "$f" | tr / _).log" | sed 's/^/                       /' >&2
    new_broken=$((new_broken + 1))
  done < "$TMP/failures"
fi

if [ "$new_broken" -ne 0 ]; then
  echo "[check-discovered] FAIL: $new_broken file(s) newly do not compile." >&2
  exit 1
fi

# Shrink the allowlist when the generator is fixed.
for k in $KNOWN_BROKEN; do
  if ! grep -qxF "$k" "$TMP/failures" 2>/dev/null; then
    echo "[check-discovered] NOTE: $k now compiles — remove it from KNOWN_BROKEN." >&2
  fi
done

nk="$(printf '%s' "$KNOWN_BROKEN" | wc -w | tr -d ' ')"
echo "[check-discovered] PASS: $((total - nk)) of $total files under $DISC compile; \
$nk documented broken (Forge-generated; see KNOWN_BROKEN)."
exit 0
