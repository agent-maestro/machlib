#!/usr/bin/env python3
"""THE THIRD ORACLE — reference-free physics assertions, run on the SILICON trace.

WHY THIS IS CATEGORICALLY DIFFERENT FROM THE TWO CHECKS THIS PROJECT ALREADY HAD.

The two-layer rule gave an EXACT check below the AST (bit-exact vs a golden) and an INDEPENDENT
check above it (hand-written composition, float reference, analytic spot values). But "independent"
has always meant ANOTHER IMPLEMENTATION -- and implementations can share a defect's ancestry. That
is precisely what happened on 2026-07-27: the golden and the RTL agreed bit-for-bit on a wrong
number, because they share arithmetic by construction. `eml_reciprocal` sign-inverted at 3 LSB and
survived THREE bench rounds of ACCEPTANCE: PASS.

Physics assertions have NO IMPLEMENTATION ON EITHER SIDE of the comparison. Monotone error on a
constant measurement, trace(P) decreasing, P positive-semidefinite, P symmetric -- these check the
output against the MATHEMATICS. No golden, no reference implementation, nothing to share ancestry
with.

    A PHYSICS GATE WOULD HAVE FAILED THE DEFECTIVE KERNEL THREE ROUNDS AGO,
    WITH NO RECONSTRUCTION AND NO FORWARD-ERROR BOUND NEEDED.

RUN IT ON THE SILICON TRACE, NOT THE GOLDEN. This is not a detail. Checking these assertions
against the golden re-verifies the defect -- the golden is what was wrong. The whole point is that
the trace off the wire is the only artifact with no implementation of ours between it and the
physics.

NOT a practice run "before celebrating bit-exactness". It is an ACCEPTANCE gate: the analyzers call
`gate()` and a violation fails the anchor, the same as a value mismatch.

Per filter class, because the assertions differ:
  converging_2d      -- 2x2 covariance filter on a CONSTANT measurement (rb_ekf, ekf_filter,
                        ekf_emitted, kalman2d): error monotone, trace(P) monotone, P PSD, P symmetric.
  converging_1d      -- scalar Kalman on a constant measurement: |x - truth| monotone, p decreasing,
                        p >= 0.
  psd_only           -- any covariance filter whose measurement is NOT constant: the monotonicity
                        claims do not hold, but PSD and symmetry always do.

The monotonicity assertions REQUIRE a constant measurement. With a varying z a filter is entitled
to get worse on any given step, so asserting otherwise would be a false alarm -- which is why the
class is an explicit argument and not a guess.
"""
from __future__ import annotations

import math
from typing import Sequence

FRAC = 16


def q2d(word: int | str) -> float:
    v = int(word, 16) if isinstance(word, str) else int(word)
    if v >= (1 << 31):
        v -= 1 << 32
    return v / (1 << FRAC)


def steps_from_trace(path: str) -> list[dict]:
    """Per-step records off the wire, keyed by the SEMANTIC key `m` -- never by line number.

    The telemetry is a rolling stream: captures start at arbitrary phases of the epoch, so a
    positional read invents discrepancies. Keying on `m` is the only meaningful ordering.
    """
    import json

    by_step: dict[int, dict] = {}
    for line in open(path):
        try:
            f = json.loads(line)
        except Exception:  # noqa: BLE001
            continue
        m = f.get("m")
        if m is None:
            continue
        by_step[int(m, 16) if isinstance(m, str) else int(m)] = f
    return [by_step[k] for k in sorted(by_step)]


# --- symmetry tolerance, CALIBRATED from the shipped traces rather than guessed -------------
# The RTL computes both off-diagonals of the Joseph form through DIFFERENT truncation paths, so a
# few LSB of disagreement is a truncation artifact, not a fault. Measured worst |p1-p2| across
# every 2x2 anchor's silicon trace:
#     rb_ekf_arty              4.0 LSB   (0.180% of the max diagonal)
#     rb_ekf round-3 defective 4.0 LSB   (0.172%)
#     ekf_filter_arty          1.0 LSB   (2.778%)
#     ekf_emitted_arty         1.0 LSB   (2.778%)
# An absolute-only bound is insensitive on small-P anchors; a relative-only bound is insensitive on
# large-P ones. So: max(ABS, REL * max_diag). At ABS=8 LSB / REL=1% every anchor clears by 3.7x-8x
# and a real asymmetry -- which would be a large fraction of the diagonal -- still fires.
SYM_ABS_LSB = 8
SYM_REL = 0.01

# --- monotonicity tolerance, and why it is NOT the "quantisation wobble" excuse again ---------
# A converged filter sits at the quantisation floor: the update reduces P by less than Q adds
# back, so trace(P) can oscillate by ONE LSB -- the smallest representable change. Measured worst
# rise per trace:
#     ekf_filter_arty          1.0 LSB      <- converged, at the floor
#     ekf_emitted_arty         1.0 LSB      <- converged, at the floor
#     rb_ekf FIXED             0.0 LSB
#     rb_ekf round-3 DEFECTIVE 836.0 LSB    <- the sign-inverted gain
# THREE ORDERS OF MAGNITUDE apart. At MONO_TOL_LSB = 4

# ── THE CONTRACT IS A VERSIONED SEMANTIC OBJECT ────────────────────────────────────────────────
# The gate judges frames under a schema-version regime, so it lives under the same regime itself --
# `bump the version when a field's SEMANTICS change, not only when a field is ADDED`. Changing what
# MONOTONICITY MEANS is exactly a semantic change, so the validity-bit admission is v2, not a patch
# to v1.
#
# v1  trace(P) non-increasing on EVERY step. Correct until the ToF sentinel ruling made `valid = 0`
#     a DEFINED input -- a predict-only step, on which trace(P) rises BY DESIGN. Under v1 a rung-2
#     dropout would have fired FALSELY, and the gate would have been right by its contract and wrong
#     by the semantics.
# v2  the assertion SPLITS. Monotone decrease over valid steps; bounded predict-growth (<= the
#     Q-driven increment plus tolerance) over invalid ones. A dropout licences exactly the model's
#     growth and no more, or `valid=0` becomes a way to hide a fault.
#
# Frozen in CONTRACT.lock beside this file and asserted by the specimens, so the contract cannot
# drift silently the way `arty-tof-raw.v1` did.
CONTRACT_VERSION = "physics-gate.v2"
CONTRACT_ASSERTIONS = (
    "P positive-semidefinite",
    "P symmetric",
    "trace(P) non-increasing",              # v2: over VALID steps only
    "bounded predict-growth on valid=0",    # v2: added by the sentinel ruling
    "error monotone on constant z",
    "p >= 0",
    "p non-increasing",
    "|x - truth| monotone",
)

# --- THE GATE'S CONSTANTS MUST NOT DRIFT OUT FROM UNDER IT ------------------------------------
# Both tolerances above were measured against TODAY'S THREE ANCHORS: 8-step, ROM-driven, constant
# z. That is not the duty cycle the ToF rig will have. A hand-panned rig sitting at the
# quantisation floor through track lock may oscillate differently from an 8-step ROM replay, and
# inheriting a threshold across that change is exactly the drift this gate exists to catch --
# applied to itself.
#
#   OBLIGATION: when the first ToF live traces exist, RE-RUN the calibration sweep against them
#   (worst |p1-p2| and worst trace(P) rise, per trace) and RE-DERIVE these two constants from that
#   evidence. Do not inherit them. If the live floor oscillation exceeds 4 LSB, the threshold moves
#   and the "uncovered band" note below moves with it.
#
# The specimen test (test_physics_gate_specimen.py) pins the other end: whatever the constants
# become, they must still reject the round-3 defect (836 LSB). That bounds any re-calibration from
# above -- it cannot loosen past the historical fault. the defect still fires by 209x while the
# floor oscillation stops raising false alarms.
#
# This is exactly the framing that let the defect survive three rounds ("periodic quantisation
# wobble"), so it is stated as a NUMBER with its evidence rather than as a story: 1 LSB is the
# floor and is provably the smallest change the format can express; 836 LSB is not a wobble. If a
# future rise lands between 4 and ~100 LSB, THAT IS NOT COVERED BY THIS CALIBRATION and must be
# investigated, not waved through.
MONO_TOL_LSB = 4

# ── THE CONTRACT IS A VERSIONED SEMANTIC OBJECT ────────────────────────────────────────────────
# The gate judges frames under a schema-version regime, so it lives under the same regime itself --
# `bump the version when a field's SEMANTICS change, not only when a field is ADDED`. Changing what
# MONOTONICITY MEANS is exactly a semantic change, so the validity-bit admission is v2, not a patch
# to v1.
#
# v1  trace(P) non-increasing on EVERY step. Correct until the ToF sentinel ruling made `valid = 0`
#     a DEFINED input -- a predict-only step, on which trace(P) rises BY DESIGN. Under v1 a rung-2
#     dropout would have fired FALSELY, and the gate would have been right by its contract and wrong
#     by the semantics.
# v2  the assertion SPLITS. Monotone decrease over valid steps; bounded predict-growth (<= the
#     Q-driven increment plus tolerance) over invalid ones. A dropout licences exactly the model's
#     growth and no more, or `valid=0` becomes a way to hide a fault.
#
# Frozen in CONTRACT.lock beside this file and asserted by the specimens, so the contract cannot
# drift silently the way `arty-tof-raw.v1` did.
CONTRACT_VERSION = "physics-gate.v2"
CONTRACT_ASSERTIONS = (
    "P positive-semidefinite",
    "P symmetric",
    "trace(P) non-increasing",              # v2: over VALID steps only
    "bounded predict-growth on valid=0",    # v2: added by the sentinel ruling
    "error monotone on constant z",
    "p >= 0",
    "p non-increasing",
    "|x - truth| monotone",
)

# --- THE GATE'S CONSTANTS MUST NOT DRIFT OUT FROM UNDER IT ------------------------------------
# Both tolerances above were measured against TODAY'S THREE ANCHORS: 8-step, ROM-driven, constant
# z. That is not the duty cycle the ToF rig will have. A hand-panned rig sitting at the
# quantisation floor through track lock may oscillate differently from an 8-step ROM replay, and
# inheriting a threshold across that change is exactly the drift this gate exists to catch --
# applied to itself.
#
#   OBLIGATION: when the first ToF live traces exist, RE-RUN the calibration sweep against them
#   (worst |p1-p2| and worst trace(P) rise, per trace) and RE-DERIVE these two constants from that
#   evidence. Do not inherit them. If the live floor oscillation exceeds 4 LSB, the threshold moves
#   and the "uncovered band" note below moves with it.
#
# The specimen test (test_physics_gate_specimen.py) pins the other end: whatever the constants
# become, they must still reject the round-3 defect (836 LSB). That bounds any re-calibration from
# above -- it cannot loosen past the historical fault.


# --- THE MONOTONICITY ASSERTIONS ARE CONDITIONAL ON A MEASUREMENT HAVING ARRIVED ---------------
# Added 2026-07-28, BEFORE rung 2's first capture rather than after its first false alarm.
#
# The ToF sentinel ruling makes a dropout a DEFINED input: a frame with `valid = 0` is a
# PREDICT-ONLY step -- x <- Fx, P <- F P F' + Q, no update. That is textbook missing-data Kalman and
# it is the right semantics. But it makes `trace(P)` RISE BY DESIGN on such a step, and this gate
# asserts trace(P) non-increasing.
#
#   A dropout in a rung-2 trace would fire this gate FALSELY -- and the gate would be RIGHT by its
#   old contract and WRONG by the new semantics.
#
# So the contract splits, and the gate needs the validity bit before it ever judges a ToF-fed trace:
#
#   valid = 1   monotone DECREASE, as before (tolerance MONO_TOL_LSB)
#   valid = 0   BOUNDED PREDICT-GROWTH: the rise must be <= the Q-driven increment plus tolerance.
#               A rise LARGER than Q can explain is still a violation -- a dropout does not licence
#               arbitrary covariance growth, only exactly the growth the model predicts.
#
# Traces with no validity field are treated as all-valid, so every existing anchor is unaffected.
MISSING_OK_DEFAULT = True


def _valid_of(frame: dict) -> bool:
    """Validity bit, if the schema carries one. Absent => all-valid (existing anchors)."""
    for k in ("valid", "v", "meas_valid"):
        if k in frame:
            x = frame[k]
            return bool(int(x, 16) if isinstance(x, str) else int(x))
    return True


def gate(trace_path: str, filter_class: str, truth: Sequence[float] | None = None,
         verbose: bool = True, q_trace_increment: float | None = None) -> tuple[bool, list[str]]:
    """Return (ok, failures). Reference-free: nothing here reads a golden or any implementation."""
    rows = steps_from_trace(trace_path)
    if not rows:
        return False, ["physics gate: no per-step records in the trace"]
    if filter_class not in ("converging_2d", "psd_only", "converging_1d"):
        return False, [f"physics gate: unknown filter class {filter_class!r}"]

    # each check owns its own failure list, so the summary cannot mislabel which one fired
    checks: dict[str, list[str]] = {}

    def fail(name: str, msg: str) -> None:
        checks.setdefault(name, []).append(msg)

    if filter_class in ("converging_2d", "psd_only"):
        for n in ("P positive-semidefinite", "P symmetric"):
            checks.setdefault(n, [])
        if filter_class == "converging_2d":
            checks.setdefault("trace(P) non-increasing", [])
            checks.setdefault("bounded predict-growth on valid=0", [])
            if truth is not None:
                checks.setdefault("error monotone on constant z", [])
        prev_err = prev_tr = None
        for k, f in enumerate(rows):
            p0, p1, p2, p3 = (q2d(f["p0"]), q2d(f["p1"]), q2d(f["p2"]), q2d(f["p3"]))
            # PSD holds for ANY gain (MachLib.Real.kalman2_joseph_psd), so a violation is arithmetic
            if p0 < 0 or p3 < 0:
                fail("P positive-semidefinite",
                     f"step {k}: NEGATIVE diagonal ({p0:.6g}, {p3:.6g})")
            if p0 * p3 - p1 * p2 < -1e-9:
                fail("P positive-semidefinite",
                     f"step {k}: det P = {p0 * p3 - p1 * p2:.3e} < 0")
            tol = max(SYM_ABS_LSB / (1 << FRAC), SYM_REL * max(abs(p0), abs(p3)))
            if abs(p1 - p2) > tol:
                fail("P symmetric",
                     f"step {k}: off-diagonals differ by {abs(p1 - p2) * (1 << FRAC):.1f} LSB "
                     f"(tolerance {tol * (1 << FRAC):.1f})")
            if filter_class == "converging_2d":
                tr = p0 + p3
                is_valid = _valid_of(f)
                if prev_tr is not None and not is_valid:
                    # PREDICT-ONLY step: growth is expected, but only as much as Q explains.
                    budget = (q_trace_increment if q_trace_increment is not None else 0.0) \
                        + MONO_TOL_LSB / (1 << FRAC)
                    if tr > prev_tr + budget:
                        fail("bounded predict-growth on valid=0",
                             f"step {k}: trace(P) rose {(tr - prev_tr) * (1 << FRAC):.0f} LSB on a "
                             f"PREDICT-ONLY step, more than Q can explain "
                             f"({budget * (1 << FRAC):.0f} LSB budget). A dropout licences exactly "
                             f"the model's growth, not arbitrary growth.")
                    prev_tr = tr
                    prev_err = None      # error monotonicity is undefined across a dropout
                    continue
                if prev_tr is not None and tr > prev_tr + MONO_TOL_LSB / (1 << FRAC):
                    fail("trace(P) non-increasing",
                         f"step {k}: trace(P) ROSE {prev_tr:.6g} -> {tr:.6g} "
                         f"({(tr - prev_tr) * (1 << FRAC):.0f} LSB, tolerance {MONO_TOL_LSB}) on a "
                         f"constant measurement -- a filter cannot become less certain")
                prev_tr = tr
                if truth is not None:
                    err = math.hypot(q2d(f["x0"]) - truth[0], q2d(f["x1"]) - truth[1])
                    if prev_err is not None and err > prev_err + MONO_TOL_LSB / (1 << FRAC):
                        fail("error monotone on constant z",
                             f"step {k}: error ROSE {prev_err:.5f} -> {err:.5f} on a CONSTANT "
                             f"measurement -- physics violation")
                    prev_err = err
    else:  # converging_1d
        for n in ("p >= 0", "p non-increasing"):
            checks.setdefault(n, [])
        if truth is not None:
            checks.setdefault("|x - truth| monotone", [])
        prev_err = prev_p = None
        for k, f in enumerate(rows):
            p = q2d(f.get("p0", f.get("p")))
            if p < 0:
                fail("p >= 0", f"step {k}: variance p = {p:.6g} < 0")
            if prev_p is not None and p > prev_p + 1e-12:
                fail("p non-increasing", f"step {k}: p ROSE {prev_p:.6g} -> {p:.6g}")
            prev_p = p
            if truth is not None:
                err = abs(q2d(f.get("x0", f.get("x"))) - truth[0])
                if prev_err is not None and err > prev_err + 1e-12:
                    fail("|x - truth| monotone",
                         f"step {k}: |x - truth| ROSE {prev_err:.5f} -> {err:.5f}")
                prev_err = err

    fails = [m for msgs in checks.values() for m in msgs]
    if verbose:
        print("\n--- PHYSICS GATE (reference-free, on the SILICON trace) ---")
        print(f"    class={filter_class}  steps={len(rows)}")
        for name, msgs in checks.items():
            print(f"    {name:<32} {'FAIL' if msgs else 'ok'}")
        print(f"    PHYSICS GATE: {'PASS' if not fails else 'FAIL'}")
        for m in fails:
            print(f"      - {m}")
    return (not fails), fails


if __name__ == "__main__":
    import sys

    ok, _ = gate(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "converging_2d",
                 truth=(2.0, 5.0) if len(sys.argv) > 3 else None)
    raise SystemExit(0 if ok else 1)
