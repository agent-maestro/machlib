#!/usr/bin/env python3
"""Check the recursive streaming 2-D EKF silicon anchor against the golden trajectory.

Reads arty-ekf-filter.v0 frames (i, m, x0, x1, p0..p3). m is the trajectory STEP index (0..7 --
which measurement's result is in the state); (x0,x1)/(p0..p3) are the EKF estimate and covariance
at that step. Maps m to the golden trajectory (rb_filter_golden.trajectory()) and checks the
state bit-for-bit -- so the compiler-Jacobian EKF on the die reproduced the software filter exactly.

The z ROM and the prior (x0, P0, Q, R) are not on the wire, so verify_rom() statically parses them
from the anchor top and confirms they equal what the golden assumes -- grounding the whole
trajectory (the anchor's telemetry is not trusted to key itself).

Acceptance: every step's (x, P) == golden bit-for-bit, all 8 covered, verify_rom True.
Run:  python analyze_rb_ekf_anchor.py <rb_ekf_trace.jsonl>
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rb_filter_golden import trajectory, z_rom, X0, P0, Q, R, d2q, q2d, MASK32, TRUTH  # noqa: E402

TOP = os.path.join(HERE, "..", "rtl", "rb_ekf_anchor_top.v")


def verify_rom():
    """Parse the anchor top's z ROM + prior (X0,P0,Q,R) localparams; compare to the golden."""
    try:
        txt = open(TOP, encoding="utf-8", errors="replace").read()
    except OSError:
        return {"checked": False, "reason": "anchor top not readable"}
    # NOTE (bench, 2026-07-27): index the explicit `4'dN:` cases and use `default:` only to FILL
    # indices they do not cover. The previous version appended every matching line in order, which
    # silently assumed the top emits exactly N ROM lines. That holds for ekf_emitted_arty
    # (4'd0..4'd6 + default = 8) but NOT here: rb_filter_golden.py prints all eight cases
    # 4'd0..4'd7 AND a default, so the parse returned 9 entries against a golden of 8 and
    # z_rom_match was False on every run regardless of the data -- which, since
    # `match = zmatch and prior_match`, made ACCEPTANCE unreachable. The z words themselves were
    # correct and identical throughout. Indexing handles both emitter styles.
    explicit, dflt = {}, None
    for line in txt.splitlines():
        m = re.search(r"(4'd([0-9])|default)\s*:\s*begin\s*z0", line)
        if not m:
            continue
        ws = [int(w, 16) for w in re.findall(r"32'h([0-9A-Fa-f]{8})", line)]
        if len(ws) != 2:
            continue
        if m.group(2) is not None:
            explicit[int(m.group(2))] = tuple(ws)
        else:
            dflt = tuple(ws)
    gz = [tuple(z) for z in z_rom()]
    rom = [explicit.get(i, dflt) for i in range(len(gz))]
    zmatch = rom == gz

    def _lp(name):
        m = re.search(name + r"\s*=\s*32'h([0-9A-Fa-f]{8})", txt)
        return int(m.group(1), 16) if m else None
    # NOTE (bench, 2026-07-27): P0/Q/R are NESTED 2x2 row-major lists ([[a,b],[c,d]]) while X0 is
    # flat, so they must be flattened before d2q -- iterating them directly hands d2q a list and
    # raises "type list doesn't define __round__". rb_filter_golden.py already flattens this way
    # where it prints the priors; this check did not. verify_rom() is only reached from a real
    # capture, which is why the pre-send UART decode sim never exercised it.
    def _flat(m):
        return [v for row in m for v in row]
    xg = [d2q(v) & MASK32 for v in X0]
    pg = [d2q(v) & MASK32 for v in _flat(P0)]
    qg = [d2q(v) & MASK32 for v in _flat(Q)]
    rg = [d2q(v) & MASK32 for v in _flat(R)]
    xr = [_lp("X0_0"), _lp("X0_1")]
    pr = [_lp("P0_0"), _lp("P0_1"), _lp("P0_2"), _lp("P0_3")]
    qr = [_lp("Q_0"), _lp("Q_1"), _lp("Q_2"), _lp("Q_3")]
    rr = [_lp("R_0"), _lp("R_1"), _lp("R_2"), _lp("R_3")]
    prior_match = (xr == xg and pr == pg and qr == qg and rr == rg)
    return {"checked": True, "match": zmatch and prior_match,
            "z_rom_match": zmatch, "prior_match": prior_match, "n_steps": len(rom)}


_PHYS_TRUTH = (2.0, 5.0)   # constant-z scenario truth, for the monotonicity assertions


def _physics_gate(path):
    """THE THIRD ORACLE -- reference-free assertions on the SILICON trace.

    Bit-exactness compares two implementations, and implementations can share a defect's
    ancestry: on 2026-07-27 the golden and the RTL agreed bit-for-bit on a sign-inverted gain for
    THREE ROUNDS. These assertions have no implementation on either side -- they check the output
    against the mathematics. Run on the trace off the wire, never on the golden (the golden is
    what was wrong).
    """
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "tools"))
    try:
        from physics_gate import gate
    except Exception as exc:  # noqa: BLE001
        print("PHYSICS GATE: UNAVAILABLE (%s) -- treated as a FAILURE, not a skip" % exc)
        return False
    ok, _ = gate(path, "converging_2d", truth=_PHYS_TRUTH)
    return ok


def main() -> None:
    path = sys.argv[1] if len(sys.argv) > 1 else "ekf_filter_trace.jsonl"
    gold = {row[0]: row[1:] for row in trajectory()}      # step -> (x0,x1,p0,p1,p2,p3)
    n = len(gold)
    rom_check = verify_rom()

    frames, bad = [], 0
    with open(path, encoding="ascii") as f:
        for line in f:
            line = line.strip()
            if not (line.startswith("{") and line.endswith("}")):
                continue
            try:
                o = json.loads(line)
                frames.append({k: int(o[k], 16) & MASK32
                               for k in ("i", "m", "x0", "x1", "p0", "p1", "p2", "p3")})
            except (ValueError, KeyError):
                bad += 1

    per_step, checked, nbad = {}, 0, 0
    for fr in frames:
        m = fr["m"]
        if m not in gold:
            continue
        got = (fr["x0"], fr["x1"], fr["p0"], fr["p1"], fr["p2"], fr["p3"])
        checked += 1
        slot = per_step.setdefault(m, {"frames": 0, "mismatches": 0, "seen": set()})
        slot["frames"] += 1
        slot["seen"].add(got)
        if got != gold[m]:
            nbad += 1
            slot["mismatches"] += 1

    missing = [k for k in range(n) if k not in per_step]
    all_exact = (nbad == 0 and not missing and rom_check.get("match", False))

    rows = []
    for k in range(n):
        g = gold[k]
        slot = per_step.get(k)
        seen0 = sorted(slot["seen"])[0] if slot else None
        err = ((q2d(g[0]) - TRUTH[0]) ** 2 + (q2d(g[1]) - TRUTH[1]) ** 2) ** 0.5
        rows.append({
            "step": k, "captured": slot is not None, "frames": slot["frames"] if slot else 0,
            "silicon": ["0x%08x" % v for v in seen0] if seen0 else [],
            "golden": ["0x%08x" % v for v in g],
            "x_real": [q2d(g[0]), q2d(g[1])], "err": err, "trace_P": q2d(g[2]) + q2d(g[5]),
            "bit_exact": (slot["mismatches"] == 0) if slot else False,
            "distinct": len(slot["seen"]) if slot else 0,
        })

    out = {
        "schema": "arty-ekf-filter.evidence/v1",
        # Provenance must name THIS anchor's DUT. Adapting the sibling's analyzer renamed files and
        # modules but left these description strings, so the first evidence JSON produced here
        # labelled the run as ekf_filter_arty/ekf2d_filter.v -- the hand-written design. The numbers
        # were right and the artifact said they came from the wrong thing, which is exactly how a
        # provenance record goes bad.
        "dut": "rb_ekf_arty/rtl/rb_track_emitted.v :: track_pipeline -- COMPILER-EMITTED from forge "
               "examples/ekf_range_bearing.eml. Range-bearing radar model h=(sqrt(x0^2+x1^2), "
               "atan(x1/x0)); Jacobian derived by autodiff through sqrt/pow/div/atan and "
               "normalised to lowest terms; wide transcendental kernels (eml_sqrt_wide, "
               "eml_atan_wide) + eml_reciprocal on the die",
        "board": "Arty A7-100T (xc7a100tcsg324-1)",
        "n_frames": len(frames), "n_unparseable": bad, "n_frames_checked": checked,
        "n_value_mismatches": nbad, "n_steps_expected": n, "n_steps_captured": len(per_step),
        "missing_steps": missing, "rom_and_prior_vs_golden": rom_check, "all_bit_exact": all_exact,
        "note": ("recursive EKF: (x,P) evolves under a NONLINEAR measurement h(x)=z^2 whose Jacobian "
                 "H the COMPILER derived (emitted track_meas, not the hand-written ekf_meas_z2 -- "
                 "that is what this anchor adds over ekf_filter_arty). Each step's state is checked "
                 "against the golden "
                 "trajectory by index m; the z stream + prior (x0,P0,Q,R) are statically verified "
                 "(verify_rom). EKF is first-order (not MMSE-optimal); what is guaranteed is the "
                 "fixed-point bound, Joseph PSD, and the symbolically-exact compiler Jacobian. DSP "
                 "count + timing + cycles/step come from the Vivado reports."),
        "per_step": rows,
    }
    out_path = os.path.join(os.path.dirname(os.path.abspath(path)), "rb_ekf_anchor_evidence.json")
    with open(out_path, "w", newline="\n") as f:
        json.dump(out, f, indent=2)

    print("=" * 96)
    print("frames=%d  checked=%d  unparseable=%d  steps %d/%d  value-mismatches=%d"
          % (len(frames), checked, bad, len(per_step), n, nbad))
    print("ROM + prior == golden: %s  %s" % (rom_check.get("match"), rom_check))
    print("ALL bit-exact: %s" % all_exact)
    print("-" * 96)
    print("%4s %6s  %-9s %-9s %8s %8s  %-37s %s" %
          ("step", "frames", "x0", "x1", "err", "trace(P)", "silicon (x0,x1,P0..P3)", "verdict"))
    for w in rows:
        if not w["captured"]:
            print("%4d %6d  NOT CAPTURED" % (w["step"], 0)); continue
        print("%4d %6d  %-9.4f %-9.4f %8.5f %8.5f  %-37s %s%s"
              % (w["step"], w["frames"], w["x_real"][0], w["x_real"][1], w["err"], w["trace_P"],
                 " ".join(w["silicon"][:2]) + " ...",
                 "OK" if w["bit_exact"] else "MISMATCH",
                 "" if w["distinct"] == 1 else "  (%d distinct!)" % w["distinct"]))
    if missing:
        print("MISSING steps: %s" % missing)
    print("=" * 96)
    phys_ok = _physics_gate(path)
    accepted = all_exact and phys_ok
    print("ACCEPTANCE:", "PASS" if accepted else "FAIL")
    if all_exact and not phys_ok:
        print("  -> bit-exact BUT the physics gate failed. That combination is the\n"
              "     signature of a defect shared by the golden and the RTL.")
    # EXIT CODE MUST CARRY THE VERDICT. Until 2026-07-27 this printed PASS/FAIL and always exited 0,
    # so the result existed only as text: any harness checking $? read a FAIL as success. That is the
    # same failure family as the ROM false negative -- a gate whose output cannot be acted on is not
    # a gate. Verdict composition is unchanged (values + coverage + ROM/prior); only its
    # machine-readability is fixed. See tools/test_anchor_gates.py, which asserts BOTH directions.
    return 0 if accepted else 1
    print("wrote", out_path)



if __name__ == "__main__":
    raise SystemExit(main())
