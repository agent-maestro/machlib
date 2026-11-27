#!/usr/bin/env python3
"""Fail when the kernel watch observes something its record does not hold: movement must be READ.

WHY (2026-11-27). `watch_kernel_support.py` was run by hand. It last ran on record on 2026-07-30, and
in the four months after, Lean4Lean ported the #14577 fix, fixed the instrument bug we reported
(digama0/lean4lean#17, reported fixed in a comment while the issue stayed open), and pinned exactly
this project's destination toolchain for a morning -- and nothing here changed. A watch that is not
run is not a watch, and a watch that is run but whose output nobody compares with anything is a log.

So `.github/workflows/kernel-watch.yml` runs the watch weekly with `--out` (the record is untouched)
and then runs this, which compares that observation with the committed `watch_state.json`:

    python3 tools/migration/check_watch_record.py OBSERVED.json [RECORD.json]
    python3 tools/migration/check_watch_record.py --selftest

    exit 0  the record is current: every field but `observed_at` equals today's observation
    exit 1  the record is STALE: something moved. Re-run the watch without --out (it rewrites the
            record), read what moved against BUMP_PLAN.md, and commit the record with a dated
            MIGRATION_LOG.md line. Red until then -- on purpose.
    exit 2  could not judge: a file is unreadable, or either side holds an UNOBSERVED field (None:
            an API the watch could not read). UNAVAILABLE IS FAILURE, never "unchanged". A hole in
            the RECORD is refused too: the watch will not write one, so one there is a defect.

The watch's own exit codes stay what they were (the expiry condition only); whether the record is
current is this file's verdict, so the two never share a meaning.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile

RECORD = os.path.join(os.path.dirname(os.path.abspath(__file__)), "watch_state.json")
IGNORED = frozenset({"observed_at"})
MISSING = "(not recorded)"


def unobserved(value, path: str = "") -> list[str]:
    """Paths of every None inside a value: a field the watch could not observe."""
    if value is None:
        return [path or "(root)"]
    if isinstance(value, dict):
        return [p for k, v in value.items() for p in unobserved(v, f"{path}.{k}" if path else k)]
    return []


def compare(observed: dict, record: dict) -> tuple[int, list[str]]:
    """(rc, lines): 0 current, 1 stale (each moved field), 2 an unobserved field on either side."""
    holes = [p for k, v in observed.items() if k not in IGNORED for p in unobserved(v, k)]
    if holes:
        return 2, [f"UNOBSERVED {p}: the watch could not read it, so nothing can be said about it"
                   for p in holes]
    record_holes = [p for k, v in record.items() if k not in IGNORED for p in unobserved(v, k)]
    if record_holes:
        return 2, [f"RECORD HOLDS A HOLE {p}: re-record with every field observed" for p in record_holes]
    moved = [f"{k}: {record.get(k, MISSING)} -> {observed.get(k, MISSING)}"
             for k in sorted((observed.keys() | record.keys()) - IGNORED)
             if observed.get(k, MISSING) != record.get(k, MISSING)]
    return (1 if moved else 0), moved


def _load(path: str) -> dict:
    with open(path) as f:
        data = json.load(f)
    if not isinstance(data, dict):
        raise ValueError(f"{path} holds a {type(data).__name__}, not an object")
    return data


def judge(observed_path: str, record_path: str) -> int:
    try:
        observed, record = _load(observed_path), _load(record_path)
    except (OSError, ValueError) as e:
        print(f"WATCH-RECORD UNEVALUABLE: {type(e).__name__}: {e}")
        return 2
    rc, lines = compare(observed, record)
    for line in lines:
        print(f"  {line}")
    if rc == 0:
        print(f"WATCH-RECORD CURRENT: the record ({record.get('observed_at', '?')[:10]}) holds everything "
              f"observed {observed.get('observed_at', '?')[:10]}.")
    elif rc == 1:
        print(f"WATCH-RECORD STALE: {len(lines)} field(s) moved since the record "
              f"({record.get('observed_at', '?')[:10]}).")
        print("  From foundations/: run `python3 tools/migration/watch_kernel_support.py` (it rewrites")
        print("  watch_state.json), read what moved against BUMP_PLAN.md, and commit the record with a")
        print("  dated MIGRATION_LOG.md line. This stays red until then.")
    else:
        print("WATCH-RECORD UNEVALUABLE: the observation is incomplete. UNAVAILABLE IS FAILURE: do not")
        print("  read this as 'unchanged'. Re-run when the APIs answer.")
    return rc


def selftest() -> int:
    """Canaries for every verdict, through compare() AND through the CLI path (files on disk)."""
    base = {"observed_at": "2026-11-27T00:00:00+0000", "checker_max": "v4.28.0", "l4l_pin": "v4.36.0",
            "l4l_at_destination": {"set_by": "779c51f", "carries_issue17_fix": True},
            "l4l_issue": {"state": "open", "comments": 2}}
    cases: list[tuple[str, dict, int]] = [
        ("identical but for the timestamp", dict(base, observed_at="2027-01-01T00:00:00+0000"), 0),
        ("one top-level field moved", dict(base, checker_max="v4.33.0"), 1),
        ("a nested field moved (a new comment)", dict(base, l4l_issue={"state": "open", "comments": 3}), 1),
        ("a field the record lacks", dict(base, new_field=1), 1),
        ("a field the observation lacks", {k: v for k, v in base.items() if k != "l4l_pin"}, 1),
        ("a top-level None (unobserved)", dict(base, l4l_issue=None), 2),
        ("a nested None (unobserved)", dict(base, l4l_at_destination={"set_by": "779c51f",
                                                                      "carries_issue17_fix": None}), 2),
        ("observed none at the pin ({}) vs a record that had one", dict(base, l4l_at_destination={}), 1),
    ]
    holed_record = dict(base, l4l_issue=None)
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        rec = os.path.join(tmp, "record.json")
        with open(rec, "w") as f:
            json.dump(base, f)
        for name, observed, want in cases:
            got, _ = compare(observed, base)
            obs = os.path.join(tmp, "observed.json")
            with open(obs, "w") as f:
                json.dump(observed, f)
            with open(os.devnull, "w") as devnull:
                saved, sys.stdout = sys.stdout, devnull
                try:
                    cli = judge(obs, rec)
                finally:
                    sys.stdout = saved
            ok = got == want and cli == want
            bad += not ok
            print(f"  {'ok ' if ok else 'BAD'} {name}: compare {got}, cli {cli}, want {want}")
        with open(os.devnull, "w") as devnull:
            saved, sys.stdout = sys.stdout, devnull
            try:
                missing = judge(os.path.join(tmp, "absent.json"), rec)
            finally:
                sys.stdout = saved
        ok = missing == 2
        bad += not ok
        print(f"  {'ok ' if ok else 'BAD'} an unreadable observation file: cli {missing}, want 2")
        got, _ = compare(base, holed_record)
        ok = got == 2
        bad += not ok
        print(f"  {'ok ' if ok else 'BAD'} a record holding a hole (None): compare {got}, want 2")
    total = len(cases) + 2
    print(f"WATCH-RECORD SELFTEST {'PASS' if not bad else 'FAIL'} ({total - bad}/{total})")
    return 0 if not bad else 1


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("observed", nargs="?", help="the watch's --out file")
    ap.add_argument("record", nargs="?", default=RECORD, help="default: watch_state.json beside this file")
    ap.add_argument("--selftest", action="store_true")
    args = ap.parse_args(argv)
    if args.selftest:
        return selftest()
    if not args.observed:
        ap.error("OBSERVED is required unless --selftest")
    return judge(args.observed, args.record)


if __name__ == "__main__":
    raise SystemExit(main())
