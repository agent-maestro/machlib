#!/usr/bin/env python3
"""Fail when a scheduled workflow has not SUCCEEDED recently: a check that stops running must go red.

WHY. MachLib's public reproduction walk (reproduction-walk.yml, weekly) failed four weeks running from
2026-09-28 and nothing else turned red: its README still described it as the check that catches a bad
release. walk-freshness.yml runs this daily and on every push to master, so a walk that stops
succeeding turns those red within MAX_AGE_DAYS instead of going quiet.

    python3 tools/ci/check_workflow_freshness.py reproduction-walk.yml --max-age-days 8

Ported from Forge's tools/scripts/check_workflow_freshness.py (same logic, same exit taxonomy) so the two
repositories judge staleness the same way. Reads the GitHub API with $GITHUB_TOKEN (or $GH_TOKEN) for
$GITHUB_REPOSITORY (default agent-maestro/machlib). Exit 0 fresh, 1 stale or never succeeded, 2 the API
could not be read (never a pass).

TWO READS, and the newest success either shows: GitHub's `status=success` list has lagged behind the
unfiltered list (Forge, 2026-10-05, twice), so both are read and the newer success counts. A workflow
that really stopped succeeding has no recent success in either list, so this cannot hide one.
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import sys
import urllib.request


def verdict(runs: list[dict], now: datetime.datetime, max_age_days: float) -> tuple[bool, str]:
    """(fresh, message) from the API's workflow runs, in any order. Only a SUCCESS on the default branch counts."""
    ok = sorted((r for r in runs if r.get("conclusion") == "success"), key=lambda r: r.get("created_at", ""),
                reverse=True)
    if not ok:
        return False, "no successful run at all: the check this workflow holds has never passed here"
    last = datetime.datetime.fromisoformat(ok[0]["created_at"].replace("Z", "+00:00"))
    age = (now - last).total_seconds() / 86400
    if age > max_age_days:
        return False, (f"last success {ok[0]['created_at']} ({age:.1f} days ago, run {ok[0].get('id')}) is older "
                       f"than {max_age_days} days")
    return True, f"last success {ok[0]['created_at']} ({age:.1f} days ago, run {ok[0].get('id')})"


def newest_success(runs: list[dict]) -> str | None:
    """The creation time of the newest successful run a list holds, or None."""
    times = [r.get("created_at", "") for r in runs if r.get("conclusion") == "success"]
    return max(times) if times else None


def merged(*reads: list[dict]) -> list[dict]:
    """Runs from several reads of the API, each run once (by id)."""
    seen: dict = {}
    for runs in reads:
        for r in runs:
            seen.setdefault(r.get("id"), r)
    return list(seen.values())


def _runs(repo: str, workflow: str, token: str, *, filtered: bool = True) -> list[dict]:
    query = "?branch=master&status=success&per_page=5" if filtered else "?branch=master&per_page=30"
    url = f"https://api.github.com/repos/{repo}/actions/workflows/{workflow}/runs{query}"
    req = urllib.request.Request(url, headers={"Authorization": f"Bearer {token}",
                                               "Accept": "application/vnd.github+json"})
    with urllib.request.urlopen(req, timeout=60) as resp:
        return json.load(resp).get("workflow_runs", [])


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("workflows", nargs="+", help="workflow file names, e.g. corpus-nightly.yml")
    ap.add_argument("--max-age-days", type=float, default=2.0)
    args = ap.parse_args(argv)
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    repo = os.environ.get("GITHUB_REPOSITORY", "agent-maestro/machlib")
    if not token:
        print("UNEVALUABLE: no GITHUB_TOKEN/GH_TOKEN to read workflow runs", file=sys.stderr)
        return 2
    stale = False
    now = datetime.datetime.now(datetime.timezone.utc)
    for workflow in args.workflows:
        try:
            filtered = _runs(repo, workflow, token, filtered=True)
            unfiltered = _runs(repo, workflow, token, filtered=False)
        except Exception as exc:  # noqa: BLE001 -- unreadable is not fresh
            print(f"UNEVALUABLE: {workflow}: {exc}", file=sys.stderr)
            return 2
        a, b = newest_success(filtered), newest_success(unfiltered)
        if a != b:
            print(f"NOTE {workflow}: the success-filtered list's newest success is {a}, the unfiltered list's {b}; "
                  f"the newer one counts")
        fresh, message = verdict(merged(filtered, unfiltered), now, args.max_age_days)
        print(f"{'FRESH' if fresh else 'STALE'} {workflow}: {message}")
        stale |= not fresh
    return 1 if stale else 0


if __name__ == "__main__":
    sys.exit(main())
