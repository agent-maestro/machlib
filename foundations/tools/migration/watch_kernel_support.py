"""WATCH: has the kernel-configuration decision expired yet?

## Why this file exists

`BUMP_PLAN.md`'s decision record chooses **v4.26.0 — unpatched kernel, two independent checkers** over
**v4.32.2 — patched kernel, one checker**, and the whole argument rests on one empirical fact:

    fix ∩ lean4checker ∩ Lean4Lean = ∅        (true on 2026-07-29)

**That is a fact about July 2026, not a fact about software.** A decision recorded as permanent when it
is calendar-contingent rots in the reassuring direction — the record keeps reading "considered, with
the tradeoff owned" long after the consideration expired. So the expiry condition is *monitored*:

    python3 tools/migration/watch_kernel_support.py                 # observe AND re-record
    python3 tools/migration/watch_kernel_support.py --out FILE      # observe only; the record is untouched

    exit 0  nothing has opened; the decision still holds (movement below the threshold is reported)
    exit 2  PARTIAL — one external checker reaches the fix. Leg 2 can launch; grade needs a re-read
    exit 3  OPEN — the intersection is non-empty. The decision has EXPIRED; re-read BUMP_PLAN.md
    exit 1  the watch could not run

## ON A SCHEDULE, AGAINST ITS RECORD (2026-11-27)

Run by hand, this watch last ran on record on 2026-07-30 and then not again for four months, in which
it missed what it exists to catch (MIGRATION_LOG.md, "Kernel watch on record and on a schedule").
`.github/workflows/kernel-watch.yml` now runs it weekly with `--out`, and `check_watch_record.py`
fails the run when today's observation differs from `watch_state.json` in any field but the
timestamp. So movement turns CI red until someone reads it and re-records; it cannot pass quietly.
The exit codes above are unchanged and still mean only the expiry condition: staleness of the
record is the record checker's verdict, not this watch's. One exception, so a record can never hold
a hole: a plain run that could not observe every field REFUSES to rewrite the record and exits 1.
Unauthenticated GitHub reads are limited to 60 an hour, so run it with GITHUB_TOKEN set (CI has one;
locally `GITHUB_TOKEN=$(gh auth token)`).

## UNAVAILABLE IS FAILURE

An offline run must never be readable as *"still empty"*. That is the same reassuring-direction error
the whole record is written against, so a network failure exits **1** and says so, and never prints a
verdict about the intersection it could not observe.

## What counts as "supported", and why the two sources are asymmetric

* **lean4checker** publishes a tag per release, so its support set is *the set of stable tags*.
  Release-candidate tags are excluded: a checker built from an `-rc` toolchain is a different
  instrument from the stable kernel it would be checking, and `check_kernel_replay.py` rejects exactly
  that mismatch.
* **Lean4Lean** has no tags for this purpose; `.olean` format is version-locked, so it supports
  **exactly the version its `lean-toolchain` pins** — not a range. Hence its support set is a
  singleton, read from the file at `master`.

The threshold — the first release carrying the #14577 kernel fix — is a **historical constant with
provenance** (v4.32.2 release notes: *"fixes a soundness bug in the kernel… nested inductive types
with phantom type parameters"*), not a count, so it is written down here rather than derived.
"""
from __future__ import annotations

import argparse
import base64
import datetime as dt
import json
import os
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

FIX = (4, 32, 2)  # first release containing #14577; see docstring
CHECKER_REPO = "https://github.com/leanprover/lean4checker"
L4L_REPO = "https://github.com/digama0/lean4lean"
L4L_PIN_URL = "https://raw.githubusercontent.com/digama0/lean4lean/master/lean-toolchain"
STATE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "watch_state.json")
# MachLib's own pin. The destination's grade waits on an instrument AT THIS VERSION, which is a
# different question from the threshold above (see l4l_at_destination).
TOOLCHAIN = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "lean-toolchain")
GITHUB_API = "https://api.github.com/repos/"
L4L_OWNER_REPO = "digama0/lean4lean"
# Commit histories are read up to this many pages of 100. One page was the old limit, and Lean4Lean's
# #14577 port was the 54th of them on 2026-11-27: a port that ages out of the window must not
# read as "no longer carries the fix".
FIX_SCAN_PAGES = 10

# BLIND SPOT FOUND 2026-07-29, and it mattered the same day.
#
# This watch originally asked only "does a checker EXIST at a version >= the fix?" -- a question about
# pins and tags. It never asked "does the checker itself CARRY the fix?", which is the question the
# whole class/instance argument depends on. Those come apart exactly when it counts:
#
#   Lean4Lean commit 0c38ab8 (2026-07-29) = "fix: soundness bug from leanprover/lean4#14577".
#   It PORTS the #14577 check while still pinning v4.29.0 -- i.e. a checker that carries the fix at a
#   toolchain BELOW the fix. The old logic would have reported STILL EMPTY on the day a patched
#   independent-ish checker first became available.
#
# So the watch now also greps the checkers' own commit logs for the fix. A checker that carries the
# check can detect the exploit class regardless of which kernel it is replaying against, which is the
# entire point of running a second implementation.
FIX_PR_MARKERS = ("14577", "14576")

# Titles that would indicate the instrument breakage is being tracked upstream. Matched on SYMPTOM
# names as well as our own issue number, because a watch that only recognised our issue would miss
# someone else reporting it first -- and one that only recognised symptoms would miss a retitle.
#
# FILED 2026-07-30 as digama0/lean4lean#17 (v4.26.0 + v4.29.0, SIGSEGV on Init.Prelude and
# `unknown constant 'String.ofList'`). THIS THREAD IS NOW LOAD-BEARING: per BUMP_PLAN.md Amendment 5
# the destination lands EXTERNALLY UNREPLAYED, and its grade upgrade triggers on either this issue
# closing or lean4checker growing a tag >= v4.29. The watch is literally watching that thread.
INSTRUMENT_BUG_ISSUE = 17
INSTRUMENT_BUG_MARKERS = ("String.ofList", "Char.ofNat", "unknown constant",
                          "Init.Prelude", "Init.Core")

# The commit reported upstream as fixing #17: "9fc9c83 fixes it, but the message says (#17) with no
# 'Fixes' mentioned. Everything passes the tests in v4.33.0-rc2." (lealcharro, 2026-10-19, on the
# issue, which is still open). REPORTED BY A THIRD PARTY, NOT MEASURED HERE: containing this commit
# makes a Lean4Lean build a candidate instrument, and only a positive control makes it one.
L4L_ISSUE17_FIX = "9fc9c83"


def ver(s: str) -> tuple[int, ...]:
    return tuple(int(x) for x in s.lstrip("v").split("."))


def fmt(v: tuple[int, ...]) -> str:
    return "v" + ".".join(str(x) for x in v)


def checker_stable_tags() -> list[tuple[int, ...]]:
    p = subprocess.run(["git", "ls-remote", "--tags", CHECKER_REPO],
                       capture_output=True, text=True, timeout=120)
    if p.returncode != 0:
        raise RuntimeError(f"git ls-remote {CHECKER_REPO} failed: {p.stderr.strip()[:200]}")
    tags = set()
    for m in re.finditer(r"refs/tags/v(\d+\.\d+(?:\.\d+)?)$", p.stdout, re.M):
        tags.add(ver(m.group(1)))
    if not tags:
        raise RuntimeError("no stable vX.Y.Z tags parsed — the tag scheme changed, or the parse did")
    return sorted(tags)


def l4l_pin() -> tuple[str, tuple[int, ...] | None]:
    """`(as written, version)`. A release candidate (`leanprover/lean4:v4.33.0-rc2`) parses to its version
    and is SHOWN as one: until 2026-10-20 the pattern accepted only `vX.Y.Z` at the end, so master moving to
    an rc read as "unparsed", and the state file kept the raw toolchain string. The pin is still only
    where master points: a Lean4Lean commit pinning MachLib's own version is a different fact, and
    BUMP_PLAN.md Amendment 6 records the one measured (408edad, v4.32.2); since 2026-11-27 the watch reads
    that fact too (l4l_at_destination)."""
    with urllib.request.urlopen(L4L_PIN_URL, timeout=60) as r:
        raw = r.read().decode().strip()
    m = re.search(r"v(\d+\.\d+(?:\.\d+)?)(-rc\d+)?$", raw)
    return raw, (ver(m.group(1)) if m else None)


def pin_label(raw: str, pin: tuple[int, ...] | None) -> str:
    """`v4.33.0-rc2` for an rc pin, `v4.29.0` for a stable one, `unparsed` for neither."""
    if pin is None:
        return "unparsed"
    rc = re.search(r"(-rc\d+)$", raw)
    return fmt(pin) + (rc.group(1) if rc else "")


def _api(url: str):
    """GET a GitHub API URL. Authenticated when CI provides a token: unauthenticated reads share a
    60-an-hour limit per IP, and a hosted runner's IP is shared."""
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "machlib-kernel-watch"}
    token = os.environ.get("GITHUB_TOKEN") or os.environ.get("GH_TOKEN")
    if token:
        headers["Authorization"] = f"Bearer {token}"
    with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=60) as r:
        return json.loads(r.read().decode())


def toolchain_ver(raw: str) -> tuple[int, ...] | None:
    """(major, minor, patch) of a `lean-toolchain` line; an -rc suffix is dropped (ordering only)."""
    m = re.search(r"v(\d+)\.(\d+)\.(\d+)", raw)
    return tuple(int(x) for x in m.groups()) if m else None


def carries_fix(repo: str) -> tuple[bool, str, str | None]:
    """Does this checker's own history contain the #14577 port? -- the question pins cannot answer.

    A checker that carries the check detects the exploit class whatever kernel it replays against, so
    this is what the class/instance argument actually rests on. Returns (carries, evidence, sha).
    """
    owner_repo = repo.rstrip("/").split("github.com/")[-1]
    seen = 0
    for page in range(1, FIX_SCAN_PAGES + 1):
        commits = _api(f"{GITHUB_API}{owner_repo}/commits?per_page=100&page={page}")
        for c in commits:
            msg = (c.get("commit", {}).get("message") or "").splitlines()[0]
            if any(m in msg for m in FIX_PR_MARKERS):
                return True, f"{c['sha'][:7]}  {c['commit']['committer']['date'][:10]}  {msg[:60]}", c["sha"]
        seen += len(commits)
        if len(commits) < 100:
            break
    return False, f"no commit referencing {'/'.join(FIX_PR_MARKERS)} in the last {seen}", None


def contains(base: str, head: str) -> bool:
    """Is commit `base` in the history of `head` (Lean4Lean)?"""
    status = _api(f"{GITHUB_API}{L4L_OWNER_REPO}/compare/{base}...{head}").get("status")
    if status is None:
        raise ValueError(f"compare {base}...{head} returned no status")
    return status in ("ahead", "identical")


def l4l_at_destination(target: tuple[int, ...], port_sha: str | None,
                       port_known: bool = True) -> dict | None:
    """Which Lean4Lean commits pin EXACTLY MachLib's toolchain, and do they carry the two fixes?

    Added 2026-11-27, the third blind spot. The watch read Lean4Lean's pin at master only, so its
    support set was "the version master pins TODAY". But every commit that ever pinned version V is
    a buildable instrument at V. Lean4Lean pinned exactly v4.32.2 -- this project's destination --
    from 779c51f (2026-08-04) until 5518bf8 moved it to v4.33.0-rc2 the same morning, after both
    the #14577 port and the #17 fix had landed (2026-08-02). Master's pin had moved past v4.32.2 by
    then, so the watch never saw a candidate the destination's upgrade trigger was waiting for.

    Returns {} when no commit pins the target, else the commit that set the pin, the last commit at
    it (the first parent of the next pin change; master if none), and whether that last commit
    contains the #14577 port and the reported #17 fix. A CANDIDATE, never a verdict: whether it
    replays is a positive control this watch does not run. Returns None (UNOBSERVED) when the pages
    read ran out before the history went below the target: a truncated read is not "none".
    """
    changes, complete = [], False
    for page in range(1, FIX_SCAN_PAGES + 1):
        batch = _api(f"{GITHUB_API}{L4L_OWNER_REPO}/commits?path=lean-toolchain&per_page=100&page={page}")
        changes += batch
        if len(batch) < 100:
            complete = True
            break
    newer = None  # the next pin change after the one being read (the list is newest first)
    for c in changes:
        blob = _api(f"{GITHUB_API}{L4L_OWNER_REPO}/contents/lean-toolchain?ref={c['sha']}")
        raw = base64.b64decode(blob["content"]).decode().strip()
        v = toolchain_ver(raw)
        if v is not None and v < target:
            complete = True  # the history went below the target: nothing older can pin it
            break
        if v == target and "-rc" not in raw:
            last = (_api(f"{GITHUB_API}{L4L_OWNER_REPO}/commits/{newer['sha']}")["parents"][0]["sha"]
                    if newer else _api(f"{GITHUB_API}{L4L_OWNER_REPO}/commits/master")["sha"])
            return {"set_by": c["sha"][:7], "set_on": c["commit"]["committer"]["date"][:10],
                    "last": last[:7],
                    # no port anywhere in the history (observed) is False; unread history is None
                    "carries_14577_port": (contains(port_sha, last) if port_sha
                                           else (False if port_known else None)),
                    "carries_issue17_fix": contains(L4L_ISSUE17_FIX, last)}
        newer = c
    return {} if complete else None


def l4l_instrument_bug() -> tuple[str, str, dict | None]:
    """Is the v4.26.0 instrument breakage fixed upstream yet? -- REPORTED, never exit-code-bearing.

    Added 2026-07-30. The pins above answer *which version Lean4Lean claims to support*; they cannot
    answer *whether it works there*, and stop 5 proved those are different questions: three builds all
    pinning v4.26.0, none able to replay `Init.Core`. A pin is a claim; a positive control is a
    measurement.

    This matters to the destination, not to the past. The v4.32.2 configuration wants this instrument
    working, so the cheapest way to make that more likely is to have the bug reported with a minimal
    repro and then to watch the tracker for movement. See `docs/lean4lean_string_literal_bug.md`.

    DELIBERATELY NOT A THRESHOLD: this returns a line to print. The watch's exit codes belong to the
    expiry condition and to nothing else -- widening what they mean would make two runs of this watch
    incomparable, which is the same error the gate-scoping deferrals keep refusing.

    RECORDED since 2026-11-27 (the third element: state, updated_at, comment count; None when the
    tracker could not be read). A state is not enough: on 2026-10-19 a comment reported the bug fixed
    while the issue stayed OPEN, and a watch reading the state alone printed the same line before and
    after. Any activity on the thread now moves the record, so the scheduled run goes red on it.
    """
    try:
        # Ours by NUMBER, read directly -- a retitle upstream must not read as "no longer filed", and
        # neither must the issue falling off the first page of a busy tracker.
        try:
            ours = _api(f"{GITHUB_API}{L4L_OWNER_REPO}/issues/{INSTRUMENT_BUG_ISSUE}")
        except urllib.error.HTTPError as e:
            if e.code != 404:
                raise
            ours = None
        issues = [] if ours else _api(f"{GITHUB_API}{L4L_OWNER_REPO}/issues?state=all&per_page=100&sort=updated")
    except Exception as e:  # noqa: BLE001 -- an unreadable tracker must not read as "no bug filed"
        return "COULD NOT READ", f"{type(e).__name__}: {e}", None
    hits = [i for i in issues
            if any(m in (i.get("title") or "") for m in INSTRUMENT_BUG_MARKERS)]
    top = ours or (hits[0] if hits else None)
    if not top:
        return "NOT FILED", "no issue matching the instrument breakage -- file it (see docs/)", {}
    state = top.get("state", "?").upper()
    note = f"#{top['number']} {(top.get('title') or '')[:52]}"
    if state == "CLOSED":
        note += "  <- CLOSED: re-probe the instrument, the destination grade may upgrade"
    record = {"number": top["number"], "state": top.get("state"),
              "updated_at": top.get("updated_at"), "comments": top.get("comments")}
    note += f"  (updated {(top.get('updated_at') or '?')[:10]}, {top.get('comments')} comments)"
    return state, note, record


def unobserved_fields(value, path: str = "") -> list[str]:
    """Paths of every None in an observation: a field this run could not read."""
    if value is None:
        return [path or "(root)"]
    if isinstance(value, dict):
        return [p for k, v in value.items() for p in unobserved_fields(v, f"{path}.{k}" if path else k)]
    return []


def load_state() -> dict:
    return json.load(open(STATE)) if os.path.exists(STATE) else {}


def report_movement(prev: dict, now: dict) -> None:
    """Every recorded field that moved since the record, not only the two the watch began with."""
    if not prev:
        print("no previous observation on file — this run establishes the reference point.")
        return
    print(f"since {prev['observed_at'][:10]} (the record):")
    for key in now:
        if key == "observed_at":
            continue
        was, cur = prev.get(key, "(not recorded)"), now[key]
        print(f"  {key:<22} {was} -> {cur}" if was != cur else f"  {key:<22} unchanged")


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description="Has the kernel-configuration decision expired yet?")
    ap.add_argument("--out", default=STATE,
                    help="where to write this observation (default: the record, watch_state.json). CI "
                         "writes elsewhere and compares with check_watch_record.py.")
    args = ap.parse_args(argv)
    print(f"KERNEL-SUPPORT WATCH   threshold = {fmt(FIX)} (first release with the #14577 fix)\n")
    try:
        tags = checker_stable_tags()
        raw_pin, pin = l4l_pin()
    except Exception as e:  # noqa: BLE001 -- whatever stopped it, this run observed nothing
        print(f"[WATCH_UNAVAILABLE] {type(e).__name__}: {e}")
        print("\nUNAVAILABLE IS FAILURE. This run observed NOTHING and asserts nothing about the")
        print("intersection. Re-run with network access; do not read this as 'still empty'.")
        return 1

    checker_max = tags[-1]
    print(f"lean4checker stable tags : {len(tags)}, newest {fmt(checker_max)}")
    print(f"Lean4Lean pin (master)   : {raw_pin}")

    # The question pins cannot answer -- see the blind-spot note at the top of this file.
    # A fix-port state that could not be read is recorded as None, never False: the record checker
    # refuses None as UNOBSERVED, where a False would read as the checker having lost the fix.
    l4l_port: str | None = None
    l4l_fix: bool | None
    chk_fix: bool | None
    try:
        l4l_fix, l4l_ev, l4l_port = carries_fix(L4L_REPO)
        chk_fix, chk_ev, _ = carries_fix(CHECKER_REPO)
    except Exception as e:  # noqa: BLE001 -- unread history must not read as "no"
        print(f"\n[FIX_PORT_UNKNOWN] could not read commit histories: {type(e).__name__}: {e}")
        print("  The pin/tag verdict below stands, but 'does the checker CARRY the fix' is UNKNOWN.")
        l4l_fix = chk_fix = None
        l4l_ev = chk_ev = "UNKNOWN -- history unavailable, do not read as 'no'"
    yn3 = {True: "YES", False: "no ", None: "?  "}
    print(f"Lean4Lean carries #14577 : {yn3[l4l_fix]}   {l4l_ev}")
    bug_state, bug_ev, bug_record = l4l_instrument_bug()
    print(f"Lean4Lean v4.26 bug      : {bug_state:<13}  {bug_ev}")
    print("  (reported only -- a pin says which version it CLAIMS; only a positive control measures")
    print("   whether it works there. Stop 5: three builds pinning v4.26.0, none replayed Init.Core)")
    print(f"lean4checker  carries it : {yn3[chk_fix]}   {chk_ev}")

    # MachLib's own pin, and the Lean4Lean commits that pin exactly it (see l4l_at_destination).
    dest_raw = open(TOOLCHAIN).read().strip()
    dest = toolchain_ver(dest_raw)
    try:
        at_dest = l4l_at_destination(dest, l4l_port, port_known=l4l_fix is not None) if dest else None
    except Exception as e:  # noqa: BLE001 -- unread history must not read as "none"
        print(f"\n[DESTINATION_UNKNOWN] could not read Lean4Lean's pin history: {type(e).__name__}: {e}")
        at_dest = None
    print(f"\nMachLib pins             : {dest_raw}  (foundations/lean-toolchain)")
    if at_dest is None:
        print("Lean4Lean at MachLib's pin: UNKNOWN -- do not read as 'none'")
    elif not at_dest:
        print("Lean4Lean at MachLib's pin: none -- no Lean4Lean commit has pinned this version")
    else:
        yn = {True: "yes", False: "NO", None: "unknown"}
        print(f"Lean4Lean at MachLib's pin: {at_dest['set_by']} (set {at_dest['set_on']}) .. {at_dest['last']}")
        print(f"  {at_dest['last']} carries the #14577 port: {yn[at_dest['carries_14577_port']]};"
              f" carries {L4L_ISSUE17_FIX} (reported to fix #17): {yn[at_dest['carries_issue17_fix']]}")
        print("  A CANDIDATE INSTRUMENT, not a verdict: only a positive control (replay Init.Core, then")
        print("  MachLib) says it works. This watch does not run one.")

    observation = {"observed_at": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                   "threshold": fmt(FIX), "checker_max": fmt(checker_max),
                   "checker_tag_count": len(tags), "l4l_pin": pin_label(raw_pin, pin),
                   "l4l_carries_fix": l4l_fix, "checker_carries_fix": chk_fix,
                   "intersection_open": pin is not None and pin in tags and pin >= FIX,
                   "destination": fmt(dest) if dest else dest_raw,
                   "l4l_at_destination": at_dest,
                   "l4l_issue": bug_record}
    print()
    report_movement(load_state(), observation)

    checker_ok = checker_max >= FIX
    l4l_ok = pin is not None and pin >= FIX
    both = pin is not None and pin in tags and pin >= FIX

    print(f"\nlean4checker reaches the fix : {'YES ' + fmt(checker_max) if checker_ok else 'no'}")
    print(f"Lean4Lean reaches the fix    : {'YES ' + pin_label(raw_pin, pin) if l4l_ok else 'no'}")

    holes = unobserved_fields(observation)
    refused = bool(holes) and os.path.abspath(args.out) == STATE
    if refused:
        print(f"\n[NOT RECORDED] unobserved: {', '.join(holes)}. A record must never hold a hole, so")
        print("  watch_state.json is untouched and this run exits 1. Re-run with GITHUB_TOKEN set.")
    else:
        with open(args.out, "w") as f:
            json.dump(observation, f, indent=1)
            f.write("\n")
        print(f"\nobservation written to {args.out}"
              + ("  (the record)" if os.path.abspath(args.out) == STATE else "  (the record is untouched)")
              + (f"  UNOBSERVED: {', '.join(holes)}" if holes else ""))

    print()
    # Printed BEFORE the verdict branches, on purpose: the first version sat in the exit-0
    # path only, so the two verdicts that actually mean 'something moved' were the two that
    # skipped the reminder. A reminder reachable from one branch is not a reminder.
    print_scheduled_reverifications()
    print()
    if both:
        print(f"INTERSECTION OPEN at {fmt(pin)} — THE DECISION HAS EXPIRED.")
        print("  Both checkers reach a kernel carrying the fix. The dual-kernel and patched-kernel")
        print("  configurations are no longer alternatives: re-read BUMP_PLAN.md's decision record,")
        print("  retarget the destination to the newest member of the intersection, and note in the")
        print("  record that the tradeoff it defends no longer exists.")
        return 1 if refused else 3
    if l4l_fix or chk_fix:
        which = "Lean4Lean" if l4l_fix else "lean4checker"
        print(f"FIX PORTED INTO A CHECKER — {which} carries the #14577 check itself.")
        print("  This is a DIFFERENT state from 'a checker exists at a kernel >= the fix', and it is")
        print("  the one the class/instance argument actually needs: a checker carrying the check can")
        print("  DETECT the exploit class whatever kernel it replays against. So a dual-replay stop")
        print("  below the fix threshold can now cover the instance -- by the second checker having")
        print("  the check, not by an assumption that it re-derived it.")
        print("  RE-READ BUMP_PLAN.md's destination table before the next pin advance.")
        return 1 if refused else 2
    if checker_ok or l4l_ok:
        which = "lean4checker" if checker_ok else "Lean4Lean"
        print(f"PARTIAL — {which} reaches the fix; the other does not.")
        print("  Leg 2's launch condition (at least one external checker at the destination) is MET,")
        print("  so the migration may proceed to the fix — but the grade drops to whatever that one")
        print("  checker earns. If it is lean4checker alone, that is SECOND OPINION, not independent")
        print("  kernel, and the registry row must say so.")
        return 1 if refused else 2
    print("STILL EMPTY — the decision holds, and the wait remains monitored rather than standing.")
    print("  Cheapest way to open it from our side: contribute the lean4checker tag upstream. Its")
    print("  history is mechanical per release, so it is plausibly a PR, not a project.")
    print()
    return 1 if refused else 0


def print_scheduled_reverifications() -> None:
    """Other things that expire on this watch's cadence, printed so they cannot be quietly skipped.

    Added 2026-07-30. monogate.org/accountability grades this project against the Leiden Declaration,
    and a grade is only as current as the last time a human re-read it against its artifact. The link
    gate (`blog/scripts/check_accountability.py`) proves the artifacts still RESOLVE on every CI run;
    it cannot prove a grade is still CORRECT. That second half is human work on a clock, and a clock
    with no alarm is a wish -- so the alarm lives here, next to the other thing this project promised
    to re-check quarterly rather than remember.
    """
    print("SCHEDULED RE-VERIFICATIONS (this watch's cadence, not just the intersection):")
    for name, due, how in (
        # Re-graded 2026-11-25 (monogate 51a974ce); quarterly from there. The monogate repo's
        # check_accountability.py fails every row from 2027-03-26 (120 days), so this is the warning.
        ("accountability page grades", "2027-02-23",
         "in the monogate repo: re-read each grade in blog/src/data/accountability.json against its "
         "artifact, bump last_verified, downgrade anything whose evidence moved, then run "
         "blog/scripts/check_accountability.py (it fails every row from 2027-03-26)"),
    ):
        try:
            days = (dt.date.fromisoformat(due) - dt.date.today()).days
            when = f"in {days}d" if days >= 0 else f"OVERDUE by {-days}d"
        except Exception:  # noqa: BLE001
            when = "?"
        print(f"  · {name:<28} due {due}  ({when})")
        print(f"      {how}")


if __name__ == "__main__":
    raise SystemExit(main())
