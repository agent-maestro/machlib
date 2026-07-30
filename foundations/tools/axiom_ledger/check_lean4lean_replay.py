"""CRITERION 7: replay the compiled environment through Lean4Lean — the SECOND implementation.

## What this earns, and the phrase it does NOT earn

`BUMP_PLAN.md` Amendment 1 added this gate at stops 3–5. Amendment 2's ⚠ finding then established what
it is worth, and the honest label is **"second implementation, shared lineage"**:

* Lean4Lean's own README: *"derived directly from the C++ kernel implementation, and as such likely
  shares some implementation bugs with it (it's not really an independent implementation)"*.
* Empirically confirmed for the bug that started this migration: Lean4Lean commit `0c38ab8`
  (2026-07-29) is *"fix: soundness bug from leanprover/lean4#14577"* — **it had #14576 too**, in the
  ported `ElimNestedInductive` path.

So this gate does **not** license "verified by two independent kernels". What it does buy is real:
a **different implementation in a different language**, which catches porting divergence, environment
manipulation, and any defect the two codebases do *not* happen to share. And at v4.29.0 specifically it
buys the thing the kernel cannot yet give us — a checker that **carries the #14577 check**.

## Three checks, and the middle one is the half the protocol was missing

1. **THE INSTRUMENT REJECTS.** Lean4Lean ships no negative tests, so it is fed lean4checker's
   `AddFalse` environment-smuggling specimen, copied from the version-matched lean4checker checkout —
   historical, not synthetic, and it must FAIL with a kernel error. **Re-fired every stop**, because a
   gate validated once at v4.19.0 is not known to be a gate at v4.20.1: the instrument is rebuilt at
   each version and so is the specimen.
1b. **THE INSTRUMENT HOLDS FIRE.** Two known-good specimens must PASS: `Init.Core` (Lean's own core)
   and `MachLib.Sign` (ours). **Negative controls prove it can fire; positive controls prove it can
   hold fire, and a gate needs both before any verdict it renders is worth reading.** Two specimens
   because breakage is feature-conditional — see `POSITIVE_CONTROLS`. Five seconds each.
2. **THE ENVIRONMENT REPLAYS.** `lean4lean MachLib` must exit 0. Only reached when 1 and 1b both
   pass, because a checker that cannot accept a known-good environment can only convict.

The specimen is written into `MachLib/` only for the duration of this gate and removed afterwards,
including its `.olean`s — it constructs a proof of `False`, so it must never persist in the source tree,
and leaving its artifacts behind would (correctly) trip the artifact-drift tripwire.

UNAVAILABLE IS FAILURE, for either checker: the specimen comes from lean4checker's checkout, so this
gate requires *both* instruments at the pinned version. Both present or the stop halts.

Run: python3 tools/axiom_ledger/check_lean4lean_replay.py
"""
from __future__ import annotations

import datetime
import os
import re
import shutil
import subprocess
import sys

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SPECIMEN = [("OpenPrivate.lean", "MachLib/ZZZSpecimenOpenPrivate.lean"),
            ("AddFalse.lean", "MachLib/ZZZSpecimenAddFalse.lean")]


def resolve(base: str, ver: str, override: str = "") -> str:
    """Version-path by default; an explicit env override when a SECOND checkout of the same
    version must be distinguished.

    Both exist because a Lean4Lean *version pin* is not a Lean4Lean *build*: several commits pin
    the same toolchain, and they do not behave alike -- v4.26.0's last commit SIGSEGVs on an
    environment its first commit may well replay clean. The version path alone cannot name which
    one ran, so swapping directories to test the other would have written a log byte-identical to
    the run it was meant to distinguish. `LEAN4LEAN_PATH` selects the checkout deliberately, and
    `commit_of` below records what actually ran. Provenance, not a threshold: no criterion moves.
    """
    if override:
        return os.path.expanduser(override)
    versioned = os.path.expanduser(f"{base}-{ver}")
    return versioned if os.path.exists(versioned) else os.path.expanduser(base)


def commit_of(path: str) -> str:
    """The checker's commit, MEASURED from its checkout -- never inferred from its directory name."""
    r = subprocess.run(["git", "-C", path, "rev-parse", "--short", "HEAD"],
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 else "UNKNOWN (not a git checkout)"


# POSITIVE CONTROLS -- the missing half of the maiden-run protocol. Two, not one, because
# instrument breakage is FEATURE-CONDITIONAL: v4.26.0's `String.ofList`/`Char.ofNat` failure lives in
# `Main.lean`'s string-literal special case, so a checker that replays core cleanly can still choke on
# whichever literal forms a given library happens to exercise. Core proves it can read Lean; a module
# of ours proves it can read THIS environment's encoding. Neither implies the other.
#
# `MachLib.Sign` earned its slot on 2026-07-30 by being the minimisation that broke both v4.26.0
# checkouts -- a specimen with a firing history, per the standing preference for historical over
# synthetic. Replace it only with another module that has one.
POSITIVE_CONTROLS = [("Init.Core", "core   -- can the instrument read Lean itself?"),
                     ("MachLib.Sign", "ours   -- can it read our environment's encoding?")]


def foreign_unknown_constants(out: str) -> list[str]:
    """Names the checker called unknown that CANNOT be our fault -- anything outside `MachLib`.

    The general rule, not the incident: our environment can only be indicted through our own names.
    A checker that cannot resolve `Nat`, `Eq` or `String.ofList` has failed to build its own
    environment and is in no condition to render a verdict about ours -- reporting that as
    REPLAY_FAIL would convict a clean tree on the testimony of an instrument that cannot read `Nat`.
    """
    names = re.findall(r"unknown constant '([^']+)'", out)
    return sorted({n for n in names if not n.startswith("MachLib.")})


def describe_failure(rc: int, out: str) -> str:
    """One line naming the MECHANISM of a failed invocation, for the positive controls."""
    if rc in (-9, 137):
        return "killed (SIGKILL -- resource, not fault)"
    if rc < 0 or rc in (134, 139):
        return f"died by signal (rc={rc}; SIGSEGV/SIGABRT -- a fault inside the checker)"
    foreign = foreign_unknown_constants(out)
    if foreign:
        return f"cannot resolve non-MachLib constants: {', '.join(foreign[:4])}"
    return f"exit {rc}: {out.strip()[-160:] or '(no output)'}"


def oom_evidence(pid: int, since: str) -> str:
    """Ask the KERNEL whether it killed this pid, instead of inferring OOM from the signal.

    SIGKILL alone does not mean out-of-memory: an operator's `kill -9`, a cgroup limit and the
    global OOM killer are indistinguishable from inside the dying process, which is precisely why
    the process's own output cannot settle it -- SIGKILL is uncatchable, so an OOM'd checker prints
    NOTHING. An empty output tail was the tell that went unread on 2026-07-30.

    The kernel log is the only witness that separates them, and it carries `anon-rss` -- the number
    that decides whether a retry is worth attempting or whether the run needs less concurrency.
    Returns a human-readable line, or "" when the kernel has no record (in which case something
    else sent the signal, and saying OOM would be a guess wearing a measurement's clothes).
    """
    r = subprocess.run(["journalctl", "-k", "--since", since, "--no-pager"],
                       capture_output=True, text=True)
    if r.returncode != 0:
        return ""
    for line in r.stdout.splitlines():
        if f"Killed process {pid} " in line and "Out of memory" in line:
            # The kernel writes `anon-rss:94794704kB,` -- WITH the trailing comma, because the field
            # sits mid-list. `rstrip("kB")` leaves that comma, `isdigit()` then says no, and the
            # number silently becomes 0.0 GiB: a plausible wrong answer that reads as a real
            # measurement. Keep the digits and nothing else.
            raw = next((f.split(":", 1)[1] for f in line.split() if f.startswith("anon-rss:")), "")
            kb = int("".join(c for c in raw if c.isdigit()) or 0)
            return f"kernel OOM-killed pid {pid} at anon-rss {kb / 1048576:.1f} GiB"
    return ""


def olean_dir() -> str:
    for root, _, files in os.walk(os.path.join(FOUND, ".lake", "build", "lib")):
        if "MachLib.olean" in files:
            return root
    return ""


def cleanup(paths: list[str]) -> None:
    """Remove specimen sources AND their oleans -- at the MODULE path, matching how they were written.

    This got it wrong once, and the consequence was not a missing file: the leftover
    `MachLib/ZZZSpecimenAddFalse.olean` was still on the search path when step 2 replayed `MachLib`,
    so the second check dutifully found a smuggled proof of `False` that step 1 had planted. A gate
    that fails to clean up does not merely leave litter -- it CONTAMINATES ITS OWN NEXT CHECK.
    """
    od = olean_dir()
    for p in paths:
        for f in (os.path.join(FOUND, p), os.path.join(od, p.replace(".lean", ".olean"))):
            if os.path.exists(f):
                os.remove(f)


def main() -> int:
    want = open(os.path.join(FOUND, "TOOLCHAIN.lock")).read().split()[0]
    ver = want.split(":")[-1]
    l4l = resolve("~/lean4lean", ver, os.environ.get("LEAN4LEAN_PATH", ""))
    chk = resolve("~/lean4checker", ver)
    bin_ = os.path.join(l4l, ".lake", "build", "bin", "lean4lean")

    print(f"lean4lean path   : {l4l}")
    print(f"lean4lean commit : {commit_of(l4l)}")
    # Recorded, never set here. The fan-out width changes peak memory by an order of magnitude, so a
    # log that omits it cannot explain why one run died and the next did not -- but defaulting it
    # inside the gate would silently make two stops incomparable. Provenance, not a threshold.
    print(f"LEAN_NUM_THREADS : {os.environ.get('LEAN_NUM_THREADS', '(unset -- one task per core)')}")
    if not os.path.exists(bin_):
        print(f"[INSTRUMENT_ABSENT] no lean4lean at {bin_}")
        print(f"  git clone https://github.com/digama0/lean4lean ~/lean4lean-{ver}")
        print(f"  cd ~/lean4lean-{ver} && git checkout <commit pinning {ver}> && lake build lean4lean")
        return 1
    have = open(os.path.join(l4l, "lean-toolchain")).read().strip()
    print(f"lean4lean toolchain: {have}\nledger toolchain   : {want}")
    if have != want:
        print(f"\n[VERSION_MISMATCH] built against {have}, we pin {want}. `.olean` format is "
              f"version-locked; a checker that cannot read our artifacts is not a second opinion.")
        return 1

    print("\n1 INSTRUMENT REJECTS (lean4checker's AddFalse smuggling specimen must FAIL)")
    src = os.path.join(chk, "Lean4CheckerTests")
    if not os.path.isdir(src):
        print(f"    [INSTRUMENT_UNVALIDATED] no specimen source at {src}")
        print("    An unfired checker's PASS and FAIL are equally uninformative. UNAVAILABLE IS FAILURE.")
        return 1
    dsts = [d for _, d in SPECIMEN]
    try:
        for name, dst in SPECIMEN:
            text = open(os.path.join(src, name)).read().replace(
                "import Lean4CheckerTests.OpenPrivate", "import MachLib.ZZZSpecimenOpenPrivate")
            open(os.path.join(FOUND, dst), "w").write(text)
        od = olean_dir()
        for _, dst in SPECIMEN:
            # The olean must land at the MODULE path, not the olean root: `MachLib.ZZZSpecimenAddFalse`
            # lives at `<root>/MachLib/ZZZSpecimenAddFalse.olean`. Writing it to `<root>/` made
            # lean4lean report "Could not find any oleans", which the first version of this gate then
            # mislabelled as an ACCEPTED False -- see the three-way classification below.
            out = os.path.join(od, dst.replace(".lean", ".olean"))
            os.makedirs(os.path.dirname(out), exist_ok=True)
            b = subprocess.run(["lake", "env", "lean", "-o", out, dst],
                               cwd=FOUND, capture_output=True, text=True)
            if b.returncode != 0:
                print(f"    [INSTRUMENT_ERROR] could not build the specimen {dst}:")
                print("   ", (b.stdout + b.stderr).strip()[-300:])
                return 1
        r = subprocess.run(["lake", "env", bin_, "MachLib.ZZZSpecimenAddFalse"],
                           cwd=FOUND, capture_output=True, text=True)
        out = r.stdout + r.stderr
        # THREE outcomes, never two. Conflating "the specimen was not checked" with "the specimen
        # passed" is how a gate reports a false accusation: the first version of this check saw a
        # nonzero exit without the word "kernel" and printed "it ACCEPTED a smuggled False", when in
        # fact the instrument had errored before checking anything.
        if r.returncode == 0:
            verdict, rejected = "FAIL -- it ACCEPTED a smuggled False", False
        elif "kernel" in out:
            verdict, rejected = "PASS -- rejected with a kernel error, naming it", True
        else:
            verdict, rejected = "[INSTRUMENT_ERROR] nonzero exit, but NOT a kernel rejection -- " \
                                "the specimen was not checked; this is not an acceptance", False
        print(f"    {verdict}")
        if not rejected:
            print("   ", out.strip()[-400:])
    finally:
        cleanup(dsts)
    if not rejected:
        return 1

    print("\n1b INSTRUMENT HOLDS FIRE (known-good specimens must PASS -- both directions, not one)")
    unusable = []
    for module, why in POSITIVE_CONTROLS:
        r = subprocess.run(["lake", "env", bin_, module], cwd=FOUND, capture_output=True, text=True)
        if r.returncode == 0:
            print(f"    PASS  {module:<16} {why}")
        else:
            print(f"    FAIL  {module:<16} {why}")
            print(f"          {describe_failure(r.returncode, r.stdout + r.stderr)}")
            unusable.append(module)
    if unusable:
        print(f"\n    [INSTRUMENT_UNUSABLE] the checker cannot replay {', '.join(unusable)}.")
        if "Init.Core" in unusable:
            print("    Init.Core is LEAN'S OWN CORE -- MachLib is not in the hypothesis space. The void")
            print("    is the instrument's, not the environment's, and it is proven so UPSTREAM of the")
            print("    subject. Criterion 7 is UNMEASURABLE at this version, which is not the same as")
            print("    waived: record it, do not silently drop it.")
        else:
            print("    Core replays but ours does not, so the breakage is FEATURE-CONDITIONAL -- the")
            print("    instrument meets something in our encoding it cannot handle. Still the")
            print("    instrument's void, but narrow it before reporting upstream.")
        print("    Step 2 is NOT run: a checker that cannot accept a known-good environment can only")
        print("    produce an unearned conviction, and REPLAY_FAIL is the most expensive verdict here.")
        print("\nLEAN4LEAN-REPLAY GATE: FAIL [INSTRUMENT_UNUSABLE -- no verdict about MachLib]")
        return 1

    print("\n2 ENVIRONMENT REPLAYS through the second implementation")
    # Launched via Popen, not `run`, for ONE reason: we need the pid to match against the kernel's
    # OOM log afterwards. Correlating on the process NAME instead would pick up any other lean4lean
    # the box happened to kill -- including this gate's own earlier attempts.
    since = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    proc = subprocess.Popen(["lake", "env", bin_, "MachLib"], cwd=FOUND,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    so, se = proc.communicate()
    p = subprocess.CompletedProcess(proc.args, proc.returncode, so, se)
    out2 = p.stdout + p.stderr
    ok = p.returncode == 0
    # Same three-way discipline as step 1: a CRASH is not a verdict about our environment. Seen for
    # real at v4.20.1 with Lean4Lean commit 7cc5a77 -- deterministic `free(): double free detected in
    # tcache 2`, with a stack trace inside lean4lean, on an environment that replayed CLEAN through
    # the same checker at v4.19.0. Reporting that as REPLAY_FAIL would have accused MachLib of a
    # defect that lives in the instrument.
    # CLASSIFY BY MECHANISM, NOT BY MESSAGE TEXT. This classifier was wrong three times in a row while
    # being written, each time from substring matching: it called an instrument error an ACCEPTANCE, and
    # then called a genuine kernel rejection a CRASH -- because `uncaught exception:` is how lean4lean
    # reports ordinary rejections. The reliable signal is how the PROCESS died: a memory fault aborts
    # (SIGABRT/SIGSEGV -> negative returncode under Python, or 134/139 through a shell), whereas a
    # rejection is an orderly non-zero exit.
    # A RESOURCE KILL IS NOT A CRASH, and the difference decides the remedy. Both arrive as a
    # negative returncode, so the original two-way split (`died_by_signal` -> INSTRUMENT_CRASH)
    # routed an out-of-memory kill to the advice "try the LAST commit pinning this version". That
    # advice was followed on 2026-07-30: f37aeab -> 6bca7f6, two more OOM kills, and the checkout
    # was never the variable. Four attempts, ~62-90 GiB anon-rss each, all inside the busiest hour
    # of the box's day.
    # SIGKILL (-9) is its OWN mechanism: the process did not fault, it was executed. Separating it
    # costs one branch and one query to the kernel log -- and it is the same lesson step 1 already
    # carries, arriving one layer down. THREE outcomes were not enough; there are four.
    killed_hard = p.returncode in (-9, 137)
    oom = oom_evidence(proc.pid, since) if killed_hard else ""
    died_by_signal = p.returncode < 0 or p.returncode in (134, 139)
    memory_fault = any(c in out2 for c in ("double free", "tcache", "Segmentation fault",
                                           "free(): ", "corrupted", "stack smashing"))
    if ok:
        print("    PASS -- MachLib re-checks clean")
    elif oom:
        print(f"    [INSTRUMENT_OOM] {oom}. NOT a crash and NOT a verdict about our environment --")
        print("    the checker never finished, so it never had an opinion. Do NOT change checkouts.")
        print("    lean4lean's Main.lean pushes one `IO.asTask` per matched module with NO bound, so")
        print("    `MachLib` fans out across the whole pool at once. Levers, in order:")
        print("      1. LEAN_NUM_THREADS=4 -- bounds the fan-out. Same binary, same target, same")
        print("         semantics; only scheduler width moves, so no criterion moves either.")
        print("      2. Run it when the box is quiet. On the GB10 the GPU tenants share ONE 128 GB")
        print("         pool with the CPU, so peak headroom swings ~40 GB with what ollama holds.")
        print("      3. Chunk the target -- one process per module or per batch; memory is reclaimed")
        print("         at each exit, and a failure names the module instead of the library.")
    elif killed_hard:
        print("    [INSTRUMENT_KILLED] SIGKILL with no OOM record in the kernel log. Something")
        print("    outside this gate stopped the checker -- an operator, a cgroup, a reaper. Not a")
        print("    verdict about our environment, and not evidence about the checkout either.")
    elif died_by_signal or memory_fault:
        print("    [INSTRUMENT_CRASH] the checker died; this says NOTHING about our environment.")
        print("    Do not read as REPLAY_FAIL. Try the LAST commit pinning this version (the first")
        print("    one is the start of the support window, before that window's own fixes).")
        print("   ", out2.strip()[-300:])
    elif foreign_unknown_constants(out2):
        # BACKSTOP. 1b should have caught this upstream; if it did not, the instrument broke on
        # something the controls do not exercise, and an orderly non-zero exit is EXACTLY what an
        # unearned conviction looks like. On 2026-07-30 only an OOM kill stood between this branch
        # and REPLAY_FAIL against a tree lean4checker had passed forty minutes earlier.
        names = foreign_unknown_constants(out2)
        print("    [INSTRUMENT_ERROR] the checker could not resolve constants that are not ours:")
        print(f"      {', '.join(names[:8])}")
        print("    An instrument that cannot resolve these has not built its own environment, so it")
        print("    has no environment to check ours against. NOT a REPLAY_FAIL, and 1b needs a")
        print("    specimen that exercises whatever this run reached and the controls did not.")
    else:
        print("    REPLAY_FAIL -- the checker rejected our environment. This IS a finding.")
        print("   ", out2.strip()[-600:])

    print()
    if ok:
        print("LEAN4LEAN-REPLAY GATE: PASS")
        print("  Grade: SECOND IMPLEMENTATION, SHARED LINEAGE -- not 'independent kernel'. Lean4Lean is")
        print("  a port of the C++ kernel by its author's own statement, and it carried #14576 until")
        print("  2026-07-29. This catches porting divergence and environment manipulation; it does NOT")
        print("  make a shared defect visible. See BUMP_PLAN.md's Amendment 2 finding.")
        return 0
    print("LEAN4LEAN-REPLAY GATE: FAIL")
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
