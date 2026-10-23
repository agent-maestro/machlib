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
gate requires *both* instruments. Both present or the stop halts.

## Amendment 6 (2026-10-20): the gate at the destination, v4.32.2

Lean4Lean 408edad -- the last master commit pinning v4.32.2, carrying the issue #17 SIGSEGV fix
(9fc9c83) and the #14577 soundness fix (d7e70a5) -- replays MachLib, so criterion 7 has an instrument
at the destination again (`BUMP_PLAN.md` Amendment 6, owner's ruling "adopt, fix the proof"). Three
things this gate did could not work there, each measured on 2026-10-20:

* THE SPECIMEN'S SOURCE. lean4checker has no stable tag at or above v4.29, so `~/lean4checker-v4.32.2`
  cannot exist -- and `resolve` would then have fallen back to `~/lean4checker`, which is checked out
  at v4.14.0, without a word. The specimens are SOURCES compiled here at the pinned toolchain, so the
  newest stable tag at or below the pin supplies them (`specimen_source`), and the run names it.
  v4.28.0's AddFalse builds at v4.32.2 and is rejected: `(kernel) declaration type mismatch`.
* THE REPLAY. `lean4lean MachLib` starts one task per matched module at once (Main.lean's own
  fan-out): killed at 32 GB in 32 s, and LEAN_NUM_THREADS=6 did not bound it (24 GB in 16 s). Step 2
  runs ONE process per module, REPLAY_JOBS at a time, over the modules MachLib's sources declare.
  A target MATCHES BY PREFIX (`target.isPrefixOf m`, Main.lean), so a module that prefixes another is
  that fan-out again: this gate's first run listed the aggregator `MachLib`, and on 2026-10-21 that
  one job grew to 87 GB and the box's OOM killer took VS Code with it. Such a module is replayed
  through the modules it prefixes, and may only be left out when it declares nothing of its own
  (`declares_nothing`). Every module also runs under tools/capped_lean.sh at MODULE_CAP, so a
  runaway is one module's INSTRUMENT_OOM, never the desktop.
* FUEL. One module of 826 stopped at Lean4Lean's default fuel (Geometry/Apollonius/Coordinates, three
  numeral-heavy proofs; it passed at `lazyDelta = 1500`). The proofs were reworked, not the fuel
  raised: this gate passes NO `--config`, and a fuel exhaustion is its own verdict, INSTRUMENT_FUEL --
  neither an acceptance nor a rejection.

Run: python3 tools/axiom_ledger/check_lean4lean_replay.py
"""
from __future__ import annotations

import concurrent.futures
import datetime
import os
import re
import shutil
import signal
import subprocess
import sys
import time

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
#: Modules replayed at once, one lean4lean process each (Amendment 6). Peak per module, measured at
#: v4.32.2 over all 826: about 1 GB typical; the whole sweep took 196 s at 6.
REPLAY_JOBS = int(os.environ.get("LEAN4LEAN_JOBS", "6"))
MODULE_TIMEOUT_S = 1800
#: Memory per module process (tools/capped_lean.sh). 8x the typical peak; REPLAY_JOBS multiplies it.
MODULE_CAP = os.environ.get("LEAN4LEAN_MODULE_CAP", "8G")
CAPPED = os.path.join(FOUND, "tools", "capped_lean.sh")
#: A sweep that reached nothing reports a clean library. 826 modules on 2026-10-20.
POPULATION_FLOOR = 800
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


def _version(tag: str) -> tuple[int, ...] | None:
    m = re.fullmatch(r"v(\d+)\.(\d+)\.(\d+)", tag)
    return tuple(int(g) for g in m.groups()) if m else None


def specimen_source(ver: str) -> tuple[str, str]:
    """`(checkout, note)`: lean4checker AT the pinned version, else its newest STABLE tag below it.

    The specimens are sources this gate compiles at the PINNED toolchain, so the checkout supplies text,
    not a build -- what a version mismatch costs is that the files may not compile here, which step 1
    then reports as INSTRUMENT_ERROR. An rc tag is never taken. `("", why)` when there is none.
    """
    want = _version(ver)
    home = os.path.expanduser("~")
    found = []
    for name in os.listdir(home):
        if name.startswith("lean4checker-"):
            v = _version(name[len("lean4checker-"):])
            if v is not None and want is not None and v <= want:
                found.append((v, os.path.join(home, name)))
    if not found:
        return "", f"no ~/lean4checker-vX.Y.Z checkout at or below {ver}"
    v, path = max(found)
    tag = "v" + ".".join(map(str, v))
    if tag == ver:
        return path, f"lean4checker {tag}, the pinned version"
    return path, (f"lean4checker {tag}: no stable tag at {ver}, so the newest below it "
                  f"(BUMP_PLAN.md Amendment 6)")


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
    chk, chk_note = specimen_source(ver)
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
    print(f"    specimen source: {chk or '(none)'} -- {chk_note}"
          + (f", commit {commit_of(chk)}" if chk else ""))
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

    print("\n2 ENVIRONMENT REPLAYS through the second implementation, one module per process")
    if not scope_available():
        print("    [INSTRUMENT_UNCAPPED] no usable `systemd-run --user --scope`, so no module can be held to a")
        print("    memory cap -- and an uncapped replay took the desktop down on 2026-10-21. Not run. No verdict.")
        print("\nLEAN4LEAN-REPLAY GATE: FAIL")
        return 1
    tracked = replay_population()
    built = [m for m in tracked if os.path.exists(olean_path(m))]
    prefixes = [m for m in built if any(o.startswith(m + ".") for o in built)]
    declaring = [m for m in prefixes if not declares_nothing(m)]
    if declaring:
        print(f"    [POPULATION] {', '.join(declaring)}: Lean4Lean matches a target by PREFIX, so these cannot")
        print("    be replayed alone, and each declares something of its own that no other target reaches.")
        print("\nLEAN4LEAN-REPLAY GATE: FAIL")
        return 1
    population = [m for m in built if m not in prefixes]
    print(f"    {len(population)} modules: the {len(tracked)} MachLib sources git tracks, less the "
          f"{len(tracked) - len(built)} `lake build` does not build (Discovered/, and those "
          f"scripts/check_aggregator.sh documents as unreachable), less {len(prefixes)} imports-only "
          f"prefix module(s) ({', '.join(prefixes) or 'none'}); {REPLAY_JOBS} at a time, {MODULE_CAP} "
          f"each, Lean4Lean's DEFAULT fuel (no --config)")
    if len(population) < POPULATION_FLOOR:
        print(f"    [POPULATION] {len(population)} modules, under the floor of {POPULATION_FLOOR}: a sweep "
              f"that reached nothing would report a clean library. No verdict.")
        print("\nLEAN4LEAN-REPLAY GATE: FAIL")
        return 1
    t0 = time.monotonic()
    with concurrent.futures.ThreadPoolExecutor(max_workers=REPLAY_JOBS) as pool:
        results = list(pool.map(lambda m: replay_module(bin_, m), population))
    wall = time.monotonic() - t0
    by_kind: dict[str, list[tuple[str, str]]] = {}
    for module, kind, line, _ in results:
        by_kind.setdefault(kind, []).append((module, line))
    declarations = sum(n for *_, n in results)
    print(f"    {len(by_kind.get(PASS, []))} of {len(population)} modules replay clean, {declarations} "
          f"declarations checked, {wall:.0f} s")
    for kind in sorted(set(by_kind) - {PASS}):
        print(f"    {kind}: {len(by_kind[kind])} module(s)")
        for module, line in by_kind[kind][:10]:
            print(f"      {module}: {line}")
    print()
    if set(by_kind) == {PASS}:
        print("LEAN4LEAN-REPLAY GATE: PASS")
        print("  Grade: SECOND IMPLEMENTATION, SHARED LINEAGE -- not 'independent kernel'. Lean4Lean is")
        print("  a port of the C++ kernel by its author's own statement, and it carried #14576 until")
        print("  2026-07-29. This catches porting divergence and environment manipulation; it does NOT")
        print("  make a shared defect visible. See BUMP_PLAN.md's Amendment 2 finding.")
        return 0
    if REPLAY_FAIL in by_kind:
        print("  REPLAY_FAIL is a finding about MachLib. Every other kind above is the instrument's,")
        print("  and says nothing about our environment.")
    print("LEAN4LEAN-REPLAY GATE: FAIL")
    return 1


PASS, REPLAY_FAIL = "PASS", "REPLAY_FAIL"


def replay_population() -> list[str]:
    """Every module MachLib's SOURCES declare -- the repository's population, never the build directory's,
    which keeps the .olean of a module whose source was deleted, and once kept this gate's own specimen."""
    r = subprocess.run(["git", "ls-files", "MachLib.lean", "MachLib/*.lean"], cwd=FOUND,
                       capture_output=True, text=True, check=True)
    return sorted(p[:-len(".lean")].replace("/", ".") for p in r.stdout.split())


def olean_path(module: str) -> str:
    return os.path.join(olean_dir() or os.path.join(FOUND, ".lake", "build", "lib", "lean"),
                        *module.split(".")) + ".olean"


def scope_available() -> bool:
    """capped_lean.sh's own test: without a delegated scope it runs UNCAPPED, which this gate refuses."""
    r = subprocess.run(["systemd-run", "--user", "--scope", "-p", "MemoryMax=64M", "--quiet", "--", "true"],
                       capture_output=True)
    return r.returncode == 0


def declares_nothing(module: str) -> bool:
    """True when the module's source is imports and comments only -- the aggregator's shape.

    Lean block comments NEST, so they are stripped by depth, not by a regex."""
    src = open(os.path.join(FOUND, *module.split(".")) + ".lean").read()
    code, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            code.append(src[i])
            i += 1
    return all(not ln.strip() or ln.strip().startswith("import ") for ln in "".join(code).splitlines())


def replay_module(bin_: str, module: str) -> tuple[str, str, str, int]:
    """`(module, kind, line, declarations checked)` for ONE module, in a process of its own, under
    MODULE_CAP.

    Launched via Popen, not `run`, for ONE reason: the pid is matched against the kernel's OOM log
    afterwards. Correlating on the process NAME would pick up any other lean4lean the box happened to
    kill -- including this sweep's own neighbours. Its own SESSION, so a timeout kills the whole
    group: killing the direct child alone leaves lean4lean running under it.
    """
    since = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    proc = subprocess.Popen([CAPPED, "--cap", MODULE_CAP, "lake", "env", bin_, module], cwd=FOUND,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            start_new_session=True)
    try:
        so, se = proc.communicate(timeout=MODULE_TIMEOUT_S)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        proc.communicate()
        return module, "INSTRUMENT_TIMEOUT", f"no answer in {MODULE_TIMEOUT_S} s -- not a verdict", 0
    out = so + se
    m = re.search(r"checked (\d+) declarations", out)
    kind, line = classify(proc.returncode, out, proc.pid, since)
    return module, kind, line, int(m.group(1)) if m else 0


def classify(rc: int, out: str, pid: int, since: str) -> tuple[str, str]:
    """One module's outcome, BY MECHANISM -- never by message text alone.

    The whole-library form of this classifier was wrong three times in a row while being written, each
    time from substring matching: it called an instrument error an ACCEPTANCE, then a genuine kernel
    rejection a CRASH, because `uncaught exception:` is how lean4lean reports ordinary rejections. How the
    PROCESS died is the reliable signal: a memory fault aborts (a negative returncode under Python, or
    134/139 through a shell), a rejection is an orderly non-zero exit. A crash was seen for real at
    v4.20.1 (lean4lean 7cc5a77, `free(): double free detected in tcache 2`, on an environment that
    replayed clean at v4.19.0).

    A RESOURCE KILL IS NOT A CRASH, and the difference decides the remedy: on 2026-07-30 an OOM kill
    routed to "try the LAST commit pinning this version" cost four attempts, and the checkout was never
    the variable. SIGKILL is asked of the KERNEL LOG (`oom_evidence`). And a FUEL exhaustion -- `(kernel)
    deterministic timeout` -- is the checker running out of its own budget: no verdict either way, and
    per Amendment 6 the remedy is the proof, not the fuel.
    """
    if rc == 0:
        return PASS, ""
    if rc in (137, 143) and "capped_lean: KILLED AT THE" in out:
        # The cgroup's kill, reported by the wrapper that owns the cgroup. The kernel logs it against
        # lean4lean's pid as "Memory cgroup out of memory", which `oom_evidence` (this gate's pid,
        # "Out of memory") would never match -- it would call our own cap "something outside".
        return "INSTRUMENT_OOM", f"killed at the {MODULE_CAP} per-module cap -- a resource verdict, not a proof verdict"
    if rc in (-9, 137):
        oom = oom_evidence(pid, since)
        if oom:
            return "INSTRUMENT_OOM", f"{oom} -- the checker never finished, so it has no opinion"
        return "INSTRUMENT_KILLED", "SIGKILL with no OOM record in the kernel log: something outside stopped it"
    memory_fault = any(c in out for c in ("double free", "tcache", "Segmentation fault",
                                          "free(): ", "corrupted", "stack smashing"))
    if rc < 0 or rc in (134, 139) or memory_fault:
        return "INSTRUMENT_CRASH", f"the checker died (rc={rc}): {out.strip()[-160:]}"
    foreign = foreign_unknown_constants(out)
    if foreign:
        # BACKSTOP. 1b should catch this upstream: an instrument that cannot resolve names that are not
        # ours has not built its own environment, and an orderly non-zero exit is exactly what an
        # unearned conviction looks like.
        return "INSTRUMENT_ERROR", f"cannot resolve constants that are not ours: {', '.join(foreign[:6])}"
    tail = " ".join(ln for ln in out.strip().splitlines()[-3:] if not ln.startswith(("/", "backtrace")))
    if "deterministic timeout" in out:
        return "INSTRUMENT_FUEL", f"Lean4Lean's default fuel ran out: {tail[-200:]}"
    return REPLAY_FAIL, f"the checker rejected it: {tail[-300:]}"


if __name__ == "__main__":
    raise SystemExit(main())
