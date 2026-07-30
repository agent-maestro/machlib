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

## Two checks, and the second one is why this is a gate and not a script

1. **THE INSTRUMENT REJECTS.** Lean4Lean ships no negative tests, so it is fed lean4checker's
   `AddFalse` environment-smuggling specimen, copied from the version-matched lean4checker checkout —
   historical, not synthetic, and it must FAIL with a kernel error. **Re-fired every stop**, because a
   gate validated once at v4.19.0 is not known to be a gate at v4.20.1: the instrument is rebuilt at
   each version and so is the specimen.
2. **THE ENVIRONMENT REPLAYS.** `lean4lean MachLib` must exit 0.

The specimen is written into `MachLib/` only for the duration of this gate and removed afterwards,
including its `.olean`s — it constructs a proof of `False`, so it must never persist in the source tree,
and leaving its artifacts behind would (correctly) trip the artifact-drift tripwire.

UNAVAILABLE IS FAILURE, for either checker: the specimen comes from lean4checker's checkout, so this
gate requires *both* instruments at the pinned version. Both present or the stop halts.

Run: python3 tools/axiom_ledger/check_lean4lean_replay.py
"""
from __future__ import annotations

import os
import shutil
import subprocess
import sys

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SPECIMEN = [("OpenPrivate.lean", "MachLib/ZZZSpecimenOpenPrivate.lean"),
            ("AddFalse.lean", "MachLib/ZZZSpecimenAddFalse.lean")]


def resolve(base: str, ver: str) -> str:
    versioned = os.path.expanduser(f"{base}-{ver}")
    return versioned if os.path.exists(versioned) else os.path.expanduser(base)


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
    l4l = resolve("~/lean4lean", ver)
    chk = resolve("~/lean4checker", ver)
    bin_ = os.path.join(l4l, ".lake", "build", "bin", "lean4lean")

    print(f"lean4lean path   : {l4l}")
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

    print("\n2 ENVIRONMENT REPLAYS through the second implementation")
    p = subprocess.run(["lake", "env", bin_, "MachLib"], cwd=FOUND, capture_output=True, text=True)
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
    died_by_signal = p.returncode < 0 or p.returncode in (134, 139)
    memory_fault = any(c in out2 for c in ("double free", "tcache", "Segmentation fault",
                                           "free(): ", "corrupted", "stack smashing"))
    if ok:
        print("    PASS -- MachLib re-checks clean")
    elif died_by_signal or memory_fault:
        print("    [INSTRUMENT_CRASH] the checker died; this says NOTHING about our environment.")
        print("    Do not read as REPLAY_FAIL. Try the LAST commit pinning this version (the first")
        print("    one is the start of the support window, before that window's own fixes).")
        print("   ", out2.strip()[-300:])
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
