#!/usr/bin/env python3
"""Gate 13 — the MachLib.Real soundness witness must be LIVE, not merely present.

MachLib is Mathlib-free by construction, so nothing inside this repo can check that its
axioms are satisfiable. That check lives in a separate project (`monogate-lean`) which
imports BOTH Mathlib and MachLib and, for each trusted axiom, verifies that a Mathlib term
inhabits the axiom's interpreted type. `MachLib.Real |= R`.

The failure this gate exists for actually happened. On 2026-07-31 MachLib's toolchain moved
to v4.32.2; the witness project stayed on v4.14.0 and was therefore building MachLib's
CURRENT source under the OLD toolchain, which cannot compile. The witness was dark for 33
days and nothing said so -- the ledger still reported "trusted", because "trusted" was an
assertion about a check that was no longer running. A certificate that cannot build is not
a weaker certificate; it is no certificate.

Three ways it can rot, all FAIL:
  1. toolchain skew   -- the witness pins a different Lean than MachLib, so it cannot build
  2. unaccounted      -- a trusted axiom the witness does not witness/classify at all
  3. stale accounting -- the witness accounts for an axiom the ledger no longer carries

Absent witness project => UNAVAILABLE (exit 2), never a silent pass:
an unavailable check is not a passing check, and it is not a failing one either.
"""
import re, sys, pathlib

HERE = pathlib.Path(__file__).resolve().parent.parent          # machlib/foundations
WITNESS = HERE.parent.parent / "monogate-lean"                  # sibling project
BRIDGE = WITNESS / "MonogateEML" / "AxiomWitnessBridge.lean"

def strip_comments(s):
    """Strip Lean comments, but NOT inside string literals.

    A naive version treats `--` as a line comment even inside a `"..."` reason string, which
    truncates the entry at that point and silently loses everything after it. That is exactly
    how a gap entry reading "cheaper than it looks -- do this one first" came back UNACCOUNTED
    while gate 13 (which only needs the NAME, before the dashes) reported it fine.
    """
    out, i, depth, instr = [], 0, 0, False
    while i < len(s):
        c = s[i]
        if instr:
            out.append(c)
            if c == '\\' and i + 1 < len(s): out.append(s[i+1]); i += 2; continue
            if c == '"': instr = False
            i += 1; continue
        if not depth and c == '"':
            instr = True; out.append(c); i += 1; continue
        if s.startswith('/-', i): depth += 1; i += 2; continue
        if s.startswith('-/', i) and depth: depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        out.append(c); i += 1
    return ''.join(out)
def bracket_span(s, pat):
    m = re.search(pat, s)
    if not m: return None
    i = s.index('[', m.end()); depth = 0; j = i
    while j < len(s):
        if s[j] == '[': depth += 1
        elif s[j] == ']':
            depth -= 1
            if depth == 0: break
        j += 1
    return strip_comments(s[i:j+1])

def names(s, pat, entry=False):
    body = bracket_span(s, pat)
    if body is None: return None
    return set(re.findall(r'\(\s*`([A-Za-z_][\w.]*)\s*,', body) if entry
               else re.findall(r'`([A-Za-z_][\w.]*)', body))

def analyze(ledger_src, bridge_src, mine, theirs):
    """The audit, as a pure function of its four inputs.

    Lifted out of `main` so `--selftest` can run THIS function -- the one that ships -- against
    deliberately corrupted copies of the real files. The selftest this replaced re-implemented
    the predicates inline (literally `skew = ("v4.32.2" != "v4.14.0")`) and then checked its own
    re-implementation, which can only ever confirm that Python compares strings. It would have
    stayed green through ANY bug in the code below, including a regex that had stopped matching.
    A predicate re-implemented in the test is not the predicate that ships.

    Returns (fails, stats). `stats is None` means the ledger could not be parsed at all.
    """
    trusted = names(ledger_src, r'def trustedFootprint\s*:\s*List Name\s*:=\s*')
    if trusted is None:
        return ["PARSE — cannot parse AxiomLedger.trustedFootprint"], None

    registry = names(bridge_src, r'def witnessRegistry\s*:\s*List \(Name × TSyntax `term\)\s*:=\s*', entry=True) or set()
    standard = names(bridge_src, r'def standardAxioms\s*:\s*List Name\s*:=\s*') or set()
    mapped   = names(bridge_src, r'def mappedConstants\s*:\s*List Name\s*:=\s*') or set()
    gap      = names(bridge_src, r'def witnessGap\s*:\s*List \(Name × String\)\s*:=\s*', entry=True) or set()
    bridge   = names(bridge_src, r'def bridgeAxioms\s*:\s*List Name\s*:=\s*') or set()
    accounted = registry | standard | mapped | gap | bridge

    fails = []
    # 1. toolchain skew -- the defect that went undetected for 33 days
    if mine != theirs:
        fails.append(f"TOOLCHAIN SKEW — MachLib pins {mine!r}, witness pins {theirs!r}. "
                     f"The witness builds MachLib's current source under a different Lean and "
                     f"CANNOT compile; every 'trusted' verdict downstream is unverified.")
    # 2. unaccounted trusted axioms
    unacct = sorted(trusted - accounted)
    if unacct:
        fails.append(f"UNACCOUNTED — {len(unacct)} trusted axiom(s) with NO Mathlib witness and "
                     f"no recorded classification: {unacct[:8]}{' …' if len(unacct) > 8 else ''}")
    # 3. stale EXCUSES only. A stale entry in `witnessGap` or `bridgeAxioms` is a defect: it
    #    excuses an axiom from being witnessed, so if it drifts off the ledger it can later mask
    #    a genuinely unwitnessed one. A witness for an axiom that is no longer in the trusted
    #    footprint is NOT a defect -- it is a witness we happen to still hold (e.g. `tanh_neg`
    #    and `tanh_zero`, still axioms in MachLib/Trig.lean, just not in `trustedFootprint`).
    #    Flagging those would convict the innocent and train the next agent to delete evidence.
    stale = sorted((gap | bridge) - trusted)
    if stale:
        fails.append(f"STALE EXCUSE — {len(stale)} entr(y/ies) (gap/float-bridge) no longer in "
                     f"the ledger — an excuse that outlives its axiom can mask a real gap: {stale}")

    stats = dict(trusted=trusted, registry=registry, standard=standard, mapped=mapped,
                 gap=gap, bridge=bridge, accounted=accounted, unacct=unacct,
                 mine=mine, theirs=theirs,
                 extra_witnesses=sorted(registry - trusted - standard - mapped))
    return fails, stats


# ---------------------------------------------------------------------------------------------
# Fault injection
# ---------------------------------------------------------------------------------------------
# Doctrine: a check is not validated because it passes; it is validated when a known-bad specimen
# makes it fail -- FOR THE RIGHT REASON. Each specimen below corrupts a copy of the REAL file and
# requires the REAL analysis to convict, then asserts the conviction NAMES the injected defect and
# that no OTHER check fired. A bare did-it-go-red assertion is not enough: a regex that silently
# stopped matching would convict every axiom at once and sail through it (that failure mode is not
# hypothetical here -- the register gate shipped it, and its tell was that seven rows failed at
# once). Naming the injected constant is what distinguishes a working gate from an indiscriminate one.

def _inject_unwitness(bridge_src, name):
    """Rename one registry KEY so its axiom loses its accounting. Targets the `(`name,` entry
    position specifically, so it cannot collide with the same name inside a witness term."""
    out, n = re.subn(r'(\(\s*`)' + re.escape(name) + r'(\s*,)', r'\1' + name + '__INJECTED\\2',
                     bridge_src, count=1)
    return out if n == 1 else None

def _inject_stale_excuse(bridge_src, name):
    """Add an excuse for an axiom the ledger does not carry."""
    out, n = re.subn(r'(def witnessGap\s*:\s*List \(Name × String\)\s*:=\s*\[)',
                     r'\1(`' + name + ', "injected by --selftest"),', bridge_src, count=1)
    return out if n == 1 else None

def selftest(ledger_src, bridge_src, mine, theirs):
    print("\n=== SELFTEST (fault injection against the live files) ===")
    ok, ran = True, 0
    def check(label, cond, detail=""):
        nonlocal ok, ran
        ran += 1
        print(f"  [{'ok' if cond else 'BROKEN'}] {label}" + (f"  {detail}" if detail and not cond else ""))
        ok &= bool(cond)

    # Control FIRST. If the real inputs are already red, every injection below would "fire"
    # without proving anything -- the specimen must be the only cause of the conviction.
    base_fails, base = analyze(ledger_src, bridge_src, mine, theirs)
    # If the SUBJECT is already red, an injection going red proves nothing -- and reporting the
    # control as BROKEN would blame the gate for a defect that is really in the ledger. Say so and
    # stand down; `main` still fails on the real conviction, so nothing is swallowed. Distinguishing
    # "the test cannot run" from "the test failed" is the same distinction --mutate draws with STALE.
    if base is None:
        print("  SELFTEST UNAVAILABLE — the live ledger does not parse; the conviction below is the")
        print("  verdict. Injections cannot be validated against an unreadable subject.")
        return 0
    if base_fails:
        print(f"  SELFTEST SKIPPED — the live inputs are ALREADY red ({len(base_fails)} conviction(s)),")
        print("  so a specimen going red would demonstrate nothing. Fix the failure below, then re-run.")
        return 0
    check("control: unmodified real inputs are silent", not base_fails, f"got {base_fails}")

    def fires(f, cls):
        return [x for x in f if x.startswith(cls)]

    # 1. toolchain skew: the 33-day defect, replayed.
    f, _ = analyze(ledger_src, bridge_src, mine, "v0.0.0-injected")
    check("skew: witness on a different Lean is convicted",
          len(fires(f, "TOOLCHAIN")) == 1 and len(f) == 1, f"got {f}")

    # 2. unwitnessed axiom: perturb ONE registry key in the real bridge text. This exercises the
    #    regex parser, the set arithmetic and the message together -- and the conviction must name
    #    the axiom that was actually broken, not merely count something.
    victim = sorted((base["trusted"] & base["registry"])
                    - base["standard"] - base["mapped"] - base["gap"] - base["bridge"])
    if not victim:
        check("unwitnessed: a registry-only trusted axiom exists to break", False,
              "no axiom is accounted for by the registry alone")
    else:
        v = victim[0]
        bad = _inject_unwitness(bridge_src, v)
        if bad is None or bad == bridge_src:
            check(f"unwitnessed: injection actually altered the source ({v})", False,
                  "the entry pattern did not match -- specimen is inert")
        else:
            f, _ = analyze(ledger_src, bad, mine, theirs)
            u = fires(f, "UNACCOUNTED")
            check(f"unwitnessed: de-registered {v} is convicted",
                  len(u) == 1 and len(f) == 1, f"got {f}")
            check("unwitnessed: the conviction NAMES the axiom broken (not just a count)",
                  bool(u) and v in u[0], f"got {u}")

    # 3. stale excuse: an excuse that outlives its axiom.
    ghost = "MachLib.Real.__selftest_ghost_axiom"
    bad = _inject_stale_excuse(bridge_src, ghost)
    if bad is None or bad == bridge_src:
        check("stale: injection actually altered witnessGap", False, "pattern did not match")
    else:
        f, _ = analyze(ledger_src, bad, mine, theirs)
        s = fires(f, "STALE EXCUSE")
        check("stale: an excuse for a non-ledger axiom is convicted",
              len(s) == 1 and len(f) == 1, f"got {f}")
        check("stale: the conviction names the ghost", bool(s) and ghost in s[0], f"got {s}")

    # 4. the parse itself must fail CLOSED. If the ledger stops being parseable the gate must
    #    convict, never report a clean footprint of zero axioms.
    f, st = analyze(ledger_src.replace("def trustedFootprint", "def somethingElse"),
                    bridge_src, mine, theirs)
    check("unparseable ledger fails closed (not a silent empty footprint)", st is None and bool(f))

    # COUNT the specimens that actually ran; never assert a literal. A hardcoded tally drifts
    # the moment a branch is added and then misreports how much was checked -- and a gate that
    # misstates its own coverage is the thing this file exists to prevent.
    print(f"  SELFTEST {'PASS' if ok else 'FAIL'} ({ran} specimens, "
          f"4 perturbations of the live inputs)")
    return 0 if ok else 1


# ---------------------------------------------------------------------------------------------
# Mutation testing -- validates the SELFTEST, which fault injection does not.
# ---------------------------------------------------------------------------------------------
# Injection proves the gate convicts a bad specimen. It says nothing about whether the selftest
# would notice if the GATE ITSELF were broken. So: break the gate five ways and require --selftest
# to go red for each. Run with `--mutate`. Kept in-tree rather than as a one-off script, because
# DOCTRINE.md cites this table and a cited result nobody can re-run is a literal, not evidence.

MUTANTS = {
    "toolchain check removed":   ("if mine != theirs:", "if False:"),
    "unaccounted check removed": ("if unacct:", "if False:"),
    "stale check removed":       ("if stale:", "if False:"),
    "ledger parse fails OPEN":   ('return ["PARSE — cannot parse AxiomLedger.trustedFootprint"], None',
                                  "trusted = set()"),
    "conviction stops naming":   ("{unacct[:8]}{' …' if len(unacct) > 8 else ''}", "<redacted>"),
}

def mutate():
    import subprocess
    me = pathlib.Path(__file__).resolve()
    src = me.read_text()
    # Mutate ONLY the code above this table. Every anchor string necessarily also appears in the
    # table itself, so a whole-file `replace(a, b, 1)` is correct only by the accident that
    # `analyze` happens to sit earlier in the file. Reorder the file and all five mutants would
    # patch the dict literal, leave the gate intact, and report MISSED together. Splitting here
    # removes the coincidence -- and makes a drifted anchor report STALE instead of MISSED,
    # which is the difference between "the test is broken" and "the gate is broken".
    head, sep, tail = src.partition("MUTANTS = {")
    # The mutant MUST live beside this file: `HERE` is derived from `__file__`, so a copy written
    # to a temp dir finds no witness project and exits UNAVAILABLE before reaching any check --
    # which reads as "selftest missed the mutant" for every mutant at once. First run of this test
    # scored 0/5 for exactly that reason. All-fail-together is a harness smell, not a result.
    mut = me.parent / "_mutant_selftest_tmp.py"
    print("=== MUTATION TEST (break the gate, require --selftest to notice) ===")
    ok = True
    try:
        for label, (a, b) in MUTANTS.items():
            if a not in head:
                print(f"  [STALE] {label} — anchor no longer in the gate's code; mutant is inert")
                ok = False; continue
            mut.write_text(head.replace(a, b, 1) + sep + tail)
            r = subprocess.run([sys.executable, str(mut), "--selftest"],
                               capture_output=True, text=True)
            caught = r.returncode != 0 and "BROKEN" in r.stdout
            ok &= caught
            hit = next((l.strip() for l in r.stdout.splitlines() if "BROKEN" in l), "")
            print(f"  [{'caught' if caught else 'MISSED'}] {label}")
            if hit: print(f"            by: {hit[:96]}")
    finally:
        mut.unlink(missing_ok=True)
    print(f"  MUTATION {'PASS' if ok else 'FAIL'} ({len(MUTANTS)} mutants)")
    return 0 if ok else 1


def main():
    if len(sys.argv) > 1 and sys.argv[1] == "--mutate":
        return mutate()
    if not BRIDGE.exists():
        print(f"SOUNDNESS-WITNESS UNAVAILABLE — no witness project at {WITNESS}")
        return 2
    ledger_src = (HERE / "AxiomLedger.lean").read_text()
    bridge_src = BRIDGE.read_text()
    mine = (HERE / "lean-toolchain").read_text().strip()
    theirs_p = WITNESS / "lean-toolchain"
    theirs = theirs_p.read_text().strip() if theirs_p.exists() else "(none)"

    fails, st = analyze(ledger_src, bridge_src, mine, theirs)
    if st is None:
        print("SOUNDNESS-WITNESS FAIL")
        for f in fails: print(f"  - {f}")
        return 1

    if st["extra_witnesses"]:
        print(f"  (also holds {len(st['extra_witnesses'])} witness(es) for axioms outside the "
              f"trusted footprint: {st['extra_witnesses']}) — not a defect")
    t = st["trusted"]
    print(f"  trusted footprint (live ledger) : {len(t)}")
    print(f"  witnessed against Mathlib       : {len(t & st['registry'])}")
    print(f"  standard / mapped / tracked gap : {len(t & st['standard'])} / {len(t & st['mapped'])} / {len(t & st['gap'])}")
    print(f"  float-bridge (NOT R-modelable)  : {len(t & st['bridge'])}")
    print(f"  UNMODELED (no witness at all)   : {len(st['unacct'])}")
    print(f"  MachLib toolchain / witness     : {st['mine']} / {st['theirs']}")

    if len(sys.argv) > 1 and sys.argv[1] == "--selftest":
        if selftest(ledger_src, bridge_src, mine, theirs) != 0:
            return 1
    if fails:
        print("\nSOUNDNESS-WITNESS FAIL")
        for f in fails: print(f"  - {f}")
        return 1
    print(f"\nSOUNDNESS-WITNESS OK — {len(t)} trusted axioms, all accounted, toolchains agree.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
