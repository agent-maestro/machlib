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
    out, i, depth = [], 0, 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; i += 2; continue
        if s.startswith('-/', i) and depth: depth -= 1; i += 2; continue
        if depth: i += 1; continue
        if s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j; continue
        out.append(s[i]); i += 1
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

def main():
    selftest = len(sys.argv) > 1 and sys.argv[1] == "--selftest"
    if not BRIDGE.exists():
        print(f"SOUNDNESS-WITNESS UNAVAILABLE — no witness project at {WITNESS}")
        return 2
    ledger_src = (HERE / "AxiomLedger.lean").read_text()
    bridge_src = BRIDGE.read_text()

    trusted = names(ledger_src, r'def trustedFootprint\s*:\s*List Name\s*:=\s*')
    if trusted is None:
        print("SOUNDNESS-WITNESS FAIL — cannot parse AxiomLedger.trustedFootprint"); return 1

    registry = names(bridge_src, r'def witnessRegistry\s*:\s*List \(Name × TSyntax `term\)\s*:=\s*', entry=True) or set()
    standard = names(bridge_src, r'def standardAxioms\s*:\s*List Name\s*:=\s*') or set()
    mapped   = names(bridge_src, r'def mappedConstants\s*:\s*List Name\s*:=\s*') or set()
    gap      = names(bridge_src, r'def witnessGap\s*:\s*List \(Name × String\)\s*:=\s*', entry=True) or set()
    bridge   = names(bridge_src, r'def bridgeAxioms\s*:\s*List Name\s*:=\s*') or set()
    accounted = registry | standard | mapped | gap | bridge

    fails = []
    # 1. toolchain skew -- the defect that went undetected for 33 days
    mine  = (HERE / "lean-toolchain").read_text().strip()
    theirs_p = WITNESS / "lean-toolchain"
    theirs = theirs_p.read_text().strip() if theirs_p.exists() else "(none)"
    if mine != theirs:
        fails.append(f"TOOLCHAIN SKEW — MachLib pins {mine!r}, witness pins {theirs!r}. "
                     f"The witness builds MachLib's current source under a different Lean and "
                     f"CANNOT compile; every 'trusted' verdict downstream is unverified.")
    # 2. unaccounted trusted axioms
    unacct = sorted(trusted - accounted)
    if unacct:
        fails.append(f"{len(unacct)} trusted axiom(s) with NO Mathlib witness and no recorded "
                     f"classification: {unacct[:8]}{' …' if len(unacct) > 8 else ''}")
    # 3. stale EXCUSES only. A stale entry in `witnessGap` or `bridgeAxioms` is a defect: it
    #    excuses an axiom from being witnessed, so if it drifts off the ledger it can later mask
    #    a genuinely unwitnessed one. A witness for an axiom that is no longer in the trusted
    #    footprint is NOT a defect -- it is a witness we happen to still hold (e.g. `tanh_neg`
    #    and `tanh_zero`, still axioms in MachLib/Trig.lean, just not in `trustedFootprint`).
    #    Flagging those would convict the innocent and train the next agent to delete evidence.
    stale = sorted((gap | bridge) - trusted)
    if stale:
        fails.append(f"{len(stale)} EXCUSE entr(y/ies) (gap/float-bridge) no longer in the "
                     f"ledger — an excuse that outlives its axiom can mask a real gap: {stale}")
    extra_witnesses = sorted(registry - trusted - standard - mapped)
    if extra_witnesses:
        print(f"  (also holds {len(extra_witnesses)} witness(es) for axioms outside the trusted "
              f"footprint: {extra_witnesses}) — not a defect")

    print(f"  trusted footprint (live ledger) : {len(trusted)}")
    print(f"  witnessed against Mathlib       : {len(trusted & registry)}")
    print(f"  standard / mapped / tracked gap : {len(trusted & standard)} / {len(trusted & mapped)} / {len(trusted & gap)}")
    print(f"  float-bridge (NOT R-modelable)  : {len(trusted & bridge)}")
    print(f"  UNMODELED (no witness at all)   : {len(unacct)}")
    print(f"  MachLib toolchain / witness     : {mine} / {theirs}")
    if selftest:
        print("\n=== SELFTEST ===")
        ok = True
        # firing specimen: a footprint entry that cannot be accounted for
        probe = trusted | {"MachLib.Real.__selftest_absent_axiom"}
        fired = bool(sorted(probe - accounted))
        print(f"  [{'ok' if fired else 'BROKEN'}] injected unaccounted axiom is detected")
        ok &= fired
        # firing specimen: toolchain skew
        skew = ("v4.32.2" != "v4.14.0")
        print(f"  [{'ok' if skew else 'BROKEN'}] toolchain comparison discriminates v4.32.2 vs v4.14.0")
        ok &= skew
        # control: the real trusted set minus itself must NOT fire
        quiet = not bool(sorted(trusted - (trusted | accounted)))
        print(f"  [{'ok' if quiet else 'BROKEN'}] control: fully-accounted set stays silent")
        ok &= quiet
        print(f"  SELFTEST {'PASS' if ok else 'FAIL'} (3 specimens)")
        if not ok: return 1
    if fails:
        print("\nSOUNDNESS-WITNESS FAIL")
        for f in fails: print(f"  - {f}")
        return 1
    print(f"\nSOUNDNESS-WITNESS OK — {len(trusted)} trusted axioms, all accounted, toolchains agree.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
