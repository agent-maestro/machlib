#!/usr/bin/env python3
"""MachSig trust-footprint ratchet — gate 14.

FAILS when a theorem's axiom footprint GROWS while its statement is unchanged.

That is a real regression class and this corpus has 59 live instances of the underlying
phenomenon (same claim, different footprint), so the gate watches something that actually varies.
It is deliberately NOT the roadmap's canonicalisation-drift gate: that one cannot fire here at all,
because no canonical view exists (docs/machsig/CANONICALIZER_BRIDGE.md), and a gate that can never
fire reads as "checked and clean".

The ratchet turns ONE WAY. A footprint may shrink freely; growth on an unchanged statement must be
accepted deliberately via --update, exactly like witness_baseline.json and hypothesis_baseline.json.

  statement UNCHANGED, axioms GREW      -> FAIL (the same claim now costs more trust)
  statement UNCHANGED, axioms shrank    -> PASS, and the baseline is stale (re-run --update)
  statement CHANGED                     -> INFO: a different claim, not a trust regression
  new / removed theorem                 -> INFO

Absent baseline => UNAVAILABLE (exit 2), never a silent pass.
"""
import json, sys, pathlib, hashlib

FOUND = pathlib.Path(__file__).resolve().parent.parent.parent
BASE = FOUND / "tools" / "machsig" / "trust_baseline.json"
SIGS = FOUND / "artifacts" / "machsig_signatures.jsonl"


def current():
    if not SIGS.exists():
        return None
    out = {}
    for ln in SIGS.read_text().split("\n"):
        if not ln.strip():
            continue
        j = json.loads(ln)
        if j["kind"] != "theorem":
            continue          # StatementDigest is meaningless for non-theorems
        # AX lives in TrustSig from MachSig/v0.2 (it answers "what does this rely upon", not
        # "how is it proved"). Fall back to ProofSig so older signature sets still parse.
        ax = None
        for p in j.get("TrustSig", j["ProofSig"]).split("-"):
            if p.startswith("AX"):
                try: ax = int(p[2:])
                except ValueError: ax = None
        if ax is not None:
            out[j["object"]] = {"d": j["StatementDigest"][:32], "ax": ax}
    return out


def main(argv):
    cur = current()
    if cur is None:
        # The signature set is a generated artifact (gitignored), so a fresh clone has none.
        # UNAVAILABLE with exit 2, never a silent pass -- and name the WHOLE chain, since the
        # signatures depend on a Lean extraction step that is easy to omit.
        print("MACHSIG-TRUST UNAVAILABLE — no signature set. Regenerate with:\n"
              "    lake env lean tools/machsig/extract_statement.lean > artifacts/machsig_stmt_raw.tsv\n"
              "    lake env lean tools/machsig/extract.lean            > artifacts/machsig_raw.tsv\n"
              "    python3 tools/machsig/census.py && python3 tools/machsig/sig.py sigs")
        return 2
    if "--update" in argv:
        BASE.write_text(json.dumps(cur, sort_keys=True, indent=0))
        print(f"MACHSIG-TRUST baseline written: {len(cur)} theorems")
        return 0
    if "--selftest" in argv:
        # DOCTRINE: no green gate without a demonstrated red path. A predicate check is a unit
        # test; it is not evidence this gate CONVICTS. So the selftest performs a real FAULT
        # INJECTION -- it perturbs a copy of the live baseline, runs the gate's actual comparison
        # over the real signature set, and requires a red result.
        import copy, tempfile, os
        live = current()
        if not BASE.exists() or not live:
            print("SELFTEST UNAVAILABLE — needs a baseline and a signature set"); return 2
        base = json.loads(BASE.read_text())
        ok = True

        def compare(b, c):
            return [k for k in c if k in b and c[k]["d"] == b[k]["d"] and c[k]["ax"] > b[k]["ax"]]

        print("=== SELFTEST (fault injection against the REAL signature set) ===")
        # 1. control: unperturbed baseline must be SILENT
        quiet = compare(base, live)
        print(f"  [{'ok' if not quiet else 'BROKEN'}] control: unmodified baseline stays green")
        ok &= not quiet
        # 2. FIRING: lower a real theorem's recorded footprint -> the live corpus 'grew'
        victims = [k for k in sorted(base) if base[k]["ax"] > 3][:2]
        inj = copy.deepcopy(base)
        for k in victims:
            inj[k]["ax"] -= 3
        fired = compare(inj, live)
        hit = all(v in fired for v in victims)
        print(f"  [{'ok' if hit else 'BROKEN'}] INJECTED footprint growth on {len(victims)} real "
              f"theorem(s) makes the gate RED ({len(fired)} convicted)")
        ok &= hit
        # 3. control: a changed statement must NOT count as a trust regression
        inj2 = copy.deepcopy(base)
        for k in victims:
            inj2[k]["d"] = "0" * 32
            inj2[k]["ax"] -= 3
        restated = compare(inj2, live)
        clean = not any(v in restated for v in victims)
        print(f"  [{'ok' if clean else 'BROKEN'}] control: same growth under a CHANGED statement "
              f"is not convicted")
        ok &= clean
        print(f"  SELFTEST {'PASS' if ok else 'FAIL'} — 1 injected red path, 2 controls")
        if not ok:
            return 1

    if not BASE.exists():
        print("MACHSIG-TRUST UNAVAILABLE — no baseline; run with --update to establish one")
        return 2
    base = json.loads(BASE.read_text())
    grew, shrank, restated, new, gone = [], [], [], [], []
    for k, v in cur.items():
        if k not in base:
            new.append(k); continue
        b = base[k]
        if b["d"] != v["d"]:
            restated.append(k)
        elif v["ax"] > b["ax"]:
            grew.append((k, b["ax"], v["ax"]))
        elif v["ax"] < b["ax"]:
            shrank.append((k, b["ax"], v["ax"]))
    gone = [k for k in base if k not in cur]
    print(f"  theorems compared : {len(cur)}")
    print(f"  statement restated: {len(restated)}   new: {len(new)}   removed: {len(gone)}")
    print(f"  footprint shrank  : {len(shrank)}")
    print(f"  footprint GREW    : {len(grew)}")
    if grew:
        print("\nMACHSIG-TRUST FAIL — same statement, larger axiom footprint")
        for k, a, b_ in sorted(grew, key=lambda t: -(t[2] - t[1]))[:12]:
            print(f"  - {k}  {a} -> {b_}")
        return 1
    print("\nMACHSIG-TRUST OK — no theorem acquired axioms without its statement changing.")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
