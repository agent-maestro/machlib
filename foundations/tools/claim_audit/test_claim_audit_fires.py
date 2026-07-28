"""CONDUCTIVITY SPECIMEN for the claim auditor -- the registry's last blank.

The standard this session settled on: a specimen must demonstrate conductivity from INJECTION to
EXIT CODE, not merely that some inner function can detect a fault. Three gate defects taught it:

  ROM gate                   fired INVERTED (FAIL with zero mismatches)
  sorry-audit canary         never fired (landed outside the filtered namespace)
  assert_normalised_cleanly  never CALLED (two docs named it "the gate"; nothing invoked it)

So this drives `claim_audit.py` as a SUBPROCESS and requires a non-zero exit, for each of the two
drift classes it claims to catch. "Inherited green" is exactly the posture that let the third one
sit unwired under passing CI.

NOTE ON THE EXISTING `--self-test`. The auditor already ships one, and it is good, but it is
LINK-5-ONLY: it compiles a `by sorry` canary and checks that the string `sorryAx` appears in the
`#print axioms` output. That validates the substring detection -- an inner capability -- and never
runs the audit over a registry or reaches an exit code. It would stay green if `audit()` ignored its
findings entirely. This file supplies the missing conductivity.

Run: python3 test_claim_audit_fires.py   (exit 0 = the auditor conducts, both classes)
"""
from __future__ import annotations

import json
import pathlib
import shutil
import subprocess
import sys
import tempfile

HERE = pathlib.Path(__file__).resolve().parent
FOUNDATIONS = HERE.parents[1]
AUDIT = HERE / "claim_audit.py"
CLAIMS = HERE / "claims.json"


def _reachability_witness(name: str, ok: bool, detail: str) -> bool:
    """Assert the injected fault is PRESENT AT THE GATE'S INPUT, before reading the gate's verdict.

    Every injection needs one. A malformed injection and a broken gate produce the IDENTICAL
    observation -- "GATE DID NOT FIRE" -- and the malformed injection is the likelier of the two
    when the gate is old and the test is new. Without a witness you cannot tell them apart, and the
    default reading (blame the gate) sends you patching working code.

    This is the mirror of the wrong-reason protocol: that one audits HITS (predicted 9, measured 9 --
    but via the right mechanism?), this one audits MISSES (no fire -- but did the fault arrive?).
    An unaudited positive and an unaudited negative are equally uninformative.
    """
    print(f"    witness: {name:<34} {'REACHED' if ok else '*** FAULT NEVER ARRIVED ***'}  {detail}")
    return ok


def _run(claims_path: pathlib.Path) -> subprocess.CompletedProcess:
    return subprocess.run([sys.executable, str(AUDIT), "--registry", str(claims_path)],
                          cwd=FOUNDATIONS, capture_output=True, text=True, timeout=2400)


def main() -> int:
    fails: list[str] = []
    claims = json.loads(CLAIMS.read_text())
    rows = claims["claims"]

    with tempfile.TemporaryDirectory() as td:
        # ---- 1. baseline: the real registry must PASS -------------------------------------
        r = _run(CLAIMS)
        print(f"1 real registry ({len(rows)} claims)            -> exit {r.returncode}  "
              f"{'ok' if r.returncode == 0 else 'UNEXPECTED'}")
        if r.returncode != 0:
            fails.append("the real registry does not pass; the specimen cannot distinguish anything")

        # ---- 2. AXIOM DRIFT: forbid an axiom the theorem actually uses --------------------
        #     the auditor must notice the headline outrunning its trail.
        # forbid an axiom the theorem PROVABLY uses -- `MachLib.Real` itself is in every
        # footprint. A forbid the theorem does not use would be a no-op and would prove nothing.
        drift = [dict(c) for c in rows]
        target = next(c for c in drift if c.get("forbid_axioms"))
        target["forbid_axioms"] = list(target["forbid_axioms"]) + ["MachLib.Real.lt_total"]
        # WITNESS: the forbidden axiom must actually be in that theorem's footprint, or the
        # injection is a no-op and a non-firing gate would be CORRECT. (My first cut forbade
        # `MachLib.Real.exp`, which this Rolle-based theorem never touches.)
        sys.path.insert(0, str(HERE))
        import claim_audit as _ca  # noqa: E402
        _fp = _ca.axiom_footprint(target["module"], target["theorem"])
        if not _reachability_witness("forbidden axiom is in the footprint",
                                     "MachLib.Real.lt_total" in _fp,
                                     f"(theorem {target['theorem']})"):
            fails.append("axiom-drift injection never reached the gate -- the forbid is a no-op")
        p2 = pathlib.Path(td) / "axiom_drift.json"
        p2.write_text(json.dumps({"claims": drift}))
        r2 = _run(p2)
        print(f"2 AXIOM DRIFT injected ({target['id'][:34]}) -> exit {r2.returncode}  "
              f"{'GATE FIRED' if r2.returncode != 0 else 'GATE DID NOT FIRE'}")
        if r2.returncode == 0:
            fails.append("axiom drift did not fail the audit -- class (A) is not conducted")

        # ---- 3. CLAIM DRIFT: point a claim at text that is not in its source doc ----------
        drift2 = [dict(c) for c in rows]
        t2 = drift2[0]
        # claim_text is a LIST of phrases. Setting it to a bare string makes the auditor iterate
        # over CHARACTERS -- each trivially present -- so the gate correctly passes. The first cut
        # of this specimen did exactly that and I nearly reported the auditor as broken.
        t2["claim_text"] = ["this sentence appears in no document in this repository whatsoever"]
        # WITNESS: claim_text must be a LIST of phrases, and the phrase must genuinely be absent
        # from the source doc. A bare string degrades the auditor into checking single CHARACTERS,
        # every one of which trivially passes -- a malformed injection that reads exactly like a
        # broken gate. That is what the first cut of this file did.
        _src = pathlib.Path(FOUNDATIONS).parent / t2["source_file"]
        _absent = (_src.exists() and t2["claim_text"][0] not in _src.read_text(encoding="utf-8"))
        if not _reachability_witness("claim_text is a list & phrase absent",
                                     isinstance(t2["claim_text"], list) and _absent,
                                     f"({t2['source_file']})"):
            fails.append("claim-drift injection never reached the gate -- phrase present or not a list")
        p3 = pathlib.Path(td) / "claim_drift.json"
        p3.write_text(json.dumps({"claims": drift2}))
        r3 = _run(p3)
        print(f"3 CLAIM DRIFT injected ({t2['id'][:34]}) -> exit {r3.returncode}  "
              f"{'GATE FIRED' if r3.returncode != 0 else 'GATE DID NOT FIRE'}")
        if r3.returncode == 0:
            fails.append("claim drift did not fail the audit -- class (B) is not conducted")

    print()
    if fails:
        print("CLAIM-AUDIT SPECIMEN: FAIL")
        for f in fails:
            print("  -", f)
        return 1
    print("CLAIM-AUDIT SPECIMEN: PASS -- conducts from injection to exit code, both drift classes.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
