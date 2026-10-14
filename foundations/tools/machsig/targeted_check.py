#!/usr/bin/env python3
"""Targeted checks for the transition classification (the owner's step 6): a seeded random sample
from EVERY class, each re-derived through Lean's own `#print axioms` at both revisions.

    python3 tools/machsig/targeted_check.py --evidence DIR --old-root OLD/foundations \
        --new-root NEW/foundations [--seed 20261013] [--per-class 8]

WHY. The classification is computed from signature sets that extract.lean produced. A check that
reused extract.lean would only re-run the same code. `#print axioms` is what a reader would type: it
goes through Lean's command front end and message formatting, and is parsed back here from text. For
each sampled theorem it must reproduce (a) the old axiom set, (b) the new axiom set, and from those
(c) the same kind and trust class transition.py assigned. Unchanged theorems are sampled too, as a
control: a classifier that called everything "changed" would fail there.

The seed, the buckets, every sampled name and every result are written to targeted.json, which the
report embeds. Rerunning with the same seed and evidence draws the same sample.
"""
from __future__ import annotations

import argparse
import json
import random
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import probe  # noqa: E402
import transition as T  # noqa: E402


def buckets(t: dict, old_w: dict, new_w: dict) -> dict:
    b: dict[str, list[str]] = {}
    for r in t["rows"]:
        b.setdefault(f"{r['kind']}|{r.get('trust_class')}", []).append(r["theorem"])
    changed = {r["theorem"] for r in t["rows"]}
    b["unchanged|control"] = sorted(k for k in set(old_w) & set(new_w) if k not in changed)
    out = {k: sorted(v) for k, v in sorted(b.items())}
    # Not a class but a stratum: every change the discharge mechanism does NOT explain is checked, all of
    # them, because those are the ones a person has to read.
    out["stratum:not-explained-by-discharge"] = sorted(r["theorem"] for r in t["rows"]
                                                       if r.get("explained_by_discharge") is False)
    return out


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--evidence", required=True, type=Path)
    ap.add_argument("--old-root", required=True, type=Path)
    ap.add_argument("--new-root", required=True, type=Path)
    ap.add_argument("--seed", type=int, default=20261013)
    ap.add_argument("--per-class", type=int, default=8)
    ap.add_argument("--full", action="store_true",
                    help="also run #print axioms on EVERY watched theorem at both revisions (~1-2 min)")
    a = ap.parse_args(argv)
    ev = {k: a.evidence / v for k, v in T.EVIDENCE.items() if (a.evidence / v).is_file() and k != "targeted"}
    t = T.build(ev)
    _, all_old = T.load_sigset(ev["sigs_old"])
    _, all_new = T.load_sigset(ev["sigs_new"])
    old_w, new_w = T.watched(all_old), T.watched(all_new)
    p_old = T.prepare_policy(json.loads(ev["policy_old"].read_text()))
    p_new = T.prepare_policy(json.loads(ev["policy_new"].read_text()))
    rng = random.Random(a.seed)
    bk = buckets(t, old_w, new_w)
    sample = {k: (v if len(v) <= a.per_class or k.startswith("stratum:") else sorted(rng.sample(v, a.per_class)))
              for k, v in bk.items()}
    expected = {r["theorem"]: f"{r['kind']}|{r.get('trust_class')}" for r in t["rows"]}
    names = sorted({n for v in sample.values() for n in v})
    need_old = [n for n in names if n in old_w]
    need_new = [n for n in names if n in new_w]
    pa_old = probe.print_axioms(a.old_root, need_old)
    pa_new = probe.print_axioms(a.new_root, need_new)
    rows = {r["theorem"]: r for r in t["rows"]}
    results = []
    for bucket, ns in sample.items():
        for n in ns:
            o_sig = sorted(old_w[n]["axioms"]) if n in old_w else None
            n_sig = sorted(new_w[n]["axioms"]) if n in new_w else None
            o_pa, n_pa = pa_old.get(n), pa_new.get(n)
            # recompute the classification from #print axioms alone
            old = {"d": old_w[n]["d"], "ax": len(o_pa), "axioms": o_pa} if o_pa is not None else None
            new = {"d": new_w[n]["d"], "ax": len(n_pa), "axioms": n_pa} if n_pa is not None else None
            kind = T.kind_of(old, new)
            if old is not None and new is not None:
                cls = T.trust_class(sorted(set(n_pa) - set(o_pa)), sorted(set(o_pa) - set(n_pa)), p_old, p_new)
            elif new is not None:
                cls = "new:" + T.tier(n_pa, p_new)[0]
            else:
                cls = "removed:" + T.tier(o_pa, p_old)[0]
            got = f"{kind}|{cls}" if kind != "unchanged" else "unchanged|control"
            want = expected.get(n, "unchanged|control")
            ok = (o_pa == o_sig) and (n_pa == n_sig) and got == want
            results.append({"theorem": n, "bucket": bucket, "expected": want, "old_set_matches": o_pa == o_sig,
                            "new_set_matches": n_pa == n_sig, "reclassified_as": got, "agrees": ok,
                            "old_ax": None if o_pa is None else len(o_pa),
                            "new_ax": None if n_pa is None else len(n_pa)})
    doc = {"seed": a.seed, "per_class": a.per_class, "method": "`#print axioms` via `lake env lean` at each "
           "revision's built tree, parsed from text; class recomputed with transition.kind_of/trust_class",
           "bucket_sizes": {k: len(v) for k, v in bk.items()}, "sample": sample, "results": results,
           "summary": {"checked": len(results), "agree": sum(r["agrees"] for r in results),
                       "disagree": [r["theorem"] for r in results if not r["agrees"]]}}
    if a.full:
        # Beyond the sample: every axiom set both signature sets hold, re-derived through #print axioms.
        full = {}
        for side, root, w in (("old", a.old_root, old_w), ("new", a.new_root, new_w)):
            pa = probe.print_axioms(root, sorted(w))
            bad = sorted(k for k in w if pa.get(k) != sorted(w[k]["axioms"]))
            full[side] = {"theorems": len(w), "match": len(w) - len(bad), "mismatch": bad[:50]}
        doc["full_sweep"] = full
        print(f"full sweep: old {full['old']['match']}/{full['old']['theorems']}, "
              f"new {full['new']['match']}/{full['new']['theorems']} axiom sets reproduced by #print axioms")
    (a.evidence / T.EVIDENCE["targeted"]).write_text(json.dumps(doc, sort_keys=True, indent=1) + "\n")
    s = doc["summary"]
    print(f"targeted: {s['checked']} theorems over {len(sample)} classes (seed {a.seed}); "
          f"agree {s['agree']}, disagree {len(s['disagree'])}")
    full_bad = any(v["mismatch"] for v in doc.get("full_sweep", {}).values())
    return 0 if not s["disagree"] and not full_bad else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
