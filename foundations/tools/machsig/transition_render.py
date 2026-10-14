#!/usr/bin/env python3
"""Rendering for transition.py: the report, the machine-readable JSON and the review packet.

Pure functions of transition.build()'s output and the evidence files. Determinism rules: every
collection is sorted before it is printed, there is no clock and no path outside the evidence names,
so the same evidence renders byte-identical text.
"""
from __future__ import annotations

import collections
import hashlib
import json
from pathlib import Path

import transition as T

STMT_CUT = 300
KINDS = ("grew", "shrank", "swap", "restated", "redefined", "new", "removed")
SCHEMA = "machsig-transition/v2"     # v2 (2026-10-13): the binding block a REVIEWED stamp is checked against


def _set_id(axs) -> str:
    return hashlib.sha256("\n".join(sorted(axs)).encode()).hexdigest()[:12]


def _stmts(ev: dict) -> tuple[dict, dict]:
    old = json.loads(ev["stmts_old"].read_text()) if "stmts_old" in ev else {}
    new = json.loads(ev["stmts_new"].read_text()) if "stmts_new" in ev else {}
    return old, new


def _history(ev: dict) -> dict:
    """{axiom: [commits]} -- the pickaxe trace of every axiom whose status changed."""
    h = json.loads(ev["history"].read_text()) if "history" in ev else {}
    return h.get("axioms", h)


def _file_history(ev: dict) -> dict:
    h = json.loads(ev["history"].read_text()) if "history" in ev else {}
    return h.get("files", {})


def _redefinition(ev: dict) -> dict | None:
    return json.loads(ev["redefinition"].read_text()) if "redefinition" in ev else None


def _targeted(ev: dict) -> dict | None:
    return json.loads(ev["targeted"].read_text()) if "targeted" in ev else None


def counts(t: dict) -> dict:
    by_kind = collections.Counter(r["kind"] for r in t["rows"])
    by_class = collections.Counter((r["kind"], r.get("trust_class")) for r in t["rows"])
    tiers = collections.Counter((r["old"]["tier"] if r["old"] and r["old"].get("tier") else "-",
                                 r["new"]["tier"] if r["new"] else "-") for r in t["rows"])
    causes = collections.Counter("+".join(r["causes"]) or "none" for r in t["rows"])
    return {"by_kind": dict(sorted(by_kind.items())),
            "by_kind_and_class": {f"{k}|{c}": n for (k, c), n in sorted(by_class.items())},
            "tier_transitions": {f"{a}->{b}": n for (a, b), n in sorted(tiers.items())},
            "by_cause": dict(sorted(causes.items()))}


def stale_set_check(ev_dir: Path) -> dict | None:
    """Optional: the 2026-09-03 local signature set (the one the gate read for forty days) against a
    fresh pre-v0.3 extraction at 23e0d047, compared on every field after normalising v0.1/v0.2."""
    a, b = ev_dir / "stale_local_sigs_20260903.jsonl", ev_dir / "legacy_sigs_23e0d047.jsonl"
    if not (a.is_file() and b.is_file()):
        return None

    def norm(r):
        f = {}
        for lay in ("ProofSig", "TrustSig"):
            for p in r.get(lay, "").split("-"):
                if p:
                    k = p[:2] if p[:2] in ("AX", "PD") else p[:1]
                    f["R" if k == "V" else k] = p[len(k):]
        return (r["StatementDigest"], r["StatementSig"], r["ProofFingerprint64"], r["kind"], r["module"],
                tuple(sorted(f.items())))

    def load(p):
        return {j["object"]: norm(j) for j in (json.loads(x) for x in p.read_text().split("\n") if x.strip())}
    x, y = load(a), load(b)
    return {"objects": [len(x), len(y)], "same_objects": set(x) == set(y),
            "differing": sorted(k for k in set(x) & set(y) if x[k] != y[k])[:20],
            "sha256": {a.name: T.sha256(a), b.name: T.sha256(b)}}


# ── JSON ───────────────────────────────────────────────────────────────────────────────────────────

def as_json(t: dict, manifest: dict, ev: dict) -> str:
    sets = {}
    rows = []
    for r in t["rows"]:
        out = {k: r[k] for k in ("theorem", "kind", "module", "entered", "left", "causes", "redefined") if k in r}
        out["trust_class"] = r.get("trust_class")
        out["group"] = r.get("group")
        for side in ("old", "new"):
            s = r[side]
            if s is None:
                out[side] = None
                continue
            o = {"statement_digest32": s["d"], "ax": s["ax"], "tier": s.get("tier"),
                 "outside_policy": s.get("outside_policy")}
            if s.get("axioms") is not None:
                sid = _set_id(s["axioms"])
                sets[sid] = sorted(s["axioms"])
                o["axiom_set"] = sid
            else:
                o["axiom_set"] = None
            out[side] = o
        rows.append(out)
    doc = {
        "schema": SCHEMA,
        "binding": t["binding"],
        "evidence_sha256": manifest,
        "reconstruction": {"byte_identical": t["recon_identical"], "value_diffs": t["recon_value_diffs"],
                           "stale_local_set": stale_set_check(ev["sigs_old"].parent)},
        "attribution": {"extractor_delta_old_revision": t["extractor_delta_old"],
                        "extractor_delta_new_revision": t["extractor_delta_new"],
                        "baseline_edits_c3046961": t["baseline_edits"]},
        "population": t["population"],
        "axiom_moves": t["axiom_moves"],
        "redefinition": _redefinition(ev),
        "candidate_baseline": t.get("candidate"),
        "legacy_gate_view_c3046961": t.get("legacy_gate_view_c3046961"),
        "certcom_theorems_unwatched": t.get("certcom_theorems_unwatched"),
        "signature_heads": t["heads"],
        "policy_counts": t["policy_counts"],
        "policy_delta": t["policy_delta"],
        "moved_axioms": t["moved_axioms"],
        "axiom_history": _history(ev),
        "sorry": {"now": t["sorry_now"], "allowlist": t["sorry_allowlist"],
                  "only_allowlisted": sorted(t["sorry_now"]) == sorted(t["sorry_allowlist"])},
        "counts": counts(t),
        "trust_classes": dict(T.TRUST_CLASSES),
        # members of a group: rows[] whose "group" is its id
        "groups": [{k: g[k] for k in ("id", "size", "trust_class", "entered", "left")} for g in t["groups"]],
        "targeted_checks": _targeted(ev),
        "axiom_sets": dict(sorted(sets.items())),
        "rows": rows,
    }
    return _dump(doc)


def _dump(doc: dict) -> str:
    """Readable at the top level, one line per entry in the big tables (rows, axiom_sets, groups), so the
    file stays small enough to commit and a diff shows one line per changed theorem."""
    out = ["{"]
    keys = sorted(doc)
    for i, k in enumerate(keys):
        tail = "," if i < len(keys) - 1 else ""
        v = doc[k]
        if k in ("rows", "groups") and isinstance(v, list):
            out.append(f"{json.dumps(k)}: [")
            out += [json.dumps(x, sort_keys=True, separators=(",", ":")) + ("," if j < len(v) - 1 else "")
                    for j, x in enumerate(v)]
            out.append("]" + tail)
        elif k == "axiom_sets":
            out.append(f"{json.dumps(k)}: {{")
            items = sorted(v.items())
            out += [f"{json.dumps(a)}: {json.dumps(b, separators=(',', ':'))}" + ("," if j < len(items) - 1 else "")
                    for j, (a, b) in enumerate(items)]
            out.append("}" + tail)
        else:
            out.append(f"{json.dumps(k)}: {json.dumps(v, sort_keys=True, separators=(',', ':'))}{tail}")
    out.append("}")
    return "\n".join(out) + "\n"


# ── Markdown helpers ───────────────────────────────────────────────────────────────────────────────

def _short(names: list[str], n: int = 4) -> str:
    if not names:
        return "—"
    s = ", ".join(f"`{x}`" for x in names[:n])
    return s + (f" (+{len(names) - n} more)" if len(names) > n else "")


def _cut(s: str | None, n: int = STMT_CUT) -> str:
    if s is None:
        return "(statement unavailable)"
    s = " ".join(s.split())
    return s if len(s) <= n else s[:n] + f" … [{len(s)} chars; full text in the statements evidence]"


def _cls(a: str, t_policy: dict) -> str:
    return T.axiom_class(a, t_policy)


def _policies(ev: dict) -> tuple[dict, dict]:
    return (T.prepare_policy(json.loads(ev["policy_old"].read_text())),
            T.prepare_policy(json.loads(ev["policy_new"].read_text())))


def _ax_label(a: str, side: str, p_old: dict, p_new: dict, moved: dict) -> str:
    c = _cls(a, p_new if side == "new" else p_old)
    extra = ""
    if a in moved["now_theorem"]:
        extra = ", now a THEOREM"
    elif a in moved["now_definition"]:
        extra = ", now a definition"
    elif a in moved["now_absent"]:
        extra = ", now absent"
    elif a in moved["axiom_now_not_then"]:
        extra = ", a NEW axiom"
    return f"`{a}` ({c}{extra})"


def _commits(names: list[str], hist: dict, limit: int = 6) -> list[str]:
    seen = {}
    for n in names:
        for c in hist.get(n, []):
            seen[c["commit"]] = c
    cs = sorted(seen.values(), key=lambda c: (c["date"], c["commit"]))
    return [f"`{c['commit'][:10]}` {c['date']} {c['subject']}" for c in cs[:limit]] + \
        ([f"… and {len(cs) - limit} more"] if len(cs) > limit else [])


def summary_line(t: dict) -> str:
    c = counts(t)["by_kind"]
    return ("transition: " + ", ".join(f"{k} {c.get(k, 0)}" for k in KINDS) +
            f"; extractor-caused {len(set(t['extractor_delta_old']) | set(t['extractor_delta_new']))}; "
            f"reconstruction {'byte-identical' if t['recon_identical'] else 'NOT identical'}")


# ── the report ─────────────────────────────────────────────────────────────────────────────────────

def as_markdown(t: dict, manifest: dict, ev: dict) -> str:
    import transition_report_text as RT
    return RT.report(t, manifest, ev)


def packet(t: dict, manifest: dict, ev: dict) -> str:
    import transition_report_text as RT
    return RT.packet(t, manifest, ev)
