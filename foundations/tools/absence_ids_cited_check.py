#!/usr/bin/env python3
"""A source file that cites an absence-registry id must cite one that EXISTS.

WHY THIS EXISTS (found 2026-09-11). `MachLib/GermDerivFbasis.lean` closed its frontier discussion
with:

    Registered in `tools/absence_claims.json` (`routea-separation-absent`).

There is no such entry. Zero occurrences in the registry.

That is worse than an unregistered claim, and the registry's own docstring says why: an absence claim
*"decays silently — someone adds the thing, and the sentence saying it is missing keeps reading as
true."* The registry exists to attach a falsifier to each such sentence. A sentence that ADVERTISES
a falsifier it does not have gets none of that protection while looking like it has all of it — and
in this instance the claim had in fact decayed: the step it called absent (`log_separation`) was
proved, and nothing fired.

`absence_audit.py` checks that every REGISTERED claim still holds. Nothing checked that a CITED
registration exists. That is the same perimeter error this corpus keeps finding in new costumes —
an instrument correct over its own population, pointed at the wrong one.

WHAT IT CHECKS. Every `` `id-like-this` `` appearing next to a mention of `absence_claims.json`, and
every id cited in prose that matches the registry's own naming shape, must be a key in the registry.

SELF-TEST (`--self-test`): a fabricated citation must FIRE and the unmodified corpus must stay
SILENT. An instrument shown capable of one verdict is not evidence for the other.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
FOUND = HERE.parent
REGISTRY = HERE / "absence_claims.json"

#: ids are lowercase-with-hyphens; require at least two hyphens so ordinary hyphenated prose
#: ("pole-conditioned", "two-sided") cannot be mistaken for a citation.
ID_SHAPE = re.compile(r"`([a-z][a-z0-9]*(?:-[a-z0-9]+){2,})`")
#: only look at lines that actually invoke the registry, so an unrelated backticked slug is not
#: dragged in. This is deliberately narrow: a false alarm here would train people to ignore it.
CONTEXT = re.compile(r"absence[_ ]claims\.json|absence registry|absence_claims")
#: A citation that SAYS the id is not registered is not a false claim -- it is the correction. The
#: disclosure-names gate needs the same escape for the same reason: an erratum has to be able to name
#: the thing it is erratum-ing. Requiring the disclaimer in the same breath is what stops the escape
#: from becoming a way to keep citing a dead id.
DISCLAIMED = re.compile(r"never registered|no registry entry|not in absence_claims|"
                        r"does not exist|was never in the registry", re.I)


def registry_ids(path: Path = REGISTRY) -> set[str]:
    try:
        d = json.loads(path.read_text(encoding="utf-8"))
    except OSError:
        return set()
    claims = d.get("claims", d) if isinstance(d, dict) else d
    return {c.get("id") for c in claims if isinstance(c, dict) and c.get("id")}


def cited(root: Path = FOUND) -> list[tuple[str, int, str]]:
    """(file, line, id) for every registry id cited in a source or doc file."""
    out: list[tuple[str, int, str]] = []
    files = list((root / "MachLib").rglob("*.lean")) + list((root / "docs").rglob("*.md"))
    for f in files:
        try:
            lines = f.read_text(encoding="utf-8", errors="ignore").splitlines()
        except OSError:
            continue
        for i, line in enumerate(lines, 1):
            # the citation and the registry mention may sit on adjacent lines
            window = " ".join(lines[max(0, i - 3):i + 1])
            if not CONTEXT.search(window):
                continue
            if DISCLAIMED.search(window):
                continue          # the sentence is correcting the citation, not making it
            for m in ID_SHAPE.finditer(line):
                out.append((str(f.relative_to(root)), i, m.group(1)))
    return out


def scan(ids: set[str], cites: list[tuple[str, int, str]], emit=print) -> int:
    if not ids:
        emit("UNAVAILABLE — the absence registry could not be read; this is not a pass")
        return 2
    bad = [(f, n, i) for f, n, i in cites if i not in ids]
    emit("=== absence ids cited vs registered ===")
    emit(f"  {len(ids)} registered, {len(cites)} citation(s) found")
    if bad:
        emit(f"ABSENCE-IDS DRIFT — {len(bad)} citation(s) name no registry entry:")
        for f, n, i in bad:
            emit(f"  {f}:{n} cites `{i}` — not in absence_claims.json")
        emit("  A sentence advertising a falsifier it does not have gets none of the registry's "
             "decay protection\n  while looking like it has all of it. Register it, or stop "
             "claiming it is registered.")
        return 1
    emit("ABSENCE-IDS OK — every cited id exists in the registry")
    return 0


def self_test() -> int:
    ids = registry_ids()
    cites = cited()
    ok = True
    if scan(ids, cites, lambda *_: None) != 0:
        print("SELFTEST FAIL — the real corpus does not pass; fix that before reading a self-test")
        return 1
    print("  SILENT   on the unmodified corpus")
    fake = cites + [("MachLib/Fake.lean", 1, "totally-invented-claim-id")]
    if scan(ids, fake, lambda *_: None) != 1:
        print("SELFTEST FAIL — a fabricated citation did not fire")
        ok = False
    else:
        print("  FIRES    on a fabricated citation")
    if scan(set(), cites, lambda *_: None) != 2:
        print("SELFTEST FAIL — an unreadable registry did not report UNAVAILABLE")
        ok = False
    else:
        print("  UNAVAILABLE on an unreadable registry (not a pass)")
    print("SELFTEST OK" if ok else "SELFTEST FAIL")
    return 0 if ok else 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)
    if not REGISTRY.exists():
        print(f"UNAVAILABLE — {REGISTRY} not found; this is not a pass")
        return 2
    if args.self_test:
        return self_test()
    return scan(registry_ids(), cited())


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
