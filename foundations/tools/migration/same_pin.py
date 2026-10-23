"""SAME-PIN RE-CAPTURE: the library moved and the pin did not -- attribute every difference, then seal.

`BUMP_PLAN.md` Amendment 7 (owner's ruling, 2026-10-22). `checkpoint.py --compare-to` was built for
BUMP captures: same library, new pin, so any difference belongs to the toolchain and must be ABSENT.
A same-pin re-capture is the opposite case: same pin, new library, so difference is expected and must
be ATTRIBUTED. Measuring one against the other's baseline convicts months of proof work as toolchain
drift, which is exactly what the first `v4.32.2-r2` attempt did (`captures/halted/`).

This mode compares against the NEWEST SEALED capture ON THE SAME PIN -- chosen here, never by the
operator -- and seals only if the attribution holds mechanically:

  1. IDENTITY. `lean-toolchain`, `lake-manifest.json` and the Lean4Lean commit are identical between the
     two captures. A base that predates this mode has no identity record, so it is DERIVED from git at
     the commit that sealed it, and refused if those files moved between its capture and its seal.
     One asymmetry is allowed, and it is named in the record: a base whose criterion 7 was a CITED VOID
     has no Lean4Lean commit to match, so the instrument's ARRIVAL (criterion 7 exit 0 now) is recorded.
  2. ZERO THEOREMS LOST. Every headline the base captured still has a footprint.
  3. EVERY REMOVED AXIOM ATTRIBUTED: to the one commit that removed its declaration, and to what the
     kernel says the name is now -- a theorem or definition (CONVERSION) or nothing (RETIRED from the
     trust base). Still an axiom, or no single removing commit, refuses the seal.
  4. EVERY DERIVATION ACCOUNTED FOR. Each `derivableAxioms` entry of the base is either no longer pinned
     (and so attributed by 3) or recorded in `subTheoryPrimitives` with the SAME derivation.
  5. NEW AXIOMS STAY TRUSTED. A changed footprint's added axioms, and a gained headline's whole
     footprint, lie inside `trustedFootprint`.

Every list read from `AxiomLedger.lean` is bracket-parsed AND cross-derived against the count the Lean
side reported for the same capture. Disagreement is an instrument failure, never a finding.

The library measured must be a COMMIT: attribution is by commit, so a dirty tree is refused.

    python3 tools/migration/checkpoint.py --label v4.32.2-r2 --same-pin --freeze --void-ok GATE=AMENDMENT
    python3 tools/migration/same_pin.py --selftest
"""
from __future__ import annotations

import datetime
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

FOUND = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SNAPS = os.path.join(FOUND, "snapshots")
LEDGER = "AxiomLedger.lean"
IDENTITY_FILES = ("lean-toolchain", "lake-manifest.json")
CAPPED = os.path.join(FOUND, "tools", "capped_lean.sh")


# ---------------------------------------------------------------------------------------------------
# Parsing. Same bracket-counting rule as footprint_snapshot.headline_names, for its reason: a non-greedy
# regex once ran past a list's end and harvested 122 "names", and the result still looked right.
# ---------------------------------------------------------------------------------------------------

def list_body(text: str, name: str) -> str | None:
    i = text.find(f"def {name} ")
    if i < 0:
        return None
    start = text.index("[", i)
    depth, j = 0, start
    while j < len(text):
        if text[j] == "[":
            depth += 1
        elif text[j] == "]":
            depth -= 1
            if depth == 0:
                break
        j += 1
    return re.sub(r"--[^\n]*", "", text[start + 1:j])


def names(text: str, name: str) -> list[str] | None:
    """Every backticked name in `def <name>`'s list, in order, duplicates kept (Lean's `.length` keeps them)."""
    body = list_body(text, name)
    return None if body is None else re.findall(r"`([\w.']+)", body)


def pairs(text: str, name: str) -> list[tuple[str, str]] | None:
    body = list_body(text, name)
    return None if body is None else re.findall(r"\(\s*`([\w.']+)\s*,\s*`([\w.']+)\s*\)", body)


def sub_theory(text: str) -> dict[str, str] | None:
    """`subTheoryPrimitives`: axiom -> its recorded derivation (first and last names of each tuple)."""
    body = list_body(text, "subTheoryPrimitives")
    if body is None:
        return None
    return {a: d for a, d in re.findall(r"\(\s*`([\w.']+)\s*,.*?`([\w.']+)\s*\)", body, re.S)}


LEDGER_LISTS = ("knownAxioms", "derivableAxioms", "trustedFootprint", "subTheoryPrimitives")


def ledger_record(text: str) -> dict:
    return {"knownAxioms": names(text, "knownAxioms"), "derivableAxioms": pairs(text, "derivableAxioms"),
            "trustedFootprint": names(text, "trustedFootprint"), "subTheoryPrimitives": sub_theory(text)}


def lean4lean_commit(log: str) -> str | None:
    m = re.search(r"^lean4lean commit\s*:\s*([0-9a-f]{7,40})\b", log, re.M)
    return m.group(1) if m else None


# ---------------------------------------------------------------------------------------------------
# The decision. PURE: plain data in, problems out, so --selftest can feed it every way to be wrong.
# ---------------------------------------------------------------------------------------------------

def attribute(base: dict, cur: dict) -> tuple[list[str], dict]:
    problems: list[str] = []
    problems += check_identity(base, cur)
    lost = sorted(set(base["theorems"]) - set(cur["theorems"]))
    problems += [f"[LOST] headline {t} has no footprint now" for t in lost]
    removed = sorted(base["axioms"] - cur["axioms"])
    added = sorted(cur["axioms"] - base["axioms"])
    for ax in removed:
        r = cur["removal"].get(ax) or {}
        if not r.get("commit"):
            problems.append(f"[UNATTRIBUTED] axiom {ax} removed, and no single commit removed its declaration")
        if r.get("kind") in (None, "axiom"):
            problems.append(f"[STILL_AXIOM] {ax} left the ledger but the kernel says: {r.get('kind')}")
    derivations = []
    for ax, wit in base["derivations"]:
        if ax in removed:
            derivations.append((ax, wit, "no longer an axiom (see removed axioms)"))
        elif cur["sub_theory"].get(ax) == wit:
            derivations.append((ax, wit, "sub-theory primitive, derivation kept and ledger-checked"))
        else:
            problems.append(f"[DERIVATION] {ax} via {wit}: still pinned, and not a sub-theory primitive "
                            f"with that derivation")
    trusted = cur["trusted"]
    changed, gained = {}, sorted(set(cur["theorems"]) - set(base["theorems"]))
    for t in sorted(set(base["theorems"]) & set(cur["theorems"])):
        new = set(cur["theorems"][t]) - set(base["theorems"][t])
        if set(cur["theorems"][t]) != set(base["theorems"][t]):
            changed[t] = sorted(new)
        problems += [f"[UNTRUSTED] {t} gained {a}, outside trustedFootprint" for a in sorted(new - trusted)]
    for t in gained:
        problems += [f"[UNTRUSTED] new headline {t} cites {a}, outside trustedFootprint"
                     for a in sorted(set(cur["theorems"][t]) - trusted)]
    record = {"removed_axioms": {ax: cur["removal"].get(ax) for ax in removed}, "added_axioms": added,
              "derivations": [{"axiom": a, "derivation": w, "now": n} for a, w, n in derivations],
              "lost_theorems": lost, "gained_theorems": gained, "changed_footprints": changed}
    return problems, record


def check_identity(base: dict, cur: dict) -> list[str]:
    out = []
    for k in ("toolchain", "lock"):
        if base[k] != cur[k]:
            out.append(f"[IDENTITY] {k}: {base[k]} -> {cur[k]} -- this is a bump, not a same-pin capture")
    for f in IDENTITY_FILES:
        if base["identity"].get(f) != cur["identity"].get(f):
            out.append(f"[IDENTITY] {f} changed between the captures")
    b, c = base["identity"].get("lean4lean"), cur["identity"].get("lean4lean")
    if b is None:
        if not (base["lean4lean_void_cited"] and cur["lean4lean_pass"] and c):
            out.append("[IDENTITY] Lean4Lean: the base has no commit, and this is not an ARRIVAL (the base's "
                       "criterion 7 must be a cited void and this capture's must pass)")
    elif b != c:
        out.append(f"[IDENTITY] Lean4Lean commit {b} -> {c}")
    return out


# ---------------------------------------------------------------------------------------------------
# Gathering. Everything below reads git, files or the kernel, and feeds `attribute`.
# ---------------------------------------------------------------------------------------------------

def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=FOUND, capture_output=True, text=True, check=True).stdout


def sha(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def when(stamp: str) -> datetime.datetime:
    return datetime.datetime.strptime(stamp, "%Y-%m-%dT%H:%M:%S%z")


def newest_sealed_on_pin(toolchain: str, lock: list[str]) -> str | None:
    best = None
    for name in sorted(os.listdir(SNAPS)):
        d = os.path.join(SNAPS, name)
        v = os.path.join(d, "verdict.json")
        if not (os.path.exists(os.path.join(d, "SHA256SUMS")) and os.path.exists(v)):
            continue
        vd = json.load(open(v))
        if vd.get("toolchain") == toolchain and vd.get("lock") == lock:
            if best is None or when(vd["captured_at"]) > best[0]:
                best = (when(vd["captured_at"]), d)
    return best[1] if best else None


def library_commit(vd: dict, base_dir: str) -> str:
    """The commit whose library the base measured: recorded by this mode, else the commit that sealed it."""
    if vd.get("library_commit"):
        return vd["library_commit"]
    rel = os.path.relpath(os.path.join(base_dir, "SHA256SUMS"), FOUND)
    shas = git("log", "--diff-filter=A", "--format=%H", "--", rel).split()
    if not shas:
        raise RuntimeError(f"no commit added {rel}: a base must be committed before it can be a base")
    return shas[-1]


def load_base(base_dir: str) -> tuple[dict, list[str]]:
    vd = json.load(open(os.path.join(base_dir, "verdict.json")))
    commit = library_commit(vd, base_dir)
    errs = []
    ident = vd.get("identity")
    if ident is None:
        ident = {f: sha(git("show", f"{commit}:./{f}")) for f in IDENTITY_FILES}
        # lean-toolchain: the verdict recorded its content, so the seal's copy is checked against THAT.
        # (v4.32.2's capture ran on a branch; the commit that sealed it is also the one that moved the
        # pin, so "did it change after capture" would refuse a file that is provably the same.)
        if git("show", f"{commit}:./lean-toolchain").strip() != vd["toolchain"]:
            errs.append(f"lean-toolchain at {commit[:12]} is not the toolchain the base recorded")
        # lake-manifest.json: nothing recorded, so it must not have moved between capture and seal.
        moved = git("log", "--format=%h", f"--since={vd['captured_at']}", commit, "--",
                    "lake-manifest.json").split()
        if moved:
            errs.append(f"lake-manifest.json changed between the base's capture and its seal "
                        f"({', '.join(moved)}): its identity at capture time cannot be derived")
        ident["lean4lean"] = lean4lean_commit(open(os.path.join(base_dir, "logs", "lean4lean_replay.log")).read())
    path = os.path.join(base_dir, "ledger.json")
    led = json.load(open(path)) if os.path.exists(path) else ledger_record(git("show", f"{commit}:./{LEDGER}"))
    errs += cross_derive("base", led, vd["counts"], None, ("knownAxioms", "derivableAxioms"))
    base = {"label": vd["label"], "toolchain": vd["toolchain"], "lock": vd["lock"], "identity": ident,
            "commit": commit,
            "lean4lean_void_cited": "lean4lean_replay" in vd.get("voids_cited", {}),
            "theorems": json.load(open(os.path.join(base_dir, "footprints.json")))["footprints"],
            "axioms": set(led["knownAxioms"] or []),
            "derivations": [tuple(p) for p in led["derivableAxioms"] or []]}
    return base, errs


def cross_derive(side: str, led: dict, counts: dict, trusted_lean: int | None,
                 required: tuple[str, ...] = tuple(LEDGER_LISTS)) -> list[str]:
    """A base sealed before `subTheoryPrimitives` existed is asked only for the lists it had."""
    errs = []
    if any(led.get(k) is None for k in required):
        errs.append(f"{side}: a ledger list was not found: {[k for k in required if led.get(k) is None]}")
        return errs
    if len(set(led["knownAxioms"])) != counts.get("axioms_pinned"):
        errs.append(f"{side}: knownAxioms parses to {len(set(led['knownAxioms']))}, the Lean ledger counted "
                    f"{counts.get('axioms_pinned')}")
    if len(led["derivableAxioms"]) != counts.get("derivations"):
        errs.append(f"{side}: derivableAxioms parses to {len(led['derivableAxioms'])}, the derivable gate "
                    f"counted {counts.get('derivations')}")
    if trusted_lean is not None and len(led["trustedFootprint"]) != trusted_lean:
        errs.append(f"{side}: trustedFootprint parses to {len(led['trustedFootprint'])}, Lean counted "
                    f"{trusted_lean}")
    return errs


def kernel_kinds(names_: list[str]) -> dict[str, str]:
    """What the kernel says each name is NOW. Same imports as AxiomLedger.lean, under a memory cap."""
    if not names_:
        return {}
    imports = [ln for ln in open(os.path.join(FOUND, LEDGER)).read().splitlines() if ln.startswith("import ")]
    src = "\n".join(imports) + """
open Lean in
def sameKind (env : Environment) (n : Name) : String :=
  match env.find? n with
  | none => "absent" | some (.axiomInfo _) => "axiom" | some (.thmInfo _) => "theorem"
  | some (.defnInfo _) => "def" | some (.opaqueInfo _) => "opaque" | some _ => "other"
open Lean in
run_cmd do
  let env ← getEnv
  for n in [""" + ", ".join(f"`{n}" for n in names_) + """] do
    logInfo m!"KIND {n} {sameKind env n}"
"""
    with tempfile.TemporaryDirectory() as d:
        p = os.path.join(d, "SameKinds.lean")
        open(p, "w").write(src)
        r = subprocess.run([CAPPED, "--cap", "16G", "lake", "env", "lean", p], cwd=FOUND,
                           capture_output=True, text=True)
    got = dict(re.findall(r"KIND (\S+) (\w+)", r.stdout + r.stderr))
    missing = [n for n in names_ if n not in got]
    if missing:
        raise RuntimeError(f"the kernel query answered for {len(got)} of {len(names_)} names "
                           f"(rc={r.returncode}): {missing[:5]}")
    return got


def removal_commit(full: str, since: str) -> str | None:
    """The newest commit in since..HEAD after which no `.lean` file declares `axiom <short>`, and before
    which one did. None when there is no such single commit."""
    ere = rf"axiom[[:space:]]+{full.rsplit('.', 1)[-1]}[[:space:]:]"
    spec = ["--", "*.lean", f":(exclude){LEDGER}"]
    def declared(rev: str) -> bool:
        return subprocess.run(["git", "grep", "-q", "-E", "-e", ere, rev, *spec], cwd=FOUND).returncode == 0
    for c in git("log", "--format=%H", f"-S{ere}", "--pickaxe-regex", f"{since}..HEAD", *spec).split():
        if not declared(c) and declared(f"{c}^"):
            return c
    return None


def load_current(verdict: dict, outs: dict[str, str], target: str, base: dict) -> tuple[dict, list[str]]:
    text = open(os.path.join(FOUND, LEDGER)).read()
    led = ledger_record(text)
    m = re.search(r"⊆ trusted \((\d+) names\)", outs.get("ledger", ""))
    errs = [] if m else ["the ledger gate did not report trustedFootprint's length: no second derivation"]
    errs += cross_derive("this capture", led, verdict["counts"], int(m.group(1)) if m else None)
    json.dump(led, open(os.path.join(target, "ledger.json"), "w"), indent=1)
    axioms = set(led["knownAxioms"] or [])
    removed = sorted(base["axioms"] - axioms)
    kinds = kernel_kinds(removed)
    removal = {}
    for ax in removed:
        c = removal_commit(ax, base["commit"])
        removal[ax] = {"kind": kinds[ax], "commit": c,
                       "subject": git("show", "-s", "--format=%s", c).strip() if c else None}
    ident = {f: sha(open(os.path.join(FOUND, f)).read()) for f in IDENTITY_FILES}
    ident["lean4lean"] = lean4lean_commit(outs.get("lean4lean_replay", ""))
    cur = {"toolchain": verdict["toolchain"], "lock": verdict["lock"], "identity": ident,
           "lean4lean_pass": verdict["gates"].get("lean4lean_replay") == 0,
           "theorems": json.load(open(os.path.join(target, "footprints.json")))["footprints"],
           "axioms": axioms, "trusted": set(led["trustedFootprint"] or []),
           "sub_theory": led["subTheoryPrimitives"] or {}, "removal": removal}
    return cur, errs


def gate_problems(verdict: dict, void_ok: dict[str, str]) -> list[str]:
    out = [f"[GATE] {g} failed" for g in verdict.get("fails", [])]
    out += [f"[GATE] {g} VOID ({c}) and no amendment cited" for g, c in verdict.get("voids", {}).items()
            if g not in void_ok]
    return out


def run(verdict: dict, target: str, outs: dict[str, str], void_ok: dict[str, str]) -> int:
    """Attribute this capture against the newest sealed capture on its pin. 0 = seal, 1 = halt."""
    print(f"\n{'=' * 78}\nSAME-PIN ATTRIBUTION  {verdict['toolchain']}\n{'=' * 78}")
    dirty = git("status", "--porcelain", "--untracked-files=no", "--", "*.lean").strip()
    if dirty:
        print(f"[DIRTY] tracked .lean files differ from HEAD -- the library measured is not a commit:\n{dirty}")
        return 1
    base_dir = newest_sealed_on_pin(verdict["toolchain"], verdict["lock"])
    if base_dir is None:
        print("[NO BASE] no sealed capture on this pin; a same-pin capture needs one to attribute against")
        return 1
    base, errs = load_base(base_dir)
    print(f"base: {os.path.relpath(base_dir, FOUND)}  (library {base['commit'][:12]})")
    cur, cerrs = load_current(verdict, outs, target, base)
    errs += cerrs
    if errs:
        print("INSTRUMENT FAILURE -- attribution NOT attempted:")
        for e in errs:
            print(f"  * {e}")
        return 1
    problems, record = attribute(base, cur)
    problems = gate_problems(verdict, void_ok) + problems
    report(base, cur, record)
    verdict.update({"library_commit": git("rev-parse", "HEAD").strip(), "identity": cur["identity"],
                    "same_pin": {"base": base["label"], "base_library_commit": base["commit"],
                                 "result": "ATTRIBUTED" if not problems else "HALTED",
                                 "problems": problems}})
    json.dump(record, open(os.path.join(target, "attribution.json"), "w"), indent=1)
    open(os.path.join(target, "verdict.json"), "w").write(json.dumps(verdict, indent=1) + "\n")
    print(f"\n{'=' * 78}")
    if problems:
        print("SAME-PIN HALTED -- not sealed:")
        for p in problems:
            print(f"  * {p}")
        return 1
    print("SAME-PIN ATTRIBUTED -- every difference from the base is accounted for mechanically.")
    return 0


def report(base: dict, cur: dict, record: dict) -> None:
    b, c = base["identity"].get("lean4lean"), cur["identity"].get("lean4lean")
    print("identity: " + ", ".join(f"{f} {'same' if base['identity'].get(f) == cur['identity'].get(f) else 'CHANGED'}"
                                   for f in IDENTITY_FILES)
          + f", Lean4Lean {b or 'none (cited void)'} -> {c}" + ("  ARRIVAL" if b is None and c else ""))
    print(f"theorems: {len(base['theorems'])} -> {len(cur['theorems'])}  lost {len(record['lost_theorems'])}, "
          f"gained {len(record['gained_theorems'])}, footprints changed {len(record['changed_footprints'])}")
    kinds: dict[str, int] = {}
    for r in record["removed_axioms"].values():
        kinds[(r or {}).get("kind")] = kinds.get((r or {}).get("kind"), 0) + 1
    print(f"axioms: {len(base['axioms'])} -> {len(cur['axioms'])}  removed {len(record['removed_axioms'])} "
          f"{dict(sorted(kinds.items(), key=str))}, added {len(record['added_axioms'])}")
    for ax, r in record["removed_axioms"].items():
        r = r or {}
        print(f"  - {ax:<52} {r.get('kind')!s:<8} {(r.get('commit') or 'NO COMMIT')[:10]}  {(r.get('subject') or '')[:60]}")
    print(f"derivations: {len(base['derivations'])} in the base, lost "
          f"{len(base['derivations']) - len(record['derivations'])}")
    for d in record["derivations"]:
        print(f"  - {d['axiom']}: {d['now']}")


# ---------------------------------------------------------------------------------------------------
# --selftest: one clean control and one canary per way to be wrong. A canary that does not fire, or a
# control that does, fails the selftest -- an instrument that can only say "attributed" is not one.
# ---------------------------------------------------------------------------------------------------

def _specimens() -> tuple[dict, dict]:
    ident = {"lean-toolchain": "t", "lake-manifest.json": "m", "lean4lean": None}
    base = {"label": "b", "toolchain": "v", "lock": ["v", "k"], "identity": dict(ident), "commit": "c0",
            "lean4lean_void_cited": True, "theorems": {"T1": ["A", "X"], "T2": ["A"]},
            "axioms": {"A", "X", "Z", "D"}, "derivations": [("X", "x_der"), ("D", "d_der")]}
    cur = {"toolchain": "v", "lock": ["v", "k"], "identity": dict(ident, lean4lean="408edad"),
           "lean4lean_pass": True, "theorems": {"T1": ["A", "N"], "T2": ["A"], "T3": ["A"]},
           "axioms": {"A", "N", "D"}, "trusted": {"A", "N"}, "sub_theory": {"D": "d_der"},
           "removal": {"X": {"kind": "theorem", "commit": "c1"}, "Z": {"kind": "absent", "commit": "c2"}}}
    return base, cur


def selftest() -> int:
    import copy
    canaries = {
        "LOST": lambda b, c: c["theorems"].pop("T2"),
        "UNATTRIBUTED": lambda b, c: c["removal"]["Z"].update(commit=None),
        "STILL_AXIOM": lambda b, c: c["removal"]["X"].update(kind="axiom"),
        "DERIVATION": lambda b, c: c["sub_theory"].update(D="other_der"),
        "UNTRUSTED": lambda b, c: c["theorems"]["T1"].append("Q"),
        "UNTRUSTED ": lambda b, c: c["theorems"].update(T4=["Q"]),
        "IDENTITY": lambda b, c: c["identity"].update({"lake-manifest.json": "m2"}),
        "IDENTITY ": lambda b, c: b["identity"].update(lean4lean="aaa"),
        "IDENTITY  ": lambda b, c: b.update(lean4lean_void_cited=False),
        "IDENTITY   ": lambda b, c: c.update(lock=["v", "k2"]),
    }
    base, cur = _specimens()
    problems, _ = attribute(base, cur)
    ok = not problems
    print(f"  control (every difference attributed) stays SILENT: {'yes' if ok else 'NO -- ' + str(problems)}")
    for tag, mutate in canaries.items():
        b, c = copy.deepcopy(base), copy.deepcopy(cur)
        mutate(b, c)
        problems, _ = attribute(b, c)
        fired = any(p.startswith(f"[{tag.strip()}]") for p in problems)
        ok &= fired
        print(f"  canary {tag.strip():<12} {'FIRES' if fired else 'SILENT -- BROKEN'}  {problems[:1]}")
    print("SAME-PIN SELFTEST " + ("PASS" if ok else "FAIL"))
    return 0 if ok else 1


if __name__ == "__main__":
    if sys.argv[1:] == ["--selftest"]:
        raise SystemExit(selftest())
    print(__doc__)
    raise SystemExit(2)
