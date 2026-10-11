#!/usr/bin/env python3
"""Theorem ledger: how many of MachLib's theorems are proved, and on what, read off the Lean environment.

WHY THIS EXISTS (the owner's ruling, 2026-10-10). "A text search is not an acceptable basis for reporting
the number of proved mathematical results." Until this tool, every theorem count MachLib published came from
`tools/count_theorems.py`, a pattern count over source text: it could not say that a counted declaration
compiled, still less what it rests on. "A theorem being accepted by Lean is not automatically proof that it
satisfies Monogate's axiom policy." So this enumerates the ENVIRONMENT, takes every theorem's transitive axiom
footprint from Lean, and classifies the footprint against the axiom policy `AxiomLedger.lean` declares.

HOW. The probe is `AxiomLedger.lean`'s own text with `probe.lean.in` appended, run with `lake env lean` under
`tools/capped_lean.sh`. The live `knownAxioms`, `trustedFootprint`, `headlines` and `isCompilerArtifact` are
therefore the ones in scope -- this tool copies no list -- and the environment is exactly the one the axiom
ledger checks (`import MachLib`, `import MachLib.FPGrounding`). `lake build` runs first, so the `.olean`s Lean
reads are the ones the sources at hand compile to. Lean decides what needs the environment (which declarations
are auxiliary, each footprint via `Lean.collectAxioms`, each statement's canonical serialization); this file
classifies, counts, checks the counts' invariants and binds the result to its provenance.

THE SEVEN COUNTS (each a subset of the one before it, except that the last three partition `theorems`):
  declarations     non-auxiliary declarations of every kind in MachLib's own modules (EXCLUSION_RULE)
  theorems         declarations of kind theorem = approved + conditional + unchecked
  kernel-checked   theorems whose footprint holds no sorryAx, no compiler-trust axiom and only declared axioms
                   = approved + conditional
  axiom-audited    kernel-checked theorems whose footprint was computed and classified (= kernel-checked by
                   construction: a theorem whose footprint was not computed is unchecked)
  approved-policy  footprint within `trustedFootprint`, the declared policy
  conditional      footprint within the declared axioms (`knownAxioms` and `trustedFootprint`) but not within
                   `trustedFootprint`; each record names the axioms it is conditional on
  unchecked        footprint holds sorryAx, a compiler-trust axiom (native_decide is not a kernel check: in Lean
                   v4.32 that is the `_native...ax_N` axiom it adds per use), an undeclared axiom, or was not
                   computed

WHAT IT DOES NOT COUNT. Tracked `.lean` files under `MachLib/` whose module the environment does not contain
(`Discovered/` is outside the aggregator on purpose) are reported as FILES ONLY: nothing elaborated their
declarations in this environment, so none of them is counted, and they are never counted by text.

USAGE (from foundations/)
    python3 tools/theorem_ledger/ledger.py                         # counts on stdout
    python3 tools/theorem_ledger/ledger.py --out theorem_ledger.json
    python3 tools/theorem_ledger/ledger.py --check theorem_ledger.json   # is this ledger still current?
    python3 tools/theorem_ledger/ledger.py --self-test

EXIT STATUS: 0 the ledger was produced and every invariant holds (or --check: CURRENT); 1 an invariant failed,
the axiom ledger failed, or --check: STALE; 2 UNAVAILABLE -- the build, Lean or the probe output failed, so no
count is reported (never a zero, never a pass).
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent            # foundations/tools/theorem_ledger
FOUNDATIONS = HERE.parents[1]                     # foundations/
AXIOM_LEDGER = FOUNDATIONS / "AxiomLedger.lean"
PROBE = HERE / "probe.lean.in"
CAPPED = FOUNDATIONS / "tools" / "capped_lean.sh"

SCHEMA = "machlib-theorem-ledger/v1"
POLICY_NAME = "machlib-axiom-ledger"
DEFAULT_CAP = "8G"            # the probe peaks near 1.5 GB (2026-10-10); this is a shared machine
LEAN_TIMEOUT_S = 1800

#: What a Lean check against MachLib reads, relative to foundations/. The digest over these is DEFINED to agree
#: with Forge's `machlib_sources` (tools/scripts/proof_discharge.py there): a MachLib commit touching none of
#: them -- docs, tools, site -- moves no proof; one touching any of them does.
MACHLIB_SOURCES = ("MachLib", "MachLib.lean", "CertcomLibm.lean", "lakefile.lean", "lean-toolchain",
                   "lake-manifest.json")
SORRY = "sorryAx"
COMPILER_TRUST = ("Lean.ofReduceBool", "Lean.ofReduceNat", "Lean.trustCompiler")
#: Lean v4.32's `native_decide` (and `bv_decide`) does NOT leave `Lean.ofReduceBool` in a footprint. It compiles
#: the decision, runs it, and adds an axiom per use, `<decl>._native.<tactic>.ax_N_M : e = true`
#: (`Lean.Meta.nativeEqTrue`). Found by this tool's own native_decide specimen on 2026-10-10: matching only the
#: three names above classified a native_decide proof as an undeclared-axiom case and never as compiler trust.
NATIVE_AXIOM = re.compile(r"(^|\.)_native\..+\.ax(_\d+)*$")


def is_compiler_trust(axiom: str) -> bool:
    return axiom in COMPILER_TRUST or bool(NATIVE_AXIOM.search(axiom))

EXCLUSION_RULE = [
    ("internal-name", "its name, with any `_private` prefix removed, is an internal detail (Lean's "
     "`Name.isInternalDetail`: a component starting with `_` or numeric, or a final `match_N`, `proof_N`, "
     "`eq_N`, `omega_N`): auxiliary proofs, macro and elab rules, hygienic names"),
    ("recursor", "a recursor (`T.rec`)"),
    ("aux-recursor", "an auxiliary recursor (`Lean.isAuxRecursor`: casesOn, recOn, brecOn, binductionOn, below)"),
    ("no-confusion", "a noConfusion construction (`Lean.isNoConfusion`)"),
    ("matcher", "a compiled pattern match (`Lean.Meta.isMatcherCore`)"),
    ("reserved-name", "a name Lean reserves and generates on demand (`Lean.isReservedName`: equation lemmas "
     "eq_def / eq_unfold, functional induction, hinj, congruence and match-equation theorems)"),
    ("constructor-lemma", "`C.inj`, `C.injEq` or `C.sizeOf_spec` for a constructor `C`"),
    ("compiler-artifact", "an AXIOM matching `AxiomLedger.isCompilerArtifact` (the live function), applied to "
     "axioms as `AxiomLedger.liveAxioms` applies it"),
    ("child-of-auxiliary", "its parent name is a declaration this rule excludes (`T.below.c`, `T.brecOn.eq`)"),
    ("no-source-range", "Lean recorded no source range for it (`findDeclarationRangesCore?`, the table "
     "go-to-definition reads): the elaborator records one for each declaration it elaborates from source text, "
     "so one without was generated (`ctorIdx`, `toCtorIdx`, `ctorElimType`, `noConfusionType`, `ofNat`, the "
     "`brecOn` of an inductive predicate)"),
]
EXCLUSION_NOTES = [
    "The first rule that fires names the reason; a declaration no rule excludes is counted.",
    "A `private` declaration is NOT excluded for being private: `private theorem foo` in module M is "
    "`_private.M.0.foo`, written by hand. Its user name goes through the rules like any other name.",
    "`isCompilerArtifact` is a substring test written for axiom names. Applied to every declaration it would drop "
    "hand-written theorems such as `geomSum_closed` (`_closed`); diagnostics.compiler_artifact_names_kept lists "
    "every non-axiom declaration it matches.",
    "Scope: constants whose module (the environment's module index) is `MachLib`, `MachLib.*` or `CertcomLibm`.",
]
DEFINITIONS = {
    "declarations": "Non-auxiliary declarations of every kind (rules.exclusion) whose module is one of "
                    "MachLib's own, in the environment the imports build.",
    "theorems": "Declarations of kind theorem (ConstantInfo.thmInfo) = approved_policy + conditional + unchecked. "
                "A proof stated with `def` is a definition here (diagnostics.prop_valued_definitions).",
    "kernel_checked": "Theorems admitted to the environment by Lean's kernel when `lake build` compiled their "
                      "module, whose footprint holds no sorryAx, no compiler-trust axiom and only declared "
                      "axioms = approved_policy + conditional. Importing a module does not re-run the kernel; "
                      "tools/axiom_ledger/check_kernel_replay.py replays it and is not run here.",
    "axiom_audited": "Kernel-checked theorems whose transitive axiom footprint (Lean.collectAxioms, what #print "
                     "axioms prints) was computed and classified against axiom_policy. Equal to kernel_checked "
                     "by construction; a theorem whose footprint was not computed is unchecked.",
    "approved_policy": "Footprint within AxiomLedger.trustedFootprint, the declared policy (it includes "
                       "propext, Classical.choice and Quot.sound).",
    "conditional": "Footprint within the declared axioms (knownAxioms with trustedFootprint) but not within "
                   "trustedFootprint: proved on the declared axioms named in the record's conditional_on.",
    "unchecked": "Footprint contains sorryAx, a compiler-trust axiom (Lean.ofReduceBool, Lean.ofReduceNat, "
                 "Lean.trustCompiler, or the `<decl>._native.<tactic>.ax_N` axiom Lean v4.32's native_decide and "
                 "bv_decide add per use: a compiled evaluation is not a kernel check) or an axiom outside the "
                 "declared axioms, or was not computed.",
}
STATEMENT_DIGEST_RULE = (
    "sha256 of the UTF-8 text `machlib-stmt/v1 U<number of universe parameters> <type>`, where <type> is a "
    "structural serialization of the stored type keeping constructor shape, constant names with universe "
    "arguments, de Bruijn indices and literals, with universe parameters written by position and binder names, "
    "binder info and mdata dropped (probe.lean.in, `statementSer`). A representation digest: an alpha-renamed "
    "binder does not move it; a mathematically equivalent restatement does.")


class Unavailable(Exception):
    """A measurement that could not be made. Reported as UNAVAILABLE (exit 2), never as a count."""


# ── git and toolchain provenance ────────────────────────────────────────────────────────────────────────────

def _git_env() -> dict[str, str]:
    return {k: v for k, v in os.environ.items() if k not in ("GIT_DIR", "GIT_WORK_TREE", "GIT_INDEX_FILE")}


def git(*args: str) -> str:
    r = subprocess.run(["git", *args], cwd=FOUNDATIONS, capture_output=True, text=True, env=_git_env())
    if r.returncode != 0:
        raise Unavailable(f"git {' '.join(args)} failed: {r.stderr.strip()[:200]}")
    return r.stdout


def sources_digest(commit: str = "HEAD") -> str:
    """Forge's definition, byte for byte: `sha256:` over `path objectid` lines of MACHLIB_SOURCES at `commit`."""
    lines = []
    for rel in MACHLIB_SOURCES:
        r = subprocess.run(["git", "rev-parse", f"{commit}:./{rel}"], cwd=FOUNDATIONS, capture_output=True,
                           text=True, env=_git_env())
        lines.append(f"{rel} {r.stdout.strip() if r.returncode == 0 else 'absent'}")
    return "sha256:" + hashlib.sha256("\n".join(lines).encode()).hexdigest()


def dirty(*paths: str) -> list[str]:
    out = git("status", "--porcelain", "--untracked-files=no", "--", *paths)
    return sorted(line[3:] for line in out.splitlines() if line.strip())


def lean_version() -> str:
    r = subprocess.run(["lake", "env", "lean", "--version"], cwd=FOUNDATIONS, capture_output=True, text=True,
                       timeout=300)
    lines = (r.stdout or r.stderr).strip().splitlines()
    if r.returncode != 0 or not lines:
        raise Unavailable(f"`lake env lean --version` failed (rc {r.returncode})")
    return lines[0].strip()


def tool_digest() -> str:
    h = hashlib.sha256()
    for p in (Path(__file__).resolve(), PROBE):
        h.update(p.name.encode() + b"\0" + p.read_bytes() + b"\0")
    return "sha256:" + h.hexdigest()


def imports_of(text: str) -> list[str]:
    return re.findall(r"^import\s+(\S+)", text, re.M)


def git_provenance() -> dict:
    whole = dirty()
    src = dirty(*MACHLIB_SOURCES)
    al = dirty("AxiomLedger.lean")
    return {
        "machlib_commit": git("rev-parse", "HEAD").strip(),
        "tracked_tree_clean": not whole,
        "machlib_sources": sources_digest(),
        "machlib_source_paths": [f"foundations/{p}" for p in MACHLIB_SOURCES],
        "sources_clean": not src,
        "dirty_source_paths": src,
        "axiom_ledger_blob": git("rev-parse", "HEAD:./AxiomLedger.lean").strip(),
        "axiom_ledger_clean": not al,
        "lean_toolchain": (FOUNDATIONS / "lean-toolchain").read_text(encoding="utf-8").strip(),
    }


# ── running the probe ───────────────────────────────────────────────────────────────────────────────────────

def probe_text(out_path: Path, fixture: str | None = None, fixture_prefix: str | None = None) -> str:
    """AxiomLedger.lean verbatim, an optional fixture, then the probe. Nothing is copied out of AxiomLedger."""
    s = str(out_path)
    if '"' in s or "\\" in s or "\n" in s:
        raise Unavailable(f"output path cannot be written as a Lean string literal: {s!r}")
    tail = PROBE.read_text(encoding="utf-8")
    tail = tail.replace("@@OUT_PATH@@", s)
    tail = tail.replace("@@FIXTURE_PREFIX@@", f"`{fixture_prefix}" if fixture_prefix else "Name.anonymous")
    return AXIOM_LEDGER.read_text(encoding="utf-8") + "\n" + (fixture or "") + "\n" + tail


def run_capped(cmd: list[str], cap: str) -> tuple[int, str]:
    r = subprocess.run(["bash", str(CAPPED), "--cap", cap, *cmd], cwd=FOUNDATIONS, capture_output=True, text=True,
                       timeout=LEAN_TIMEOUT_S)
    return r.returncode, r.stdout + r.stderr


def lake_build(cap: str) -> str:
    rc, out = run_capped(["lake", "build"], cap)
    tail = [line for line in out.strip().splitlines() if line.strip()]
    if rc != 0:
        raise Unavailable(f"`lake build` failed (rc {rc}): {tail[-1][:200] if tail else 'no output'}; the "
                          "environment is not the one the sources compile to, so nothing is counted")
    done = [line for line in tail if line.startswith("Build completed")]
    return done[-1] if done else (tail[-1] if tail else "")


def run_probe(cap: str, fixture: str | None = None, fixture_prefix: str | None = None) -> tuple[dict, str]:
    """Write and run the probe file; return (parsed raw facts, Lean's own output)."""
    with tempfile.TemporaryDirectory(prefix="machlib_theorem_ledger_") as tmp:
        raw = Path(tmp) / "raw.jsonl"
        lean = Path(tmp) / "TheoremLedgerProbe.lean"
        lean.write_text(probe_text(raw, fixture, fixture_prefix), encoding="utf-8")
        rc, out = run_capped(["lake", "env", "lean", str(lean)], cap)
        if not raw.exists():
            last = [line for line in out.strip().splitlines() if line.strip()]
            raise Unavailable(f"the probe wrote nothing (lean rc {rc}): {last[-1][:300] if last else 'no output'}")
        facts = parse_raw(raw.read_text(encoding="utf-8"))
    facts["lean_rc"] = rc
    return facts, out.replace(str(lean), "<probe>")


def parse_raw(text: str) -> dict:
    policy = environment = end = None
    decls = []
    for line in text.splitlines():
        if not line.strip():
            continue
        o = json.loads(line)
        t = o.get("t")
        if t == "decl":
            decls.append(o)
        elif t == "policy":
            policy = o
        elif t == "environment":
            environment = o
        elif t == "end":
            end = o
    if policy is None or environment is None:
        raise Unavailable("probe output lacks its policy or environment record")
    if end is None or end.get("declarations_emitted") != len(decls):
        raise Unavailable(f"probe output is truncated: {len(decls)} declaration records, end marker {end}")
    return {"policy": policy, "environment": environment, "decls": decls}


def axiom_ledger_verdict(lean_output: str) -> dict:
    m = re.search(r"AxiomLedger (OK|FAIL): (.*)$", lean_output, re.M)
    errors = [line for line in lean_output.splitlines() if "error:" in line]
    if not m:
        return {"verdict": "UNAVAILABLE", "line": None, "errors": errors[:10]}
    return {"verdict": m.group(1), "line": f"AxiomLedger {m.group(1)}: {m.group(2).strip()}", "errors": errors[:10]}


# ── classification ──────────────────────────────────────────────────────────────────────────────────────────

def classify(footprint: list[str] | None, known: set[str], trusted: set[str]) -> dict:
    """One theorem's check result, from its footprint and the two live lists. Exhaustive and disjoint."""
    if footprint is None:
        return {"classification": "unchecked", "unchecked_reasons": ["footprint-not-computed"]}
    fp = set(footprint)
    declared = known | trusted
    reasons = []
    if SORRY in fp:
        reasons.append("sorryAx")
    if any(is_compiler_trust(a) for a in fp):
        reasons.append("compiler-trust")
    undeclared = sorted(a for a in fp - declared - {SORRY} if not is_compiler_trust(a))
    if undeclared:
        reasons.append("undeclared-axiom")
    if reasons:
        out = {"classification": "unchecked", "unchecked_reasons": reasons}
        if undeclared:
            out["undeclared_axioms"] = undeclared
        return out
    if fp <= trusted:
        return {"classification": "approved_policy"}
    return {"classification": "conditional", "conditional_on": sorted(fp - trusted)}


def axiom_set_id(axioms: list[str]) -> str:
    return "sha256:" + hashlib.sha256("\n".join(sorted(axioms)).encode()).hexdigest()


def statement_digest(ser: str) -> str:
    return "sha256:" + hashlib.sha256(ser.encode("utf-8")).hexdigest()


def policy_block(policy: dict, al_blob: str) -> dict:
    known, trusted = sorted(set(policy["known"])), sorted(set(policy["trusted"]))
    k = hashlib.sha256("\n".join(known).encode()).hexdigest()
    t = hashlib.sha256("\n".join(trusted).encode()).hexdigest()
    version = hashlib.sha256(f"knownAxioms {k}\ntrustedFootprint {t}\n".encode()).hexdigest()
    return {
        "name": POLICY_NAME,
        "version": f"{POLICY_NAME}@sha256:{version}",
        "source": "foundations/AxiomLedger.lean: the live knownAxioms and trustedFootprint",
        "axiom_ledger_blob": al_blob,
        "known_axioms_sha256": "sha256:" + k,
        "trusted_footprint_sha256": "sha256:" + t,
        "known_axioms_count": len(known),
        "trusted_footprint_count": len(trusted),
        "trusted_outside_known": sorted(set(trusted) - set(known)),
        "declared_axioms": "knownAxioms with trustedFootprint",
        "compiler_trust_axioms": list(COMPILER_TRUST) + ["<decl>._native.<tactic>.ax_N (native_decide, bv_decide)"],
    }


def classify_all(decls: list[dict], policy: dict) -> tuple[list[dict], list[dict], dict]:
    """Counted declarations, per-theorem records and the axiom-set table."""
    known, trusted = set(policy["known"]), set(policy["trusted"])
    counted = sorted((d for d in decls if d["x"] is None), key=lambda d: d["n"])
    theorems, sets = [], {}
    for d in counted:
        if d["k"] != "theorem":
            continue
        fp = d.get("a")
        rec = {"name": d["n"], "module": d["m"], "private": bool(d["priv"])}
        rec["statement_digest"] = statement_digest(d["s"]) if "s" in d else None
        rec.update(classify(fp, known, trusted))
        if fp is not None:
            sid = axiom_set_id(fp)
            if sets.setdefault(sid, sorted(fp)) != sorted(fp):
                raise Unavailable(f"axiom-set digest collision at {sid}")
            rec["axiom_set"] = sid
            rec["axiom_count"] = len(fp)
        theorems.append(rec)
    return counted, theorems, sets


def count(counted: list[dict], theorems: list[dict]) -> dict:
    cls = Counter(t["classification"] for t in theorems)
    audited = sum(1 for t in theorems if t["classification"] in ("approved_policy", "conditional")
                  and t.get("axiom_set") is not None)
    approved, conditional, unchecked = cls["approved_policy"], cls["conditional"], cls["unchecked"]
    reasons = Counter(r for t in theorems for r in t.get("unchecked_reasons", []))
    cond_on = Counter(a for t in theorems for a in t.get("conditional_on", []))
    return {
        "declarations": len(counted),
        "theorems": len(theorems),
        "kernel_checked": approved + conditional,
        "axiom_audited": audited,
        "approved_policy": approved,
        "conditional": conditional,
        "unchecked": unchecked,
        "declarations_by_kind": dict(sorted(Counter(d["k"] for d in counted).items())),
        "unchecked_by_reason": dict(sorted(reasons.items())),
        "conditional_by_axiom": dict(sorted(cond_on.items())),
        "private_theorems": sum(1 for t in theorems if t["private"]),
    }


def invariants(c: dict) -> list[tuple[str, bool]]:
    """The arithmetic the seven counts must satisfy. Each is checked on every run and printed."""
    return [
        ("theorems = approved_policy + conditional + unchecked",
         c["theorems"] == c["approved_policy"] + c["conditional"] + c["unchecked"]),
        ("kernel_checked = approved_policy + conditional",
         c["kernel_checked"] == c["approved_policy"] + c["conditional"]),
        ("axiom_audited = kernel_checked", c["axiom_audited"] == c["kernel_checked"]),
        ("theorems <= declarations", c["theorems"] <= c["declarations"]),
    ]


def cross_checks(counted: list[dict], theorems: list[dict], policy: dict) -> list[tuple[str, bool, str]]:
    """Agreement with the axiom ledger's own lists: two instruments, one environment."""
    known, trusted = set(policy["known"]), set(policy["trusted"])
    axioms = {d["n"] for d in counted if d["k"] == "axiom"}
    by_name = {t["name"]: t for t in theorems}
    missing_h = [h for h in policy["headlines"] if h not in by_name]
    unapproved_h = [h for h in policy["headlines"] if h in by_name
                    and by_name[h]["classification"] != "approved_policy"]
    bad_trust = sorted(a for a in trusted if a == SORRY or is_compiler_trust(a))
    return [
        ("the axioms counted are exactly knownAxioms", axioms == known,
         f"counted-not-known {sorted(axioms - known)[:5]}, known-not-counted {sorted(known - axioms)[:5]}"),
        ("every AxiomLedger headline is a counted theorem", not missing_h, f"missing {missing_h[:5]}"),
        ("every AxiomLedger headline is approved-policy", not unapproved_h, f"not approved {unapproved_h[:5]}"),
        ("trustedFootprint admits no sorryAx or compiler-trust axiom", not bad_trust, f"{bad_trust}"),
    ]


# ── what the environment does not contain ───────────────────────────────────────────────────────────────────

def outside_environment(env_modules: list[str]) -> dict:
    files = [p for p in git("ls-files", "-z", "--", "MachLib").split("\0") if p.endswith(".lean")]
    mods = set(env_modules)
    out = sorted(p for p in files if p[:-len(".lean")].replace("/", ".") not in mods)
    by_dir = Counter(p.split("/")[1] if p.count("/") >= 2 else "(top level)" for p in out)
    return {
        "tracked_lean_files": len(files),
        "files_outside_environment": len(out),
        "by_directory": dict(sorted(by_dir.items())),
        "paths": out,
        "note": "Tracked .lean files under foundations/MachLib whose module the environment does not contain. "
                "Counted as FILES ONLY: nothing elaborated their declarations in this environment, so none of "
                "their declarations is counted, and they are never counted by text.",
    }


def diagnostics(decls: list[dict], counted: list[dict]) -> dict:
    by_reason: dict[str, Counter] = {}
    for d in decls:
        if d["x"]:
            by_reason.setdefault(d["x"], Counter())[d["k"]] += 1
    name_ruled_ranged = sorted(d["n"] for d in decls if d["x"] and d["x"] != "no-source-range" and d["rng"])
    range_only = [d for d in decls if d["x"] == "no-source-range"]
    return {
        "excluded_by_reason": {r: dict(sorted(c.items())) for r, c in sorted(by_reason.items())},
        "excluded_by_a_name_rule_with_a_source_range": {
            "count": len(name_ruled_ranged), "sample": name_ruled_ranged[:12],
            "note": "Declarations a name or environment rule excludes although Lean recorded a source range "
                    "for them (expected: macro_rules / elab_rules implementations, `_aux_...`)."},
        "excluded_only_for_no_source_range": {
            "count": len(range_only), "by_kind": dict(sorted(Counter(d["k"] for d in range_only).items())),
            "sample": sorted(d["n"] for d in range_only)[:12]},
        "compiler_artifact_names_kept": sorted(d["n"] for d in counted if d["ca"]),
        "prop_valued_definitions": sorted(d["n"] for d in counted if d.get("prop")),
        "private_declarations_counted": dict(sorted(Counter(d["k"] for d in counted if d["priv"]).items())),
    }


# ── assembling, writing, summarising ────────────────────────────────────────────────────────────────────────

def canonical(obj) -> bytes:
    return (json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")


def binding_of(prov: dict, policy: dict) -> dict:
    # Not the commit: a commit that touches no source moves no proof (Forge binds the same way). It is in provenance.
    keys = ("machlib_sources", "sources_clean", "axiom_ledger_blob", "axiom_ledger_clean", "lean_version",
            "lean_toolchain", "imports", "tool_digest")
    b = {k: prov[k] for k in keys}
    b["environment_modules_sha256"] = prov["environment"]["own_modules_sha256"]
    b["axiom_policy_version"] = policy["version"]
    return b


def assemble(facts: dict, lean_out: str, prov: dict) -> dict:
    policy_raw, env = facts["policy"], facts["environment"]
    policy = policy_block(policy_raw, prov["axiom_ledger_blob"])
    own = env["own_modules"]
    prov["environment"] = {
        "header_imports": list(dict.fromkeys(env["imports"])),
        "modules_total": len(env["modules"]),
        "own_modules": len(own),
        "own_modules_sha256": "sha256:" + hashlib.sha256("\n".join(sorted(own)).encode()).hexdigest(),
    }
    counted, theorems, sets = classify_all(facts["decls"], policy_raw)
    c = count(counted, theorems)
    inv = invariants(c)
    xc = cross_checks(counted, theorems, policy_raw)
    outside = outside_environment(env["modules"])
    tracked_mods = {p[:-len(".lean")].replace("/", ".") for p in git("ls-files", "-z", "--", "*.lean").split("\0")
                    if p.endswith(".lean")}
    untracked_env = sorted(m for m in own if m not in tracked_mods)
    al = axiom_ledger_verdict(lean_out)
    al["lean_exit_code"] = facts["lean_rc"]
    binding = binding_of(prov, policy)
    binding_id = "sha256:" + hashlib.sha256(canonical(binding)).hexdigest()
    unbound = []
    if not prov["sources_clean"]:
        unbound.append(f"sources differ from HEAD: {prov['dirty_source_paths'][:5]}")
    if not prov["axiom_ledger_clean"]:
        unbound.append("AxiomLedger.lean differs from HEAD")
    if untracked_env:
        unbound.append(f"the environment holds modules git does not track: {untracked_env[:5]}")
    for t in theorems:
        t["binding"] = binding_id
    return {
        "schema": SCHEMA,
        "provenance": prov,
        "binding": binding,
        "binding_id": binding_id,
        "bound_to_head": not unbound,
        "unbound_reasons": unbound,
        "axiom_policy": policy,
        "axiom_ledger": al,
        "rules": {
            "exclusion": [{"reason": r, "rule": txt} for r, txt in EXCLUSION_RULE],
            "exclusion_notes": EXCLUSION_NOTES,
            "definitions": DEFINITIONS,
            "statement_digest": STATEMENT_DIGEST_RULE,
        },
        "counts": c,
        "invariants": [{"check": name, "holds": ok} for name, ok in inv],
        "cross_checks": [{"check": name, "holds": ok, "detail": "" if ok else det} for name, ok, det in xc],
        "outside_environment": outside,
        "diagnostics": diagnostics(facts["decls"], counted),
        "declarations": [{"name": d["n"], "kind": d["k"], "module": d["m"]} for d in counted],
        "theorems": theorems,
        "axiom_sets": dict(sorted(sets.items())),
    }


def checks_hold(ledger: dict) -> bool:
    """The invariants, the cross-checks against AxiomLedger, and AxiomLedger's own verdict."""
    return (all(i["holds"] for i in ledger["invariants"]) and all(x["holds"] for x in ledger["cross_checks"])
            and ledger["axiom_ledger"]["verdict"] == "OK" and ledger["axiom_ledger"]["lean_exit_code"] == 0)


def verdict(ledger: dict) -> str:
    """OK only when the checks hold AND the ledger is bound to a commit: counts read off a tree no commit names are
    UNBOUND -- true of that tree, quotable nowhere. (A review of the first version, 2026-10-10: it printed OK and
    exited 0 for an unbound ledger, a trap for anyone taking exit 0 as "safe to quote".)"""
    if not checks_hold(ledger):
        return "FAIL"
    return "OK" if ledger.get("bound_to_head", False) else "UNBOUND"


def verdict_ok(ledger: dict) -> bool:
    return verdict(ledger) == "OK"


#: Exit codes: OK 0, FAIL 1, UNAVAILABLE 2, UNBOUND 3 (0 with --allow-unbound, for a working-tree gate).
EXIT = {"OK": 0, "FAIL": 1, "UNBOUND": 3}


def summary(ledger: dict, digest: str | None) -> list[str]:
    c, p = ledger["counts"], ledger["provenance"]
    o = ledger["outside_environment"]
    v = verdict(ledger)
    reasons = ", ".join(f"{k} {v}" for k, v in c["unchecked_by_reason"].items()) or "none"
    lines = [
        f"THEOREM-LEDGER {v} -- MachLib {p['machlib_commit'][:12]}, sources "
        f"{p['machlib_sources'][:19]} ({'clean' if p['sources_clean'] else 'DIRTY'}), {p['lean_version']}",
        f"  axiom policy {ledger['axiom_policy']['version'][:40]}..., {ledger['axiom_ledger']['verdict']} by "
        "AxiomLedger.lean",
        f"  declarations             {c['declarations']:>6}",
        f"  theorems                 {c['theorems']:>6}",
        f"  kernel-checked           {c['kernel_checked']:>6}",
        f"  axiom-audited            {c['axiom_audited']:>6}",
        f"  approved-policy proofs   {c['approved_policy']:>6}",
        f"  conditional proofs       {c['conditional']:>6}",
        f"  unchecked                {c['unchecked']:>6}   ({reasons})",
        f"  outside the environment: {o['files_outside_environment']} of {o['tracked_lean_files']} tracked .lean "
        f"files under MachLib/ ({', '.join(f'{k} {v}' for k, v in o['by_directory'].items())}) -- files only; "
        "nothing elaborated their declarations here, so none is counted",
    ]
    for i in ledger["invariants"] + ledger["cross_checks"]:
        lines.append(f"  {'holds ' if i['holds'] else 'FAILS '} {i['check']}" + (f": {i.get('detail')}"
                                                                                 if i.get("detail") else ""))
    if not ledger["bound_to_head"]:
        lines.append(f"  UNBOUND: {'; '.join(ledger['unbound_reasons'])} -- no commit names what Lean read")
    if digest:
        lines.append(f"  ledger {digest}")
    return lines


def generate(cap: str) -> dict:
    prov = git_provenance()
    prov["lean_version"] = lean_version()
    prov["imports"] = imports_of(AXIOM_LEDGER.read_text(encoding="utf-8"))
    prov["tool_digest"] = tool_digest()
    prov["build"] = lake_build(cap)
    facts, out = run_probe(cap)
    # A verdict binds to the tree it read; an edit during the run would bind it to one that no longer exists.
    after = git_provenance()
    moved = [k for k in ("machlib_commit", "machlib_sources", "sources_clean", "dirty_source_paths",
                         "axiom_ledger_blob", "axiom_ledger_clean") if after[k] != prov[k]]
    if moved:
        raise Unavailable(f"the tree changed during the run ({', '.join(moved)}); re-run on a quiescent tree")
    return assemble(facts, out, prov)


def cmd_generate(args: argparse.Namespace) -> int:
    try:
        ledger = generate(args.cap)
    except (Unavailable, subprocess.TimeoutExpired, json.JSONDecodeError, OSError, KeyError, ValueError) as e:
        print(f"THEOREM-LEDGER UNAVAILABLE -- {type(e).__name__}: {e}")
        if args.out:
            args.out.write_bytes(canonical({"schema": SCHEMA, "unavailable": True, "reason": str(e)}))
        return 2
    data = canonical(ledger)
    digest = "sha256:" + hashlib.sha256(data).hexdigest()
    if args.out:
        args.out.write_bytes(data)
    print("\n".join(summary(ledger, digest)))
    v = verdict(ledger)
    return 0 if v == "UNBOUND" and args.allow_unbound else EXIT[v]


#: What `--check` recomputes without Lean. The axiom-policy version and the environment's module list are functions
#: of these (AxiomLedger.lean's blob, the sources, the toolchain), so they need no Lean run to be re-bound.
CHECK_KEYS = ("machlib_sources", "axiom_ledger_blob", "lean_version", "lean_toolchain", "imports", "tool_digest")


def current_binding_inputs() -> dict:
    now = git_provenance()
    now.update(lean_version=lean_version(), tool_digest=tool_digest(),
               imports=imports_of(AXIOM_LEDGER.read_text(encoding="utf-8")))
    return now


def cmd_check(path: Path) -> int:
    """Is a written ledger still the evidence for the tree at hand? Git and the toolchain only, no Lean run."""
    try:
        ledger = json.loads(path.read_text(encoding="utf-8"))
        if ledger.get("unavailable"):
            print(f"THEOREM-LEDGER-CHECK UNAVAILABLE -- the ledger itself is unavailable: {ledger.get('reason')}")
            return 2
        old = ledger["binding"]
        now = current_binding_inputs()
    except (Unavailable, OSError, KeyError, json.JSONDecodeError, subprocess.TimeoutExpired) as e:
        print(f"THEOREM-LEDGER-CHECK UNAVAILABLE -- {e}")
        return 2
    moved = [f"{k}: {old.get(k)} -> {now[k]}" for k in CHECK_KEYS if old.get(k) != now[k]]
    if not now["sources_clean"]:
        moved.append(f"sources differ from HEAD: {now['dirty_source_paths'][:5]}")
    if not now["axiom_ledger_clean"]:
        moved.append("AxiomLedger.lean differs from HEAD")
    if not ledger.get("bound_to_head", False):
        moved.append(f"the ledger was never bound: {ledger.get('unbound_reasons')}")
    if moved:
        print(f"THEOREM-LEDGER-CHECK STALE -- {path.name} ({ledger['binding_id'][:19]}) no longer describes "
              "this tree; regenerate it. Moved:")
        print("\n".join(f"  {m}" for m in moved))
        return 1
    print(f"THEOREM-LEDGER-CHECK CURRENT -- {path.name} binds to sources {now['machlib_sources'][:19]}, "
          f"policy blob {now['axiom_ledger_blob'][:12]}, {now['lean_version']}")
    return 0


# ── self-test ───────────────────────────────────────────────────────────────────────────────────────────────

FIXTURE = r'''
namespace LedgerFixture
theorem approved_rfl : (1 : Nat) + 1 = 2 := rfl
theorem approved_classical (p : Prop) : p ∨ ¬p := Classical.em p
theorem conditional_erf : True := (fun _ => trivial) MachLib.Real.erf_le_one
theorem unchecked_sorry : (1 : Nat) = 2 := sorry
theorem unchecked_native : 20 + 22 = 42 := by native_decide
axiom local_axiom : (2 : Nat) = 3
theorem unchecked_local_axiom : (2 : Nat) = 3 := local_axiom
theorem alpha_x (x : Nat) : x = x := rfl
theorem alpha_y (y : Nat) : y = y := rfl
theorem alpha_add (x : Nat) : x + 0 = x := rfl
theorem geom_closed : True := trivial
private theorem private_helper : True := trivial
inductive Shape where
  | dot
  | seg (n : Nat)
def dbl : Nat → Nat
  | 0 => 0
  | n + 1 => dbl n + 2
theorem dbl_zero : dbl 0 = 0 := by simp [dbl]
end LedgerFixture
'''
#: user name -> (kind, classification or None, reason that must be among unchecked_reasons or None)
FIXTURE_EXPECT = {
    "LedgerFixture.approved_rfl": ("theorem", "approved_policy", None),
    "LedgerFixture.approved_classical": ("theorem", "approved_policy", None),
    "LedgerFixture.conditional_erf": ("theorem", "conditional", None),
    "LedgerFixture.unchecked_sorry": ("theorem", "unchecked", "sorryAx"),
    "LedgerFixture.unchecked_native": ("theorem", "unchecked", "compiler-trust"),
    "LedgerFixture.local_axiom": ("axiom", None, None),
    "LedgerFixture.unchecked_local_axiom": ("theorem", "unchecked", "undeclared-axiom"),
    "LedgerFixture.alpha_x": ("theorem", "approved_policy", None),
    "LedgerFixture.alpha_y": ("theorem", "approved_policy", None),
    "LedgerFixture.alpha_add": ("theorem", "approved_policy", None),
    "LedgerFixture.geom_closed": ("theorem", "approved_policy", None),
    "LedgerFixture.private_helper": ("theorem", "approved_policy", None),
    "LedgerFixture.Shape": ("inductive", None, None),
    "LedgerFixture.Shape.dot": ("constructor", None, None),
    "LedgerFixture.Shape.seg": ("constructor", None, None),
    "LedgerFixture.dbl": ("definition", None, None),
    "LedgerFixture.dbl_zero": ("theorem", "approved_policy", None),
}
CONDITIONAL_FIXTURE_AXIOM = "MachLib.Real.erf_le_one"


def check_canaries(check) -> None:
    """`--check` must read a binding equal to this tree's as CURRENT and a moved source digest as STALE."""
    import contextlib
    import io
    now = current_binding_inputs()
    cur = {"binding": {k: now[k] for k in CHECK_KEYS}, "binding_id": "sha256:selftest", "bound_to_head": True}
    moved = dict(cur, binding=dict(cur["binding"], machlib_sources="sha256:" + "0" * 64))
    rcs = []
    with tempfile.TemporaryDirectory(prefix="machlib_theorem_ledger_check_") as tmp:
        for name, obj in (("current.json", cur), ("moved.json", moved)):
            p = Path(tmp) / name
            p.write_text(json.dumps(obj), encoding="utf-8")
            with contextlib.redirect_stdout(io.StringIO()):
                rcs.append(cmd_check(p))
    check(rcs[1] == 1, f"--check reads a moved source digest as STALE (rc {rcs[1]})")
    if now["sources_clean"] and now["axiom_ledger_clean"]:
        check(rcs[0] == 0, f"--check reads this tree's own binding as CURRENT (rc {rcs[0]})")
    else:
        print("  skip --check CURRENT canary: the sources or AxiomLedger.lean differ from HEAD")


def self_test(cap: str) -> int:
    print("=== THEOREM-LEDGER SELFTEST ===")
    fails: list[str] = []

    def check(ok: bool, what: str) -> None:
        print(f"  {'ok  ' if ok else 'FAIL'} {what}")
        if not ok:
            fails.append(what)

    try:
        facts, _ = run_probe(cap, FIXTURE, "LedgerFixture")
    except (Unavailable, subprocess.TimeoutExpired) as e:
        print(f"THEOREM-LEDGER SELFTEST UNAVAILABLE -- {e}")
        return 2
    pol = facts["policy"]
    check(CONDITIONAL_FIXTURE_AXIOM in pol["known"] and CONDITIONAL_FIXTURE_AXIOM not in pol["trusted"],
          f"the conditional specimen's axiom {CONDITIONAL_FIXTURE_AXIOM} is declared and not trusted")
    counted, theorems, _ = classify_all(facts["decls"], pol)
    got = {d["u"]: d for d in counted}
    user = {d["n"]: d["u"] for d in counted}
    check(set(got) == set(FIXTURE_EXPECT),
          f"exactly the hand-written fixture declarations are counted (extra {sorted(set(got) - set(FIXTURE_EXPECT))}"
          f", missing {sorted(set(FIXTURE_EXPECT) - set(got))})")
    recs = {user[t["name"]]: t for t in theorems}
    for name, (kind, cls, reason) in FIXTURE_EXPECT.items():
        d = got.get(name)
        if d is None:
            continue
        check(d["k"] == kind, f"{name} has kind {kind} (got {d['k']})")
        if cls:
            r = recs.get(name, {})
            check(r.get("classification") == cls, f"{name} is {cls} (got {r.get('classification')}, "
                                                   f"footprint {d.get('a')})")
            if reason:
                check(reason in r.get("unchecked_reasons", []), f"{name} is unchecked for {reason}")
    cond = recs.get("LedgerFixture.conditional_erf", {})
    check(CONDITIONAL_FIXTURE_AXIOM in cond.get("conditional_on", []),
          "the conditional specimen names the declared axiom it is conditional on")
    native_fp = (got.get("LedgerFixture.unchecked_native") or {}).get("a", [])
    check(any(NATIVE_AXIOM.search(a) for a in native_fp),
          f"native_decide leaves its per-use `_native` axiom in the footprint ({native_fp})")
    excluded = {d["x"] for d in facts["decls"] if d["x"]}
    for r in ("recursor", "aux-recursor", "constructor-lemma", "no-source-range"):
        check(r in excluded, f"generated declarations are excluded as {r}")
    sx, sy, sa = (recs.get(f"LedgerFixture.{n}", {}).get("statement_digest") for n in ("alpha_x", "alpha_y",
                                                                                       "alpha_add"))
    check(sx is not None and sx == sy, "an alpha-renamed binder leaves the statement digest unchanged")
    check(sx is not None and sx != sa, "a different statement moves the statement digest")
    check(recs.get("LedgerFixture.private_helper", {}).get("private") is True,
          "a private theorem is counted and marked private")
    c = count(counted, theorems)
    check(all(ok for _, ok in invariants(c)), "the fixture's counts satisfy every invariant")
    for k in ("approved_policy", "conditional", "unchecked"):
        check(c[k] > 0, f"category {k} is reachable")
    # Pure canaries: the two ways a run could go quietly wrong.
    lost = classify(None, set(pol["known"]), set(pol["trusted"]))
    check(lost == {"classification": "unchecked", "unchecked_reasons": ["footprint-not-computed"]},
          "a theorem whose footprint was not computed is unchecked, never approved")
    unbound = {"invariants": [], "cross_checks": [], "axiom_ledger": {"verdict": "OK", "lean_exit_code": 0},
               "bound_to_head": False}
    check(verdict(unbound) == "UNBOUND" and not verdict_ok(unbound) and EXIT["UNBOUND"] != 0,
          "a ledger no commit names reads UNBOUND, never OK, and does not exit 0 by default")
    broken = dict(c, kernel_checked=c["kernel_checked"] + 1)
    check(not all(ok for _, ok in invariants(broken)), "a doctored kernel_checked count fails an invariant")
    check_canaries(check)
    print(f"THEOREM-LEDGER SELFTEST {'PASS' if not fails else 'FAIL'} -- {len(fails)} failure(s)")
    return 0 if not fails else 1


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--out", type=Path, help="write the ledger JSON (canonical, sorted keys) here")
    ap.add_argument("--check", type=Path, metavar="LEDGER", help="report whether LEDGER is still current")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--allow-unbound", action="store_true",
                    help="exit 0 for a ledger of a tree no commit names (check_all on a working tree); the headline "
                         "still says UNBOUND, and its counts are quotable nowhere")
    ap.add_argument("--cap", default=os.environ.get("MACHLIB_LEDGER_CAP", DEFAULT_CAP),
                    help=f"memory cap for each Lean run (default {DEFAULT_CAP})")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test(args.cap)
    if args.check:
        return cmd_check(args.check)
    return cmd_generate(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
