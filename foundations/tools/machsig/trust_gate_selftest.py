#!/usr/bin/env python3
"""Fault injection for the MachSig trust gate (DOCTRINE section 4: no green gate without a
demonstrated red path). Run through `trust_gate.py --selftest` / `--selftest-only`.

TWO PARTS, because the gate has two halves that fail differently.

A. THE DECISION, ON THE REAL SIGNATURE SET. A baseline is built in memory from the live set, then
   perturbed, and the gate's own `compare()` must convict exactly the perturbed theorems and name the
   axiom that entered. Includes a SWAP (one axiom out, another in, same count): the count rule this gate
   used until 2026-10-13 is run on the same input and must MISS it -- a known-answer test for why the
   ratchet now compares sets.

B. THE REFUSALS, END TO END. Each refusal is a property of the TREE (what is committed, what changed
   since extraction), so each is injected into a throwaway git repository built in a temp directory,
   holding a copy of this gate, identity.py and the extractor files (so the extractor digest is the
   real one). The copied gate runs as a subprocess and must exit with the right code, print EXACTLY ONE
   refusal tag (rule 4a: a gate that refuses everything is not discriminating), and name what moved.
   The fixture's unperturbed control must PASS, or every red result below would prove nothing.
   Case B4 is the blind spot of 2026-09-03..10-13 itself: a signature set extracted at one commit,
   read after a later commit changed a Lean source.

Nothing is written inside the real tree, so this is safe in check_all.sh's tree freeze.
"""
from __future__ import annotations

import copy
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import identity  # noqa: E402
import trust_gate as tg  # noqa: E402

TAG = re.compile(r"^MACHSIG-TRUST (?:REFUSED|UNAVAILABLE) \[([a-z-]+)\]", re.M)
PHANTOM = "MachSigSelftest.phantom_axiom"


def legacy_count_rule(base: dict, cur: dict) -> list[str]:
    """The comparison this gate made until 2026-10-13, verbatim in effect: count grew, digest same."""
    return [k for k in cur if k in base and cur[k]["d"] == base[k]["d"] and cur[k]["ax"] > base[k]["ax"]]


# ── Part A ─────────────────────────────────────────────────────────────────────────────────────────

def part_a() -> tuple[bool | None, list[str]]:
    lines = []
    if not tg.SIGS.is_file():
        return None, ["  [UNAVAILABLE] no real signature set; run tools/machsig/regen.py"]
    head, live, problem = tg.read_signature_set(tg.SIGS)
    if problem:
        return None, [f"  [UNAVAILABLE] the real signature set is unusable for injection: [{problem[0]}]"]
    base = {k: {"d": v["d"], "ax": v["ax"], "axioms": list(v["axioms"])} for k, v in live.items()}
    ok = True

    def check(cond: bool, text: str) -> None:
        nonlocal ok
        lines.append(f"  [{'ok' if cond else 'BROKEN'}] {text}")
        ok &= cond

    quiet = tg.compare(base, live)
    check(not quiet["acquired"], f"control: the live set against itself convicts nothing ({len(live)} theorems)")
    victims = [k for k in sorted(base) if base[k]["ax"] >= 4][:2]
    inj = copy.deepcopy(base)
    dropped = {}
    for k in victims:
        dropped[k] = inj[k]["axioms"][-1]
        inj[k]["axioms"] = inj[k]["axioms"][:-1]
        inj[k]["ax"] -= 1
    res = tg.compare(inj, live)
    names = {a["theorem"]: a["entered"] for a in res["acquired"]}
    check(set(names) == set(victims) and all(names[k] == [dropped[k]] for k in victims),
          f"INJECTED growth on {len(victims)} real theorems: exactly they are convicted, each naming the "
          f"axiom removed from its baseline ({', '.join(v.split('.')[-1] for v in victims)})")
    swap = victims[0]
    inj2 = copy.deepcopy(base)
    inj2[swap]["axioms"] = sorted(inj2[swap]["axioms"][1:] + [PHANTOM])   # same count, different set
    res2 = tg.compare(inj2, live)
    legacy = legacy_count_rule(inj2, live)
    check([a["theorem"] for a in res2["acquired"]] == [swap] and swap not in legacy,
          f"INJECTED swap on {swap.split('.')[-1]} (same count, one axiom exchanged): convicted by the set "
          f"rule, MISSED by the pre-2026-10-13 count rule (convicted {len(legacy)})")
    inj3 = copy.deepcopy(inj)
    for k in victims:
        inj3[k]["d"] = "0" * 32
    res3 = tg.compare(inj3, live)
    check(not res3["acquired"] and all(k in res3["restated"] for k in victims),
          "control: the same growth under a CHANGED statement is INFO, not a conviction")
    inj4 = copy.deepcopy(base)
    inj4[swap]["axioms"] = sorted(inj4[swap]["axioms"] + [PHANTOM])
    inj4[swap]["ax"] += 1
    res4 = tg.compare(inj4, live)
    check(not res4["acquired"] and res4["shrank"] == [swap], "control: a shrinking footprint stays green")
    return ok, lines


# ── Part B ─────────────────────────────────────────────────────────────────────────────────────────

GIT_ENV = {"GIT_AUTHOR_NAME": "machsig-selftest", "GIT_AUTHOR_EMAIL": "selftest@invalid",
           "GIT_COMMITTER_NAME": "machsig-selftest", "GIT_COMMITTER_EMAIL": "selftest@invalid",
           "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
COPIED = ("tools/machsig/trust_gate.py", "tools/machsig/trust_gate_selftest.py") + identity.EXTRACTOR_FILES
THEOREMS = {"Fx.alpha": ["Fx.ax_one", "propext"],
            "Fx.beta": ["Classical.choice", "Fx.ax_one", "Fx.ax_two", "Quot.sound", "propext"],
            "Fx.gamma": []}


def env() -> dict:
    e = {k: v for k, v in os.environ.items() if not k.startswith("GIT_")}
    e.update(GIT_ENV)
    return e


def sh(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-c", "commit.gpgsign=false", *args], cwd=repo, env=env(), check=True,
                   capture_output=True)


def write_sigs(found: Path, theorems: dict, header: bool = True) -> None:
    sys.path.insert(0, str(found / "tools" / "machsig"))
    import sig                                         # the real writer's provenance format
    live = identity.live_identity(found)
    ext = dict(live, lean_version="selftest", raw={})
    lines = []
    for name in sorted(theorems):
        axs = sorted(theorems[name])
        lines.append(json.dumps({"kind": "theorem", "object": name, "version": sig.VERSION,
                                 "StatementDigest": hashlib.sha256(name.encode()).hexdigest(),
                                 "TrustSig": f"AX{len(axs)}-S0", "TrustAxioms": axs}, sort_keys=True) + "\n")
    body = "".join(lines).encode()
    head = json.dumps(sig.provenance_record(ext, body, len(lines)), sort_keys=True) + "\n"
    (found / "artifacts").mkdir(exist_ok=True)
    (found / "artifacts" / "machsig_signatures.jsonl").write_bytes((head.encode() if header else b"") + body)


def build_fixture(root: Path, gate_text: str | None = None) -> Path:
    repo = root / "pristine"
    found = repo / "foundations"
    (found / "MachLib").mkdir(parents=True)
    (found / "MachLib" / "A.lean").write_text("theorem a : True := trivial\n")
    for f, txt in (("MachLib.lean", "import MachLib.A\n"), ("CertcomLibm.lean", "\n"),
                   ("lakefile.lean", "-- fixture\n"), ("lean-toolchain", "leanprover/lean4:v4.32.2\n"),
                   ("lake-manifest.json", "{}\n"), (".gitignore", "artifacts/\n__pycache__/\n")):
        (found / f).write_text(txt)
    real = HERE.parent.parent
    for rel in COPIED:
        (found / rel).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(real / rel, found / rel)
    if gate_text is not None:                          # --mutate: the fixture runs a mutant gate
        (found / "tools/machsig/trust_gate.py").write_text(gate_text)
    sh(repo, "init", "-q", "-b", "main")
    sh(repo, "add", "-A")
    sh(repo, "commit", "-q", "-m", "fixture")
    write_sigs(found, THEOREMS)
    rc = subprocess.run([sys.executable, str(found / "tools/machsig/trust_gate.py"), "--update"],
                        cwd=found, env=env(), capture_output=True, text=True)
    if rc.returncode != 0:
        raise RuntimeError(f"fixture --update failed: {rc.stdout}{rc.stderr}")
    (found / "docs").mkdir()
    (found / "docs" / "TRANSITION.md").write_text("fixture transition report\n")
    stamp(found, "REVIEWED")
    sh(repo, "add", "-A")
    sh(repo, "commit", "-q", "-m", "reviewed baseline")
    return repo


def stamp(found: Path, status: str) -> None:
    p = found / tg.BASE_REL
    b = json.loads(p.read_text())
    b["review"] = {"status": status, "reviewer": "selftest" if status == "REVIEWED" else None,
                   "transition_report": "docs/TRANSITION.md" if status == "REVIEWED" else None}
    p.write_text(tg.dump_baseline(b))


def run_gate(found: Path) -> tuple[int, str]:
    r = subprocess.run([sys.executable, str(found / "tools/machsig/trust_gate.py")], cwd=found, env=env(),
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def edit_baseline(found: Path, fn) -> None:
    p = found / tg.BASE_REL
    b = json.loads(p.read_text())
    fn(b)
    p.write_text(tg.dump_baseline(b))


def grow_alpha(b: dict) -> None:
    """Baseline says alpha rested on less: the live set now 'acquired' Fx.ax_one."""
    small = ["propext"]
    sid = tg.set_id(small)
    b["axiom_sets"][sid] = small
    b["theorems"]["Fx.alpha"] = dict(b["theorems"]["Fx.alpha"], ax=1, set=sid)


def commit_all(repo: Path, msg: str) -> None:
    sh(repo, "add", "-A")
    sh(repo, "commit", "-q", "-m", msg)


# (name, fault, expected rc, expected tag or None, text the output must contain)
def cases():
    def rm_sigs(repo, f): (f / "artifacts" / "machsig_signatures.jsonl").unlink()
    def rm_base(repo, f): sh(repo, "rm", "-q", "foundations/" + tg.BASE_REL); commit_all(repo, "rm")
    def legacy_sigs(repo, f): write_sigs(f, THEOREMS, header=False)
    def later_commit(repo, f):
        (f / "MachLib" / "A.lean").write_text("theorem a : True := by trivial\n")
        commit_all(repo, "a later source commit")
    def dirty_source(repo, f): (f / "MachLib" / "A.lean").write_text("theorem a : True := by exact trivial\n")
    def new_module(repo, f): (f / "MachLib" / "B.lean").write_text("theorem b : True := trivial\n")
    def extractor_edit(repo, f):
        p = f / "tools/machsig/sig.py"
        p.write_text(p.read_text() + "\n# extractor edited after extraction\n")
        commit_all(repo, "extractor edit")
    def untrack(repo, f):
        # `git add -A` would re-add it, so commit the index as it stands: the file stays on disk, untracked
        sh(repo, "rm", "-q", "--cached", "foundations/" + tg.BASE_REL)
        sh(repo, "commit", "-q", "-m", "untrack the baseline")
    def modify(repo, f): edit_baseline(f, grow_alpha)
    def stage(repo, f): edit_baseline(f, grow_alpha); sh(repo, "add", "foundations/" + tg.BASE_REL)
    def legacy_base(repo, f):
        (f / tg.BASE_REL).write_text(json.dumps({k: {"ax": len(v), "d": "0" * 32} for k, v in THEOREMS.items()}))
        commit_all(repo, "legacy baseline")
    def unresolvable(repo, f):
        edit_baseline(f, lambda b: b["provenance"].update(machlib_commit="0" * 40)); commit_all(repo, "x")
    def malformed(repo, f):
        edit_baseline(f, lambda b: b["theorems"]["Fx.beta"].update(ax=99)); commit_all(repo, "x")
    def extractor_mismatch(repo, f):
        edit_baseline(f, lambda b: b["provenance"].update(extractor_digest="sha256:" + "1" * 64))
        commit_all(repo, "x")
    def unreviewed(repo, f): stamp(f, "UNREVIEWED"); commit_all(repo, "x")
    def truncate(repo, f):
        p = f / "artifacts" / "machsig_signatures.jsonl"
        p.write_bytes(b"".join(p.read_bytes().splitlines(keepends=True)[:-1]))
    def growth(repo, f): edit_baseline(f, grow_alpha); commit_all(repo, "baseline with a smaller alpha")
    def swap(repo, f):
        def fn(b):
            # live beta rests on Fx.ax_one; the baseline says Fx.ax_three instead -- five axioms either way
            s = sorted(a for a in THEOREMS["Fx.beta"] if a != "Fx.ax_one") + ["Fx.ax_three"]
            s = sorted(s)
            sid = tg.set_id(s)
            b["axiom_sets"][sid] = s
            b["theorems"]["Fx.beta"] = dict(b["theorems"]["Fx.beta"], set=sid)
        edit_baseline(f, fn); commit_all(repo, "baseline with a swapped beta")
    return [
        ("B1 signature set missing", rm_sigs, 2, "no-signature-set", "regen.py"),
        ("B2 baseline missing", rm_base, 2, "no-baseline", tg.BASE_REL),
        ("B3 legacy signature set, no identity", legacy_sigs, 3, "signatures-unidentified", "no source identity"),
        ("B4 THE BLIND SPOT: set extracted, then a later commit changed a Lean source", later_commit, 3,
         "signatures-stale", "MachLib/A.lean"),
        ("B5 uncommitted edit to a Lean source", dirty_source, 3, "signatures-stale", "MachLib/A.lean"),
        ("B6 new untracked Lean module", new_module, 3, "signatures-stale", "MachLib/B.lean"),
        ("B7 extractor edited after extraction", extractor_edit, 3, "signatures-stale-extractor",
         "tools/machsig/sig.py"),
        ("B8 truncated signature set", truncate, 3, "signatures-corrupt", "truncated"),
        ("B9 baseline untracked", untrack, 3, "baseline-untracked", "not committed"),
        ("B10 baseline modified, unstaged", modify, 3, "baseline-modified", "differs from the committed"),
        ("B11 baseline modified, staged", stage, 3, "baseline-modified", "differs from the committed"),
        ("B12 committed baseline without provenance (the 2026-09-03 format)", legacy_base, 3,
         "baseline-provenance-absent", "no provenance"),
        ("B13 provenance names a commit the repo lacks", unresolvable, 3, "baseline-provenance-unresolvable",
         "000000000000"),
        ("B14 baseline entry contradicts itself", malformed, 3, "baseline-malformed", "Fx.beta"),
        ("B15 baseline from another extractor", extractor_mismatch, 3, "extractor-mismatch", "across extractors"),
        ("B16 baseline never reviewed", unreviewed, 3, "baseline-unreviewed", "'UNREVIEWED'"),
        ("B17 an axiom entered an unchanged statement", growth, 1, None, "Fx.alpha  1 -> 2  entered Fx.ax_one"),
        ("B18 swap: same count, different axiom", swap, 1, None, "Fx.beta  5 -> 5  entered Fx.ax_one"),
    ]


def part_b(gate_text: str | None = None) -> tuple[bool, list[str]]:
    lines, ok = [], True
    with tempfile.TemporaryDirectory(prefix="machsig-selftest-") as td:
        td = Path(td)
        try:
            pristine = build_fixture(td, gate_text)
        except (subprocess.CalledProcessError, RuntimeError, identity.Unavailable) as e:
            return False, [f"  [BROKEN] could not build the fixture repository: {e}"]
        work = td / "case"
        shutil.copytree(pristine, work, symlinks=True)
        rc, out = run_gate(work / "foundations")
        control = rc == 0 and "MACHSIG-TRUST OK" in out and not TAG.search(out)
        lines.append(f"  [{'ok' if control else 'BROKEN'}] B0 control: fresh set, reviewed committed baseline "
                     f"-> OK (rc {rc})")
        ok &= control
        if not control:
            lines.append("        " + out.strip().replace("\n", "\n        ")[:1500])
        for name, fault, want_rc, want_tag, want_text in cases():
            shutil.rmtree(work)
            shutil.copytree(pristine, work, symlinks=True)
            try:
                fault(work, work / "foundations")
            except (subprocess.CalledProcessError, OSError) as e:
                lines.append(f"  [BROKEN] {name}: the fault could not be injected ({e})")
                ok = False
                continue
            rc, out = run_gate(work / "foundations")
            tags = TAG.findall(out)
            good = rc == want_rc and (tags == [want_tag] if want_tag else not tags) and want_text in out
            lines.append(f"  [{'ok' if good else 'BROKEN'}] {name} -> rc {rc}"
                         f"{', [' + tags[0] + ']' if len(tags) == 1 else (', tags ' + str(tags) if tags else '')}")
            if not good:
                lines.append(f"        expected rc {want_rc}, tag {want_tag}, text {want_text!r}; got:")
                lines.append("        " + out.strip().replace("\n", "\n        ")[:1500])
            ok &= good
    return ok, lines


# DOCTRINE 4b: fault injection validates the gate; MUTATION validates the selftest. Each mutant disables
# one decision in a COPY of the gate (only inside the throwaway fixture) and Part B must then go red.
# A mutant whose anchor no longer occurs exactly once is STALE ("the test is broken"), never MISSED.
MUTANTS = [
    ("content staleness check removed",
     'if head.get("content_digest") != live["content_digest"]:', "if False:"),
    ("extractor staleness check removed",
     'if head.get("extractor_digest") != live["extractor_digest"]:', "if False:"),
    ("record digest/count check removed",
     'if digest != head.get("records_sha256") or n != head.get("records"):', "if False:"),
    ("untracked-baseline check removed",
     'if not identity.git_ok(root, "ls-files", "--error-unmatch", "--", BASE_REL):', "if False:"),
    ("modified-baseline check removed", "    if st.strip():", "    if False:"),
    ("provenance-commit resolution removed",
     'if not identity.git_ok(root, "cat-file", "-e", f"{prov[\'machlib_commit\']}^{{commit}}"):', "if False:"),
    ("extractor-mismatch check removed",
     'and prov["extractor_digest"] != head.get("extractor_digest"):', "and False:"),
    ("review check removed",
     'if r.get("status") != "REVIEWED" or not r.get("reviewer") or not rep or not (root / str(rep)).is_file():',
     "if False:"),
    ("set ratchet weakened to the pre-2026-10-13 count rule", "        if entered:",
     '        if v["ax"] > b["ax"]:'),
    ("stale refusal stops naming what moved",
     "Moved: {', '.join(moved) or '(file list unavailable)'}", "Moved: (not named)"),
    ("self-contradicting baseline entries accepted",
     'if axs is None or len(axs) != e.get("ax") or not isinstance(e.get("d"), str):', "if axs is None:"),
]


def mutate() -> int:
    src = (HERE / "trust_gate.py").read_text()
    print("=== MACHSIG-TRUST MUTATION TEST: each mutant must turn Part B red ===")
    bad = 0
    for name, anchor, repl in MUTANTS:
        if src.count(anchor) != 1:
            print(f"  [STALE ] {name} -- anchor occurs {src.count(anchor)} times; the TEST is broken")
            bad += 1
            continue
        ok, lines = part_b(src.replace(anchor, repl, 1))
        broken = [ln.strip() for ln in lines if ln.startswith("  [BROKEN]")]
        print(f"  [{'KILLED' if not ok else 'MISSED'}] {name}"
              f"{' -- caught by ' + broken[0].split(' -> ')[0][9:] if broken else ''}")
        bad += ok
    print(f"  MUTATION {'PASS' if not bad else 'FAIL'} -- {len(MUTANTS) - bad}/{len(MUTANTS)} killed")
    return tg.OK if not bad else tg.FAIL


def run() -> int:
    print("=== MACHSIG-TRUST SELFTEST (fault injection) ===")
    print("Part A — the decision, on the REAL signature set")
    a_ok, a_lines = part_a()
    print("\n".join(a_lines))
    print("Part B — the refusals, end to end in a throwaway git repository")
    b_ok, b_lines = part_b()
    print("\n".join(b_lines))
    n_b = sum(1 for ln in b_lines if ln.startswith("  [")) - 1
    if a_ok is False or not b_ok:
        print("  SELFTEST FAIL — a red path did not fire as specified, or a control fired")
        return tg.FAIL
    if a_ok is None:
        print(f"  SELFTEST UNAVAILABLE — Part B passed ({n_b} injected faults + control); Part A needs a "
              "readable real signature set")
        return tg.UNAVAILABLE
    print(f"  SELFTEST PASS — Part A: 3 injections + 2 controls on the real set; Part B: {n_b} injected "
          "faults + 1 control")
    return tg.OK


if __name__ == "__main__":
    sys.exit(mutate() if "--mutate" in sys.argv else run())
