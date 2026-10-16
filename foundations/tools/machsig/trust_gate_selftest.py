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
   read after a later commit changed a Lean source. Cases B23-B31 are the attacks of the independent
   review of 2026-10-13 that PASSED against the gate of b6ad5d05 (stamp pasted onto an --update,
   lakefile.lean as the "transition report", a restatement laundering sorryAx, a theorem leaving the
   watched set), each now red. A fault that must edit the committed baseline is RESTAMPED with a
   correct binding first (`edit_restamp`), so the refusal it triggers is the one it is about.

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
    head, cur, problem = tg.read_signature_set(tg.SIGS)
    if problem:
        return None, [f"  [UNAVAILABLE] the real signature set is unusable for injection: [{problem[0]}]"]
    live = cur["theorems"]
    base = {k: {"d": v["d"], "c": v["c"], "ax": v["ax"], "axioms": list(v["axioms"])} for k, v in live.items()}
    ok = True

    def check(cond: bool, text: str) -> None:
        nonlocal ok
        lines.append(f"  [{'ok' if cond else 'BROKEN'}] {text}")
        ok &= cond

    def convictions(res):
        return [k for k, _ in tg.CONVICTIONS if res.get(k)]

    quiet = tg.compare(base, live)
    check(not convictions(quiet), f"control: the live set against itself convicts nothing ({len(live)} theorems)")
    bad0 = {x["theorem"] for x in tg.policy_violations(live, cur["policy"])}
    victims = [k for k in sorted(base) if base[k]["ax"] >= 4 and k not in bad0][:2]
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
    rs = {r["theorem"]: r["entered"] for r in res3["restated"]}
    check(convictions(res3) == ["restated"] and set(rs) == set(victims) and all(rs[k] == [dropped[k]] for k in victims),
          "INJECTED growth under a CHANGED statement (attack 5): convicted as `restated`, naming the axiom "
          "that entered -- it was INFO until 2026-10-13")
    gone = victims[1]
    live6 = {k: v for k, v in live.items() if k != gone}
    res6 = tg.compare(base, live6)
    check(convictions(res6) == ["removed"] and res6["removed"] == [gone],
          f"INJECTED removal of {gone.split('.')[-1]} (attack 6): convicted as `removed`")
    inj4 = copy.deepcopy(base)
    inj4[swap]["axioms"] = sorted(inj4[swap]["axioms"] + [PHANTOM])
    inj4[swap]["ax"] += 1
    res4 = tg.compare(inj4, live)
    check(not convictions(res4) and res4["shrank"] == [swap], "control: a shrinking footprint stays green")
    inj5 = {k: v for k, v in base.items() if k != swap}
    res5 = tg.compare(inj5, live)
    check(not convictions(res5) and res5["new"] == [swap], "control: a new theorem on declared axioms stays green")

    # v0.4: the whole judgement, on the real set and the real declared policy
    whole = {"theorems": base, "axioms": dict(cur["axioms"]), "policy": copy.deepcopy(cur["policy"])}
    # A policy violation is a property of the SUBJECT, not of a baseline: if the real set already has
    # some, the gate will FAIL them, and the controls below must not be confused by them (DOCTRINE 4b:
    # an already-red subject is reported, not used to convict the selftest's own controls).
    v0 = {x["theorem"] for x in tg.policy_violations(cur["theorems"], cur["policy"])}
    if v0:
        lines.append(f"  [note] the real set already violates the declared policy in {len(v0)} theorem(s), first "
                     f"{sorted(v0)[0]}: the gate FAILS them; the controls below set them aside")

    def judged(res):
        return [k for k in convictions(res) if not (k == "policy-violation" and
                                                    {x["theorem"] for x in res[k]} <= v0)]
    ctl = tg.judge(whole, cur)
    check(not judged(ctl), f"control: the real set judged against itself: no conviction"
                           f"{', no policy violation' if not v0 else ' beyond the pre-existing violations'} "
                           f"({len(cur['axioms'])} axioms pinned, allowlisted sorry {cur['policy']['allowed_sorry']})")
    inj7 = copy.deepcopy(whole)
    inj7["theorems"][swap]["c"] = "0" * 64
    r7 = tg.judge(inj7, cur)
    check(judged(r7) == ["redefined"] and [x["theorem"] for x in r7["redefined"]] == [swap],
          f"INJECTED definition change under {swap.split('.')[-1]} (E3, clamp): convicted as `redefined`")
    ax = sorted(a for a in cur["axioms"] if a.startswith(("MachLib", "Certcom")))[0]
    inj8 = copy.deepcopy(whole)
    inj8["axioms"][ax] = "0" * 64
    r8 = tg.judge(inj8, cur)
    check(judged(r8) == ["axiom-restated"] and r8["axiom-restated"] == [ax],
          f"INJECTED restatement of axiom {ax.split('.')[-1]} under its own name: convicted as `axiom-restated`")
    cur9 = copy.deepcopy(cur)
    cur9["theorems"][swap]["axioms"] = sorted(cur9["theorems"][swap]["axioms"] + [tg.SORRY])
    inj9 = copy.deepcopy(whole)
    inj9["theorems"][swap]["axioms"] = list(cur9["theorems"][swap]["axioms"])   # grandfathered in the baseline
    r9 = tg.judge(inj9, cur9)
    check(judged(r9) == ["policy-violation"] and {x["theorem"] for x in r9["policy-violation"]} == v0 | {swap},
          "INJECTED sorryAx into a theorem the baseline already holds that way: `policy-violation` anyway")
    promoted = "MachLib.Real.pi_lower_bound" if "MachLib.Real.pi_lower_bound" in cur["policy"]["trusted"] \
        else cur["policy"]["trusted"][-1]                                  # E1's own axiom when present
    inj10 = copy.deepcopy(whole)
    inj10["policy"]["trusted"] = [a for a in inj10["policy"]["trusted"] if a != promoted]
    r10 = tg.judge(inj10, cur)
    check(judged(r10) == ["policy-widened"] and r10["policy-widened"] == [f"trustedFootprint + {promoted}"],
          f"INJECTED promotion of {promoted.split('.')[-1]} into trustedFootprint (E1/E2): `policy-widened`")
    return ok, lines


# ── Part B ─────────────────────────────────────────────────────────────────────────────────────────

GIT_ENV = {"GIT_AUTHOR_NAME": "machsig-selftest", "GIT_AUTHOR_EMAIL": "selftest@invalid",
           "GIT_COMMITTER_NAME": "machsig-selftest", "GIT_COMMITTER_EMAIL": "selftest@invalid",
           "GIT_CONFIG_GLOBAL": os.devnull, "GIT_CONFIG_NOSYSTEM": "1"}
COPIED = ("tools/machsig/trust_gate.py", "tools/machsig/trust_gate_selftest.py") + identity.EXTRACTOR_FILES
THEOREMS = {"Fx.alpha": ["Fx.ax_one", "propext"],
            "Fx.beta": ["Classical.choice", "Fx.ax_one", "Fx.ax_two", "Quot.sound", "propext"],
            "Fx.gamma": ["sorryAx"]}                       # allowlisted below, like halve_in_unit_sorry
#: the fixture's counts-only pre-review origin (same statement digests write_sigs gives)
LEGACY = {k: {"ax": len(v), "d": hashlib.sha256(k.encode()).hexdigest()[:32]} for k, v in THEOREMS.items()}
AXIOMS = {a: hashlib.sha256(("stmt:" + a).encode()).hexdigest()
          for a in ("Classical.choice", "Quot.sound", "propext", "sorryAx", "Fx.ax_one", "Fx.ax_two", "Fx.ax_three")}
POLICY = {"known": ["Fx.ax_one", "Fx.ax_three", "Fx.ax_two"],
          "trusted": ["Classical.choice", "Fx.ax_one", "Fx.ax_two", "Quot.sound", "propext"],
          "allowed_sorry": ["Fx.gamma"]}


def env(extra: dict | None = None) -> dict:
    # MACHSIG_RUN_ID is dropped: check_all.sh exports it for the REAL set, not for these fixtures
    e = {k: v for k, v in os.environ.items() if not k.startswith("GIT_") and k != "MACHSIG_RUN_ID"}
    e.update(GIT_ENV)
    e.update(extra or {})
    return e


def sh(repo: Path, *args: str) -> None:
    subprocess.run(["git", "-c", "commit.gpgsign=false", *args], cwd=repo, env=env(), check=True,
                   capture_output=True)


SIG_VERSION = "MachSig/v0.4-wide"
LEAN_V = "Lean (version 4.32.2, aarch64-unknown-linux-gnu, commit f3b06c705e6c, Release)"


def provenance_record(ext: dict, body: bytes, n: int) -> dict:
    """sig.py's provenance header, rebuilt from its documented fields (SIGNATURE_SPEC v0.3/v0.4)."""
    keep = ("machlib_commit", "machlib_sources", "sources_clean", "dirty_source_paths", "content_digest",
            "content_files", "extractor_digest", "extractor_files", "lean_toolchain", "lean_version", "raw",
            "policy", "run_id")
    rec = {k: ext[k] for k in keep}
    rec.update({"kind": identity.PROVENANCE_KIND, "schema": identity.PROVENANCE_SCHEMA, "version": SIG_VERSION,
                "records": n, "records_sha256": "sha256:" + hashlib.sha256(body).hexdigest()})
    return rec


def write_sigs(found: Path, theorems: dict, header: bool = True, digests: dict | None = None,
               closures: dict | None = None, axioms: dict | None = None, policy: dict | None = None,
               run_id: str | None = None, lean_version: str = LEAN_V) -> None:
    """A synthetic v0.4 signature set with the real writer's provenance header. `digests` / `closures`
    perturb a theorem's StatementDigest / DefClosureDigest by name; `axioms` / `policy` replace the pins
    and the declared policy."""
    # The provenance header is built HERE, not by importing the tree's sig.py: the selftest is part of
    # the judge, and the judge imports nothing from a tree (the third review's json.py/sig.py routes).
    live = identity.live_identity(found)
    ext = dict(live, lean_version=lean_version, raw={}, policy=policy or POLICY, run_id=run_id)
    records = {}
    for name in theorems:
        axs = sorted(theorems[name])
        records[name] = {"kind": "theorem", "object": name, "version": SIG_VERSION,
                         "StatementDigest": hashlib.sha256((name + (digests or {}).get(name, "")).encode()).hexdigest(),
                         "DefClosureDigest": hashlib.sha256(("c:" + name + (closures or {}).get(name, "")).encode()).hexdigest(),
                         "TrustSig": f"AX{len(axs)}-S0", "TrustAxioms": axs}
    for a, h in (axioms or AXIOMS).items():
        records[a] = {"kind": "axiom", "object": a, "version": SIG_VERSION, "AxiomStatementDigest": h}
    lines = [json.dumps(records[k], sort_keys=True) + "\n" for k in sorted(records)]
    body = "".join(lines).encode()
    head = json.dumps(provenance_record(ext, body, len(lines)), sort_keys=True) + "\n"
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
    # The fixture's own pre-review origin: a counts-only baseline committed first, as c3046961's is in
    # MachLib; the fixture's gate copy is pointed at it (ORIGIN_CONTENT is a constant of the gate).
    gp = found / "tools/machsig/trust_gate.py"
    gp.write_text(re.sub(r'^ORIGIN_CONTENT = ".*"$', f'ORIGIN_CONTENT = "{tg.baseline_content_digest(LEGACY)}"',
                         gp.read_text(), count=1, flags=re.M))
    (found / tg.BASE_REL).write_text(json.dumps(LEGACY, sort_keys=True, indent=0))
    sh(repo, "init", "-q", "-b", "main")
    sh(repo, "add", "-A")
    sh(repo, "commit", "-q", "-m", "fixture, with the counts-only origin baseline")
    origin = subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, env=env(), capture_output=True, text=True,
                            check=True).stdout.strip()
    gp.write_text(re.sub(r'^ORIGIN_COMMIT = ".*"$', f'ORIGIN_COMMIT = "{origin}"', gp.read_text(), count=1,
                         flags=re.M))
    write_sigs(found, THEOREMS)
    rc = subprocess.run([sys.executable, str(found / "tools/machsig/trust_gate.py"), "--update"],
                        cwd=found, env=env(), capture_output=True, text=True)
    if rc.returncode != 0:
        raise RuntimeError(f"fixture --update failed: {rc.stdout}{rc.stderr}")
    (found / "docs").mkdir()
    restamp(found, previous=LEGACY)
    sh(repo, "add", "-A")
    sh(repo, "commit", "-q", "-m", "reviewed baseline")
    return repo


REPORT = "docs/transition.json"


def restamp(found: Path, previous, report: dict | None = None, reviewer: str = "selftest") -> None:
    """A REVIEWED stamp bound to the baseline's content, citing a transition report. By default the
    report is CORRECT: binding (previous -> this) and gate_transition recomputed between them, where
    `previous` is the last reviewed baseline (a parsed dict). `report` replaces it wholesale (attacks)."""
    p = found / tg.BASE_REL
    b = json.loads(p.read_text())
    mine = tg.baseline_content_digest(b)
    if report is None:
        report = {"schema": "machsig-transition/v3",
                  "binding": {"old_baseline_sha256": tg.baseline_content_digest(previous), "new_baseline_sha256": mine},
                  "gate_transition": tg.gate_transition(previous, b)}
    (found / REPORT).parent.mkdir(parents=True, exist_ok=True)
    (found / REPORT).write_text(json.dumps(report, sort_keys=True) + "\n")
    b["review"] = {"status": "REVIEWED", "reviewer": reviewer, "transition_report": REPORT, "baseline_sha256": mine}
    p.write_text(tg.dump_baseline(b))


def run_gate(found: Path, extra: dict | None = None) -> tuple[int, str]:
    """A fault may return env vars, plus `__args__` (extra gate arguments) and `__judge__` (a directory
    holding a copy of the gate: run it ISOLATED, `python3 -I -S`, from outside the tree, with --tree)."""
    extra = dict(extra or {})
    args = extra.pop("__args__", [])
    judge = extra.pop("__judge__", None)
    if judge:
        cmd = [sys.executable, "-I", "-S", str(Path(judge) / "tools/machsig/trust_gate.py"), "--tree", str(found)]
    else:
        cmd = [sys.executable, str(found / "tools/machsig/trust_gate.py")]
    r = subprocess.run(cmd + args, cwd=found, env=env(extra), capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def edit_baseline(found: Path, fn) -> None:
    p = found / tg.BASE_REL
    b = json.loads(p.read_text())
    fn(b)
    p.write_text(tg.dump_baseline(b))


def edit_restamp(repo: Path, found: Path, fn, msg: str) -> None:
    """Edit the baseline's CONTENT, restamp it as a properly reviewed rebaseline, commit. Without the
    restamp every content fault would also trip [review-unbound] and the case would test two things."""
    previous = json.loads((found / tg.BASE_REL).read_text())
    edit_baseline(found, fn)
    restamp(found, previous)
    commit_all(repo, msg)


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
        edit_restamp(repo, f, lambda b: b["provenance"].update(machlib_commit="0" * 40), "x")
    def malformed(repo, f):
        edit_restamp(repo, f, lambda b: b["theorems"]["Fx.beta"].update(ax=99), "x")
    def extractor_mismatch(repo, f):
        edit_restamp(repo, f, lambda b: b["provenance"].update(extractor_digest="sha256:" + "1" * 64), "x")
    def unreviewed(repo, f):
        # ONLY the status is wrong: reviewer and report stay valid, so no other reason can mask it
        edit_baseline(f, lambda b: b["review"].update(status="UNREVIEWED")); commit_all(repo, "x")
    def no_reviewer(repo, f):
        edit_baseline(f, lambda b: b["review"].update(reviewer="")); commit_all(repo, "x")
    def truncate(repo, f):
        p = f / "artifacts" / "machsig_signatures.jsonl"
        p.write_bytes(b"".join(p.read_bytes().splitlines(keepends=True)[:-1]))
    def growth(repo, f): edit_restamp(repo, f, grow_alpha, "baseline with a smaller alpha")
    def report_outside(repo, f):
        # Path(root) / "/abs" is "/abs": this file exists on any machine, so the stamp would pass
        edit_baseline(f, lambda b: b["review"].update(transition_report=str(Path(sys.executable).resolve())))
        commit_all(repo, "stamp cites an absolute path")
    def report_untracked(repo, f):
        edit_baseline(f, lambda b: b["review"].update(transition_report="docs/UNCOMMITTED.md"))
        commit_all(repo, "stamp cites a report that is not committed")
        (f / "docs" / "UNCOMMITTED.md").write_text("never committed\n")
    def duplicate(repo, f):
        p = f / "artifacts" / "machsig_signatures.jsonl"
        lines = p.read_bytes().splitlines(keepends=True)
        alpha = next(ln for ln in lines if b'"Fx.alpha"' in ln)
        small = json.loads(alpha)
        small["TrustAxioms"], small["TrustSig"] = ["propext"], "AX1-S0"
        body = b"".join(lines[1:]) + (json.dumps(small, sort_keys=True) + "\n").encode()
        head = json.loads(lines[0])
        head["records"] = len(lines)
        head["records_sha256"] = "sha256:" + hashlib.sha256(body).hexdigest()
        p.write_bytes((json.dumps(head, sort_keys=True) + "\n").encode() + body)
    def swap(repo, f):
        def fn(b):
            # live beta rests on Fx.ax_one; the baseline says Fx.ax_three instead -- five axioms either way
            s = sorted(a for a in THEOREMS["Fx.beta"] if a != "Fx.ax_one") + ["Fx.ax_three"]
            s = sorted(s)
            sid = tg.set_id(s)
            b["axiom_sets"][sid] = s
            b["theorems"]["Fx.beta"] = dict(b["theorems"]["Fx.beta"], set=sid)
        edit_restamp(repo, f, fn, "baseline with a swapped beta")
    def paste_old_stamp(repo, f):
        # Attack 3: sorryAx enters alpha; --update rebaselines; the old REVIEWED block is pasted back
        old_review = json.loads((f / tg.BASE_REL).read_text())["review"]
        write_sigs(f, dict(THEOREMS, **{"Fx.alpha": THEOREMS["Fx.alpha"] + ["sorryAx"]}))
        subprocess.run([sys.executable, str(f / "tools/machsig/trust_gate.py"), "--update"], cwd=f, env=env(),
                       capture_output=True, check=True)
        edit_baseline(f, lambda b: b.update(review=old_review))
        commit_all(repo, "rebaseline, old stamp pasted")
    def lakefile_report(repo, f):
        # Attack 4: reviewer "x", any committed file as the report (stamp otherwise correctly bound)
        edit_baseline(f, lambda b: b["review"].update(reviewer="x", transition_report="lakefile.lean"))
        commit_all(repo, "x")
    def json_not_report(repo, f):
        edit_baseline(f, lambda b: b["review"].update(transition_report="lake-manifest.json"))
        commit_all(repo, "x")
    def report_wrong_new(repo, f):
        rep = json.loads((f / REPORT).read_text())
        rep["binding"]["new_baseline_sha256"] = "sha256:" + "2" * 64
        (f / REPORT).write_text(json.dumps(rep, sort_keys=True) + "\n")
        commit_all(repo, "a report for some other baseline")
    def report_wrong_old(repo, f):
        rep = json.loads((f / REPORT).read_text())
        rep["binding"]["old_baseline_sha256"] = "sha256:" + "3" * 64
        (f / REPORT).write_text(json.dumps(rep, sort_keys=True) + "\n")
        commit_all(repo, "a report against the wrong predecessor")
    def restate_sorry(repo, f):
        # Attack 5: alpha's statement changes AND sorryAx enters; it used to read as "restated" (INFO)
        write_sigs(f, dict(THEOREMS, **{"Fx.alpha": THEOREMS["Fx.alpha"] + ["sorryAx"]}),
                   digests={"Fx.alpha": "restated"})
    def restate_only(repo, f):
        write_sigs(f, THEOREMS, digests={"Fx.alpha": "restated"})
    def remove(repo, f):
        # Attack 6: a watched theorem leaves the set (deleted, renamed into a filter, made private...)
        write_sigs(f, {k: v for k, v in THEOREMS.items() if k != "Fx.gamma"})
    def add_new(repo, f):
        write_sigs(f, dict(THEOREMS, **{"Fx.delta": ["propext"]}))
    def sorry_new(repo, f):
        write_sigs(f, dict(THEOREMS, **{"Fx.delta": ["propext", "sorryAx"]}))
    def native_new(repo, f):
        # DECLARED in knownAxioms, so only the compiler-trust rule can catch it (as theorem_ledger does)
        nat = "Fx.delta._native.native_decide.ax_1_1"
        write_sigs(f, dict(THEOREMS, **{"Fx.delta": [nat]}), policy=dict(POLICY, known=sorted(POLICY["known"] + [nat])),
                   axioms=dict(AXIOMS, **{nat: hashlib.sha256(nat.encode()).hexdigest()}))
    def undeclared_grandfathered(repo, f):
        # the baseline itself holds the undeclared axiom: no baseline can make it pass
        previous = json.loads((f / tg.BASE_REL).read_text())
        ths = dict(THEOREMS, **{"Fx.beta": THEOREMS["Fx.beta"] + ["Fx.undeclared"]})
        write_sigs(f, ths)
        subprocess.run([sys.executable, str(f / "tools/machsig/trust_gate.py"), "--update"], cwd=f, env=env(),
                       capture_output=True, check=True)
        restamp(f, previous)
        commit_all(repo, "a reviewed baseline that holds an undeclared axiom")
    def axiom_restated(repo, f):
        write_sigs(f, THEOREMS, axioms=dict(AXIOMS, **{"Fx.ax_one": hashlib.sha256(b"restated").hexdigest()}))
    def redefined(repo, f):
        write_sigs(f, THEOREMS, closures={"Fx.alpha": "clamp redefined"})
    def promoted(repo, f):
        write_sigs(f, THEOREMS, policy=dict(POLICY, trusted=sorted(POLICY["trusted"] + ["Fx.ax_three"])))
    def sorry_allowlisted(repo, f):
        write_sigs(f, THEOREMS, policy=dict(POLICY, allowed_sorry=["Fx.alpha", "Fx.gamma"]))
    def other_run(repo, f):
        write_sigs(f, THEOREMS, run_id="run-A")
        return {"MACHSIG_RUN_ID": "run-B"}
    def same_run(repo, f):
        write_sigs(f, THEOREMS, run_id="run-A")
        return {"MACHSIG_RUN_ID": "run-A"}
    def committed(f):
        return json.loads((f / tg.BASE_REL).read_text())
    def update(f):
        subprocess.run([sys.executable, str(f / "tools/machsig/trust_gate.py"), "--update"], cwd=f, env=env(),
                       capture_output=True, check=True)
    GROWN = dict(THEOREMS, **{"Fx.alpha": THEOREMS["Fx.alpha"] + ["Fx.ax_two"]})   # a trusted axiom enters
    SHRUNK = dict(GROWN, **{"Fx.beta": [a for a in THEOREMS["Fx.beta"] if a != "Quot.sound"]})
    def grow_unreviewed(repo, f):
        # commit 1 of H1: a real growth, rebaselined by --update and committed UNREVIEWED
        write_sigs(f, GROWN)
        update(f)
        commit_all(repo, "rebaseline after a growth (unreviewed)")
        return committed(f)
    def h1_exact(repo, f):
        # the second review's attack, verbatim: commit 2 stamps it with a 4-line "this -> itself" report
        d = tg.baseline_content_digest(grow_unreviewed(repo, f))
        restamp(f, None, report={"schema": "machsig-transition/v2",
                                 "binding": {"old_baseline_sha256": d, "new_baseline_sha256": d}}, reviewer="x")
        commit_all(repo, "stamp")
    def h1_v3_hollow_self(repo, f):
        # the same, but shaped like a v3 report: self-binding with the (empty) recompute D -> D
        b = grow_unreviewed(repo, f)
        d = tg.baseline_content_digest(b)
        restamp(f, None, report={"schema": "machsig-transition/v3",
                                 "binding": {"old_baseline_sha256": d, "new_baseline_sha256": d},
                                 "gate_transition": tg.gate_transition(b, b)})
        commit_all(repo, "stamp")
    def h1_self_with_rows(repo, f):
        # self-binding that even carries the true rows: still not a transition FROM the last review
        pristine = committed(f)
        b = grow_unreviewed(repo, f)
        d = tg.baseline_content_digest(b)
        restamp(f, None, report={"schema": "machsig-transition/v3",
                                 "binding": {"old_baseline_sha256": d, "new_baseline_sha256": d},
                                 "gate_transition": tg.gate_transition(pristine, b)})
        commit_all(repo, "stamp")
    def h1_hollow_rows(repo, f):
        # correct binding (last reviewed -> this), but rows that omit the growth
        pristine = committed(f)
        b = grow_unreviewed(repo, f)
        hollow = tg.gate_transition(pristine, pristine)
        restamp(f, None, report={"schema": "machsig-transition/v3",
                                 "binding": {"old_baseline_sha256": tg.baseline_content_digest(pristine),
                                             "new_baseline_sha256": tg.baseline_content_digest(b)},
                                 "gate_transition": hollow})
        commit_all(repo, "stamp with a hollow report")
    def h1_three_commits(repo, f):
        # c1 unreviewed growth; c2 a stamp whose report is self-bound (invalid); c3 a further change
        # stamped with an HONEST report from c2 -- c2 must not count as reviewed
        b1 = grow_unreviewed(repo, f)
        d1 = tg.baseline_content_digest(b1)
        restamp(f, None, report={"schema": "machsig-transition/v3",
                                 "binding": {"old_baseline_sha256": d1, "new_baseline_sha256": d1},
                                 "gate_transition": tg.gate_transition(b1, b1)})
        commit_all(repo, "c2: stamped, self-bound")
        b2 = committed(f)
        write_sigs(f, SHRUNK)
        update(f)
        restamp(f, b2)
        commit_all(repo, "c3: honest report from c2")
    def h1_intermediate(repo, f):
        # c1 unreviewed growth; c2 a further change stamped with an honest report FROM c1
        b1 = grow_unreviewed(repo, f)
        write_sigs(f, SHRUNK)
        update(f)
        restamp(f, b1)
        commit_all(repo, "c2: report from the unreviewed c1")
    def honest_two_step(repo, f):
        # control: c1 unreviewed --update; c2 stamps it with a report from the last REVIEWED baseline
        pristine = committed(f)
        grow_unreviewed(repo, f)
        restamp(f, pristine)
        commit_all(repo, "c2: reviewed, report from the last reviewed baseline")
    def honest_chain(repo, f):
        # two reviewed rebaselines committed straight on main, the second's report from the first. Since
        # the fifth review a plain commit's stamp never becomes a reference (in git this IS the two-hop
        # fast-forward), so the second must report from the last COUNTED baseline: refused
        pristine = committed(f)
        write_sigs(f, GROWN)
        update(f)
        restamp(f, pristine)
        commit_all(repo, "r1 reviewed")
        r1 = committed(f)
        write_sigs(f, SHRUNK)
        update(f)
        restamp(f, r1)
        commit_all(repo, "r2 reviewed, from r1")
    def head_sha(repo):
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=repo, env=env(), capture_output=True, text=True,
                              check=True).stdout.strip()
    def origin_sha(repo):
        return subprocess.run(["git", "rev-list", "--max-parents=0", "HEAD"], cwd=repo, env=env(),
                              capture_output=True, text=True, check=True).stdout.split()[0]
    def restart(repo, f):
        # RESTART (review 3): re-commit the counts-only origin (a "revert"), then rebaseline with a growth
        # and an honest report FROM THE ORIGIN -- the old walk restarted the chain at the last origin
        (f / tg.BASE_REL).write_text(json.dumps(LEGACY, sort_keys=True, indent=0))
        commit_all(repo, "revert the baseline to the counts-only origin")
        write_sigs(f, GROWN)
        update(f)
        restamp(f, LEGACY)
        commit_all(repo, "rebaseline from the origin")
    def recommit_older(repo, f, merged: bool = True):
        # re-commit an OLDER reviewed baseline (L1, with its own stamp and report) over a newer one (L2).
        # L2 arrives in a merge commit, so it is a counted reference; `merged=False` is the plain-commit
        # variant, where L2 never counted and L1 back is a net-zero step (the documented cost)
        l1_base, l1_rep = (f / tg.BASE_REL).read_text(), (f / REPORT).read_text()
        pristine = committed(f)
        if merged:
            sh(repo, "checkout", "-q", "-b", "l2")
        write_sigs(f, GROWN)
        update(f)
        restamp(f, pristine)
        commit_all(repo, "L2 reviewed from L1")
        if merged:
            sh(repo, "checkout", "-q", "main")
            sh(repo, "merge", "-q", "--no-ff", "--no-edit", "l2")
        write_sigs(f, THEOREMS)
        (f / tg.BASE_REL).write_text(l1_base)
        (f / REPORT).write_text(l1_rep)
        commit_all(repo, "put L1 back, stamp and report included")
    def recommit_older_plain(repo, f): recommit_older(repo, f, merged=False)
    def merge_attack(repo, f, side_first: bool):
        # MERGE (review 3): a branch forked BEFORE the first review rebaselines against the origin; it is
        # merged with the reviewed line and its file wins
        sh(repo, "checkout", "-q", "-b", "side", origin_sha(repo))
        write_sigs(f, GROWN)
        update(f)
        restamp(f, LEGACY)
        commit_all(repo, "side: rebaseline from the origin")
        if side_first:
            sh(repo, "merge", "-q", "--no-edit", "-X", "ours", "main")
        else:
            sh(repo, "checkout", "-q", "main")
            sh(repo, "merge", "-q", "--no-edit", "-X", "theirs", "side")
        write_sigs(f, GROWN)
    def merge_side_first(repo, f): merge_attack(repo, f, True)
    def merge_main_first(repo, f): merge_attack(repo, f, False)
    def honest_merge(repo, f):
        # control: a branch forked AFTER the review, reviewed from it, merged with --no-ff
        pristine = committed(f)
        sh(repo, "checkout", "-q", "-b", "feature")
        write_sigs(f, GROWN)
        update(f)
        restamp(f, pristine)
        commit_all(repo, "feature: reviewed from L1")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "feature")
        write_sigs(f, GROWN)
    def anchor_unreachable(repo, f):
        sh(repo, "checkout", "-q", "-b", "elsewhere")
        (f / "docs" / "note.md").write_text("not merged\n")
        commit_all(repo, "a commit HEAD will not contain")
        other = head_sha(repo)
        sh(repo, "checkout", "-q", "main")
        return {"__args__": ["--anchor", other]}
    def anchor_ok(repo, f):
        return {"__args__": ["--anchor", head_sha(repo)]}
    def toolchain(repo, f):
        write_sigs(f, THEOREMS, lean_version="Lean (version 4.33.0, aarch64-unknown-linux-gnu, commit 0123456789ab, Release)")
    def other_platform(repo, f):
        write_sigs(f, THEOREMS, lean_version=LEAN_V.replace("aarch64-unknown-linux-gnu", "x86_64-unknown-linux-gnu"))
    def runner(repo, f):
        (f / "tools" / "capped_lean.sh").write_text("#!/bin/sh\nexec \"$@\"\n")
        commit_all(repo, "a changed runner")
    JSON_PY = "import os\nos._exit(0)\n"           # the review's payload, in its simplest form
    def json_py(repo, f, isolated: bool):
        # H2 (review 3): a change adds tools/machsig/json.py (and replaces trust_gate.py) to take over the
        # judge's imports, plus a sorryAx growth. The ISOLATED judge, a copy of the pristine gate outside
        # the tree, must still FAIL it.
        judge = repo.parent / "judge"
        if isolated:
            shutil.copytree(f / "tools" / "machsig", judge / "tools" / "machsig",
                            ignore=shutil.ignore_patterns("trust_baseline.json", "__pycache__"))
        (f / "tools" / "machsig" / "json.py").write_text(JSON_PY)
        (f / "tools" / "machsig" / "trust_gate.py").write_text(JSON_PY)
        write_sigs(f, dict(THEOREMS, **{"Fx.alpha": THEOREMS["Fx.alpha"] + ["sorryAx"]}))
        if not isolated:
            # the in-tree run executes the replaced gate itself; restore it so only json.py attacks
            shutil.copy2(judge_src(f), f / "tools" / "machsig" / "trust_gate.py")
        return {"__judge__": str(judge)} if isolated else {}
    def judge_src(f):
        return f.parent.parent / "pristine" / "foundations" / "tools" / "machsig" / "trust_gate.py"
    def json_isolated(repo, f): return json_py(repo, f, True)
    def json_in_tree(repo, f): return json_py(repo, f, False)
    DROPPED = {k: v for k, v in THEOREMS.items() if k != "Fx.alpha"}
    def hop(f, theorems, previous):
        # one stamped step whose report is EXACT for its own hop (from `previous`)
        write_sigs(f, theorems)
        update(f)
        restamp(f, previous)
    def two_hop(repo, f, via_empty: bool = False, hops: int = 2, branch: bool = True, anchor: bool = False):
        # QUIET TWO-HOP (review 4): drop alpha (or empty the baseline) in one stamped commit, re-add it
        # GROWN in the next; each report exact for its own step, none showing the growth
        l1 = committed(f)
        base_sha = head_sha(repo)
        if branch:
            sh(repo, "checkout", "-q", "-b", "pr")
        mid = {} if via_empty else DROPPED
        hop(f, mid, l1)
        commit_all(repo, "hop 1: alpha dropped" if not via_empty else "hop 1: baseline emptied")
        prev = committed(f)
        if hops == 3:
            hop(f, THEOREMS, prev)
            commit_all(repo, "hop 2: back as it was")
            prev = committed(f)
            hop(f, DROPPED, prev)
            commit_all(repo, "hop 3: dropped again")
            prev = committed(f)
        hop(f, GROWN, prev)
        commit_all(repo, "last hop: alpha back, grown")
        return {"__args__": ["--anchor", base_sha]} if anchor else {}
    def two_hop_removal(repo, f): return two_hop(repo, f)
    def two_hop_empty(repo, f): return two_hop(repo, f, via_empty=True)
    def three_hop(repo, f): return two_hop(repo, f, hops=3)
    def two_hop_ci(repo, f): return two_hop(repo, f, anchor=True)
    def two_hop_merged(repo, f):
        # the same PR merged onto main with --no-ff WITHOUT CI: judged locally on main afterwards
        two_hop(repo, f)
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr")
    def later_push(repo, f):
        # a later, unrelated push on top of main: CI anchors on its `before`, the old tip
        before = head_sha(repo)
        (f / "docs" / "later.md").write_text("unrelated\n")
        commit_all(repo, "a later, unrelated push")
        return {"__args__": ["--anchor", before]}
    def two_hop_ff(repo, f, run: str):
        # the reviewer's exact limit (b): the two-hop PR FAST-FORWARDED onto main. Its push run anchors on
        # `before`; a later run anchors on the new tip. Plain commits' stamps never count, so EVERY run stays
        # red until the change is re-stamped net from main's last counted baseline
        before = head_sha(repo)
        two_hop(repo, f)
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--ff-only", "pr")
        if run == "push":
            return {"__args__": ["--anchor", before]}
        return later_push(repo, f) if run == "later-push" else {}
    def two_hop_ff_push(repo, f): return two_hop_ff(repo, f, "push")
    def two_hop_ff_local(repo, f): return two_hop_ff(repo, f, "local")
    def two_hop_ff_later_push(repo, f): return two_hop_ff(repo, f, "later-push")
    def two_hop_ff_restamped(repo, f):
        # control: the fast-forwarded two-hop, then re-stamped NET from main's last counted baseline
        l1 = committed(f)
        two_hop_ff(repo, f, "local")
        restamp(f, l1)
        commit_all(repo, "re-stamped net from L1")
        return later_push(repo, f)
    def single_ff(repo, f, run: str):
        # control: ONE stamp, net from main's last counted baseline, fast-forwarded onto main
        l1, before = committed(f), head_sha(repo)
        sh(repo, "checkout", "-q", "-b", "pr")
        hop(f, GROWN, l1)
        commit_all(repo, "one stamp, net from L1")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--ff-only", "pr")
        if run == "push":
            return {"__args__": ["--anchor", before]}
        return later_push(repo, f) if run == "later-push" else {}
    def single_ff_push(repo, f): return single_ff(repo, f, "push")
    def single_ff_later(repo, f): return single_ff(repo, f, "later-push")
    def single_ff_twice(repo, f, net: bool):
        # a second single-stamp fast-forward after the first. From the last COUNTED baseline (L1): accepted
        # (reports accumulate until a merge). From the first fast-forward's baseline: refused -- in git it
        # is the very same commits as the two-hop fast-forward, so it cannot be told apart
        l1 = committed(f)
        hop(f, DROPPED, l1)
        commit_all(repo, "ff 1: one stamp from L1")
        b1 = committed(f)
        hop(f, GROWN, l1 if net else b1)
        commit_all(repo, "ff 2: one stamp, " + ("net from L1" if net else "from ff 1"))
        return later_push(repo, f)
    def single_ff_twice_net(repo, f): return single_ff_twice(repo, f, True)
    def single_ff_twice_chained(repo, f): return single_ff_twice(repo, f, False)
    def merge_then_ff(repo, f):
        # control: a merge commit COUNTS -- a PR with one net stamp merged --no-ff, then a single-stamp
        # fast-forward reviewed from the merged baseline
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr1")
        hop(f, DROPPED, l1)
        commit_all(repo, "pr1: one stamp from L1")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr1")
        hop(f, GROWN, committed(f))
        commit_all(repo, "ff: one stamp from the merged baseline")
        return later_push(repo, f)
    def two_hop_unrelated_merge(repo, f):
        # the two-hop on main with an UNRELATED merge between the hops: the merge leaves the file as its
        # first parent had it, so it must not turn the first hop into a counted reference
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "side")
        (f / "docs" / "side.md").write_text("side\n")
        commit_all(repo, "side: unrelated")
        sh(repo, "checkout", "-q", "main")
        hop(f, DROPPED, l1)
        commit_all(repo, "hop 1 on main")
        b1 = committed(f)
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "side")
        hop(f, GROWN, b1)
        commit_all(repo, "hop 2 on main, from hop 1")
        return later_push(repo, f)
    def two_hop_sub_merge(repo, f, onto_main: bool = False):
        # the two-hop with its first hop arriving in a MERGE INTO THE BRANCH (from a sub-branch), the second
        # a plain commit from it. A merge counts only on the ANCHOR's first-parent line, and locally the
        # anchor is the main line's merge-base -- so neither the branch run nor main after the merge counts it
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr")
        sh(repo, "checkout", "-q", "-b", "sub")
        hop(f, DROPPED, l1)
        commit_all(repo, "sub: hop 1 from L1")
        sh(repo, "checkout", "-q", "pr")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "sub")
        b1 = committed(f)
        hop(f, GROWN, b1)
        commit_all(repo, "pr: hop 2 from hop 1")
        if onto_main:
            sh(repo, "checkout", "-q", "main")
            sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr")
    def two_hop_sub_merge_main(repo, f): two_hop_sub_merge(repo, f, True)
    def h1_merged(repo, f):
        # H1 through MERGE commits (merges are what count now): PR1 carries a self-bound REVIEWED stamp and
        # is merged; PR2 reports honestly from PR1's baseline and is merged. PR1's merge must not count
        sh(repo, "checkout", "-q", "-b", "pr1")
        b1 = grow_unreviewed(repo, f)
        d1 = tg.baseline_content_digest(b1)
        restamp(f, None, report={"schema": "machsig-transition/v3",
                                 "binding": {"old_baseline_sha256": d1, "new_baseline_sha256": d1},
                                 "gate_transition": tg.gate_transition(b1, b1)})
        commit_all(repo, "pr1: stamped, self-bound")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr1")
        b2 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr2")
        write_sigs(f, SHRUNK)
        update(f)
        restamp(f, b2)
        commit_all(repo, "pr2: honest report from pr1's baseline")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr2")
    def no_main_ref(repo, f):
        # T3'' (fifth review): a clone with no main-line ref -- the anchor falls back to HEAD
        sh(repo, "branch", "-q", "-m", "main", "trunk")
    def stale_main_ref(repo, f):
        # T9 (fifth review): local main still at the pre-review origin; a branch rebaselined from the origin
        sh(repo, "checkout", "-q", "-b", "work")
        sh(repo, "branch", "-q", "-f", "main", origin_sha(repo))
    def readded(repo, f):
        # limit (a), made visible: PR1 drops alpha (reviewed, merged); PR2 re-adds it grown, judged on its
        # branch -- its report shows alpha NEW; the gate notes its last reviewed footprint
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr1")
        hop(f, DROPPED, l1)
        commit_all(repo, "pr1: alpha dropped")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr1")
        b1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr2")
        hop(f, GROWN, b1)
        commit_all(repo, "pr2: alpha back, grown")
    def net_one_step(repo, f):
        # control: the same change as ONE reviewed step from the base: its report shows alpha GREW
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr")
        hop(f, GROWN, l1)
        commit_all(repo, "one reviewed step, net from the base")
    def net_after_unreviewed_hop(repo, f):
        # control: drop alpha WITHOUT a stamp, then one stamp from the base (net: alpha grew)
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr")
        write_sigs(f, DROPPED)
        update(f)
        commit_all(repo, "unreviewed drop")
        hop(f, GROWN, l1)
        commit_all(repo, "reviewed, net from the base")
    def two_prs(repo, f):
        # control: two sequential PRs, each one reviewed step from its base, each merged --no-ff
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr1")
        hop(f, DROPPED, l1)
        commit_all(repo, "pr1: alpha dropped, reviewed from L1")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr1")
        b1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "pr2")
        hop(f, GROWN, b1)
        commit_all(repo, "pr2: alpha back grown, reviewed from B1 (its report shows it NEW)")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr2")
    def stale_branch(repo, f):
        # control: a branch forked at L1 merges main after main moved (PR1 reviewed), then rebaselines
        # from main's B1; merged --no-ff. Its stale L1 reference must be superseded, not joined.
        l1 = committed(f)
        sh(repo, "checkout", "-q", "-b", "late")
        (f / "docs" / "late.md").write_text("work\n")
        commit_all(repo, "late: unrelated work")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "checkout", "-q", "-b", "pr1")
        hop(f, DROPPED, l1)
        commit_all(repo, "pr1 reviewed from L1")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "pr1")
        b1 = committed(f)
        sh(repo, "checkout", "-q", "late")
        sh(repo, "merge", "-q", "--no-edit", "main")
        hop(f, GROWN, b1)
        commit_all(repo, "late: reviewed from B1")
        sh(repo, "checkout", "-q", "main")
        sh(repo, "merge", "-q", "--no-ff", "--no-edit", "late")
    def origin_via_merge(repo, f):
        # control: main's first-parent line reaches the origin only through a merge's SECOND parent (an
        # orphan history that merged the reviewed line, its own commit first). The union over ALL parents
        # keeps the chain; counting the first parent alone would lose it and refuse a reviewed baseline.
        sh(repo, "checkout", "-q", "--orphan", "other")
        sh(repo, "commit", "-q", "-m", "an unrelated root holding the same tree")
        sh(repo, "merge", "-q", "--no-edit", "--allow-unrelated-histories", "main")
        sh(repo, "branch", "-q", "-f", "main", "HEAD")
        sh(repo, "checkout", "-q", "main")
    def shallow(repo, f):
        # depth-1 clone: neither the provenance commit nor the previous baseline is reachable
        clone = repo.parent / "shallow"
        subprocess.run(["git", "clone", "-q", "--depth", "1", f"file://{repo}", str(clone)], env=env(),
                       check=True, capture_output=True)
        shutil.copytree(f / "artifacts", clone / "foundations" / "artifacts")
        shutil.rmtree(repo)
        clone.rename(repo)
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
        ("B19 REVIEWED stamp citing a report outside the tree (absolute path)", report_outside, 3,
         "review-report-invalid", "not a path inside foundations/"),
        ("B20 REVIEWED stamp citing an uncommitted report", report_untracked, 3, "review-report-invalid",
         "not committed unmodified"),
        ("B21 signature set naming one theorem twice", duplicate, 3, "signatures-corrupt", "Fx.alpha (twice)"),
        ("B22 REVIEWED stamp naming no reviewer", no_reviewer, 3, "baseline-unreviewed", "no reviewer named"),
        ("B17 an axiom entered an unchanged statement", growth, 1, None, "Fx.alpha  1 -> 2  entered Fx.ax_one"),
        ("B18 swap: same count, different axiom", swap, 1, None, "Fx.beta  5 -> 5  entered Fx.ax_one"),
        ("B23 ATTACK 3: --update, then the old REVIEWED stamp pasted back", paste_old_stamp, 3,
         "review-unbound", "not written for this content"),
        ("B24 ATTACK 4: reviewer 'x', lakefile.lean as the transition report", lakefile_report, 3,
         "review-report-invalid", "lakefile.lean is not JSON"),
        ("B25 a JSON file that is not a transition report", json_not_report, 3, "review-report-invalid",
         "not a machsig-transition report"),
        ("B26 report describing another baseline", report_wrong_new, 3, "review-report-mismatch", "not to this baseline"),
        ("B27 report against the wrong predecessor", report_wrong_old, 3, "review-report-mismatch",
         "the last reviewed baseline is"),
        ("B28 ATTACK 5: statement changed AND sorryAx entered", restate_sorry, 1, None,
         "Fx.alpha  2 -> 3  entered sorryAx"),
        ("B29 statement changed, axioms unchanged", restate_only, 1, None, "Fx.alpha  2 -> 2  axioms unchanged"),
        ("B30 ATTACK 6: a watched theorem leaves the set", remove, 1, None, "FAIL [removed]"),
        ("B31 shallow clone: provenance and previous baseline unreachable", shallow, 3,
         ["baseline-provenance-unresolvable", "baseline-history-unavailable"], "fetch-depth: 0"),
        ("B32 control: a new theorem on declared axioms passes", add_new, 0, None, "MACHSIG-TRUST OK"),
        ("B33 sorryAx in a NEW theorem (not allowlisted)", sorry_new, 1, None, "Fx.delta  rests on sorryAx"),
        ("B34 native_decide's compiler-trust axiom in a NEW theorem, even when declared", native_new, 1, None,
         "Fx.delta  rests on Fx.delta._native.native_decide.ax_1_1"),
        ("B35 an UNDECLARED axiom the reviewed baseline already holds", undeclared_grandfathered, 1, None,
         "Fx.beta  rests on Fx.undeclared"),
        ("B36 an axiom restated under its own name (16 Certcom axioms, this window)", axiom_restated, 1, None,
         "FAIL [axiom-restated]"),
        ("B37 statement unchanged, a definition under it changed (E3, clamp)", redefined, 1, None,
         "Fx.alpha  2 -> 2  axioms unchanged"),
        ("B38 an axiom promoted into trustedFootprint (E1, E2)", promoted, 1, None, "trustedFootprint + Fx.ax_three"),
        ("B39 the sorry allowlist grew", sorry_allowlisted, 1, None, "allowedSorry + Fx.alpha"),
        ("B40 ATTACK 2 in a regenerating run: the set is from another run", other_run, 3,
         "signatures-not-this-run", "'run-A'"),
        ("B41 control: the set this run regenerated passes, without ADVISORY", same_run, 0, None,
         "regenerated in this run (run-A)"),
        ("B42 H1 (review 2), verbatim: --update, then a stamp citing a 4-line 'this -> itself' report",
         h1_exact, 3, "review-report-invalid", "gate_transition"),
        ("B43 H1, v3-shaped: self-binding with an empty recompute", h1_v3_hollow_self, 3,
         "review-report-mismatch", "self-binding"),
        ("B44 H1, self-binding that carries the true rows", h1_self_with_rows, 3, "review-report-mismatch",
         "self-binding"),
        ("B45 H1, correct binding but rows that omit the growth", h1_hollow_rows, 3, "review-report-rows",
         "first difference at Fx.alpha"),
        ("B46 H1, three commits: an invalid stamp in the middle is not a reference", h1_three_commits, 3,
         "review-report-mismatch", "neither an unreviewed --update nor a stamp on a plain commit"),
        ("B47 H1, an unreviewed intermediate under an honest stamp", h1_intermediate, 3,
         "review-report-mismatch", "neither an unreviewed --update nor a stamp on a plain commit"),
        ("B48 control: --update, then a stamp reporting from the last reviewed baseline", honest_two_step, 0,
         None, "MACHSIG-TRUST OK"),
        ("B49 two reviewed rebaselines as plain commits on main, the second from the first (review 5)",
         honest_chain, 3, "review-report-mismatch", "the last reviewed baseline is"),
        ("B50 RESTART (review 3): re-commit the origin, then rebaseline from it", restart, 3,
         "review-report-mismatch", "the last reviewed baseline is"),
        ("B51 re-commit an OLDER reviewed baseline over a newer (merged) one", recommit_older, 3, "review-report-mismatch",
         "the last reviewed baseline is the baseline reviewed at"),
        ("B52 MERGE (review 3): pre-review branch merged, its file kept, branch as first parent",
         merge_side_first, 3, "review-report-mismatch", "the last reviewed baseline is"),
        ("B53 MERGE, reviewed line as first parent", merge_main_first, 3, "review-report-mismatch",
         "the last reviewed baseline is"),
        ("B54 control: a branch reviewed from L1 merged with --no-ff", honest_merge, 0, None, "MACHSIG-TRUST OK"),
        ("B55 --anchor names a commit this history lacks", anchor_unreachable, 3, "anchor-unreachable",
         "is not an ancestor of HEAD"),
        ("B56 control: --anchor at the reviewed commit", anchor_ok, 0, None, "MACHSIG-TRUST OK"),
        ("B57 signatures extracted with another toolchain", toolchain, 3, "toolchain-mismatch", "4.33.0"),
        ("B58 control: same toolchain, other platform (aarch64 vs x86_64)", other_platform, 0, None,
         "MACHSIG-TRUST OK"),
        ("B59 tools/capped_lean.sh differs from the baseline's provenance commit", runner, 3, "runner-changed",
         "tools/capped_lean.sh"),
        ("B60 H2 (review 3): json.py in the tree; the ISOLATED judge still FAILS the sorryAx growth", json_isolated,
         1, None, "FAIL [policy-violation]"),
        ("B61 control (the attack is real): the same tree judged in-tree, unisolated, exits 0", json_in_tree, 0,
         None, ""),
        ("B62 QUIET TWO-HOP (review 4): drop alpha, re-add it grown, one PR, local run", two_hop_removal, 3,
         "review-report-mismatch", "the last reviewed baseline is"),
        ("B63 QUIET TWO-HOP through an empty baseline", two_hop_empty, 3, "review-report-mismatch",
         "the last reviewed baseline is"),
        ("B64 three hops", three_hop, 3, "review-report-mismatch", "the last reviewed baseline is"),
        ("B65 QUIET TWO-HOP judged the CI way (--anchor <base>)", two_hop_ci, 3, "review-report-mismatch",
         "as of the base"),
        ("B66 QUIET TWO-HOP merged --no-ff without CI, judged on main", two_hop_merged, 3, "review-report-mismatch",
         "the last reviewed baseline is"),
        ("B67 control: the same change as ONE reviewed step (its report shows alpha grew)", net_one_step, 0, None,
         "MACHSIG-TRUST OK"),
        ("B68 control: an unreviewed drop, then one stamp net from the base", net_after_unreviewed_hop, 0, None,
         "MACHSIG-TRUST OK"),
        ("B69 control: two sequential PRs, each one reviewed step, merged --no-ff", two_prs, 0, None,
         "MACHSIG-TRUST OK"),
        ("B70 control: a branch that merged main, then rebaselined from it, merged --no-ff", stale_branch, 0, None,
         "MACHSIG-TRUST OK"),
        ("B71 QUIET TWO-HOP fast-forwarded onto main, judged the CI push way (--anchor <before>)", two_hop_ff_push,
         3, "review-report-mismatch", "as of the base"),
        ("B72 LIMIT (b) CLOSED (review 5): that fast-forward judged on main later (local run)", two_hop_ff_local,
         3, "review-report-mismatch", "the last reviewed baseline is"),
        ("B73 control: main reaches the origin only through a merge's second parent", origin_via_merge, 0, None,
         "MACHSIG-TRUST OK"),
        ("B74 the fast-forwarded two-hop, then a LATER push (--anchor <its tip>): still refused",
         two_hop_ff_later_push, 3, "review-report-mismatch", "the last reviewed baseline is"),
        ("B75 control: the fast-forwarded two-hop re-stamped net from L1, then a later push", two_hop_ff_restamped,
         0, None, "MACHSIG-TRUST OK"),
        ("B76 control: a single-stamp fast-forward, its push run", single_ff_push, 0, None, "MACHSIG-TRUST OK"),
        ("B77 control: a single-stamp fast-forward, a later push", single_ff_later, 0, None, "MACHSIG-TRUST OK"),
        ("B78 control: two single-stamp fast-forwards, the second net from the last COUNTED baseline",
         single_ff_twice_net, 0, None, "MACHSIG-TRUST OK"),
        ("B79 two single-stamp fast-forwards, the second from the first (in git, the two-hop itself)",
         single_ff_twice_chained, 3, "review-report-mismatch", "the last reviewed baseline is"),
        ("B80 control: a merge commit counts -- a merged PR, then a fast-forward from its baseline", merge_then_ff,
         0, None, "MACHSIG-TRUST OK"),
        ("B81 the two-hop on main with an unrelated merge between the hops", two_hop_unrelated_merge, 3,
         "review-report-mismatch", "the last reviewed baseline is"),
        ("B82 control (the documented cost): an older baseline re-committed over a newer PLAIN-commit one",
         recommit_older_plain, 0, None, "MACHSIG-TRUST OK"),
        ("B83 no main-line ref: OK, but ADVISORY [anchor-none]", no_main_ref, 0, None,
         "MACHSIG-TRUST ADVISORY [anchor-none]"),
        ("B84 main ref before the first reviewed baseline: OK, but ADVISORY [anchor-before-landing]",
         stale_main_ref, 0, None, "MACHSIG-TRUST ADVISORY [anchor-before-landing]"),
        ("B85 limit (a) shown: a re-added theorem is noted with its last reviewed footprint", readded, 0, None,
         "MACHSIG-TRUST NOTE [readded] Fx.alpha is new against"),
        ("B86 two-hop whose first hop is merged INTO the branch, local run on the branch", two_hop_sub_merge, 3,
         "review-report-mismatch", "the last reviewed baseline is"),
        ("B87 that branch merged --no-ff into main, judged on main", two_hop_sub_merge_main, 3,
         "review-report-mismatch", "the last reviewed baseline is"),
        ("B88 H1 through merge commits: a self-bound stamp merged, then a PR reporting from it, merged", h1_merged,
         3, "review-report-mismatch", "the last reviewed baseline is"),
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
        control = rc == 0 and "MACHSIG-TRUST OK" in out and not TAG.search(out) and "MACHSIG-TRUST ADVISORY" in out
        lines.append(f"  [{'ok' if control else 'BROKEN'}] B0 control: fresh set, reviewed committed baseline "
                     f"-> OK (rc {rc}), and a standalone run says ADVISORY")
        ok &= control
        if not control:
            lines.append("        " + out.strip().replace("\n", "\n        ")[:1500])
        for name, fault, want_rc, want_tag, want_text in cases():
            shutil.rmtree(work)
            shutil.copytree(pristine, work, symlinks=True)
            try:
                extra = fault(work, work / "foundations")
            except (subprocess.CalledProcessError, OSError) as e:
                lines.append(f"  [BROKEN] {name}: the fault could not be injected ({e})")
                ok = False
                continue
            rc, out = run_gate(work / "foundations", extra if isinstance(extra, dict) else None)
            tags = TAG.findall(out)
            want_tags = [] if want_tag is None else (want_tag if isinstance(want_tag, list) else [want_tag])
            good = rc == want_rc and tags == want_tags and want_text in out \
                and not (name.startswith("B41") and "ADVISORY" in out)
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
    ("review status check removed", 'if r.get("status") != "REVIEWED":', "if False:"),
    ("reviewer check removed", '    if not r.get("reviewer"):', "    if False:"),
    ("stamp-to-content binding removed", 'if r.get("baseline_sha256") != mine:', "if False:"),
    ("report-must-be-a-transition-JSON check removed",
     'if bad is None and not (isinstance(report_doc, dict)', 'if False and not (isinstance(report_doc, dict)'),
    ("report's new side not checked", 'if bind.get("new_baseline_sha256") != mine:', "if False:"),
    ("report's old side not checked", 'if bind.get("old_baseline_sha256") != want_old:', "if False:"),
    ("self-binding check removed",
     'if bind.get("old_baseline_sha256") == bind.get("new_baseline_sha256") and \\', "if False and \\"),
    ("report rows not compared with the recompute", 'if report_doc["gate_transition"] != recomputed:', "if False:"),
    ("historical stamps counted without checking their reports",
     "if all(dv == k or not review_problems(v, rdoc, label, _report_at(root, c))",
     'if all(dv == k or (v.get("review") or {}).get("status") == "REVIEWED"'),
    ("the walk never advances past the origin",
     'refs[c] = {dv: (f"the baseline reviewed at {c[:12]}", v)}', "refs[c] = inherited"),
    ("RESTART: the origin restarts the chain wherever its content reappears",
     "        if c == ORIGIN_COMMIT:", "        if blobs.get(c) == blobs.get(ORIGIN_COMMIT):"),
    # Since stamps off the first-parent line never count, a second parent can only bring references the
    # line made earlier, already superseded -- so this mutant is visible only where the line reaches the
    # origin THROUGH a merge's second parent (B73), not in any graph that reaches it by first parents.
    ("MERGE: only the first parent's references count", "        for p in parents[c]:\n            if refs.get(p):",
     "        for p in parents[c][:1]:\n            if refs.get(p):"),
    ("MERGE: a merge taking one side's file is not judged", "b is None or all(blobs.get(p) == b for p in parents[c]):",
     "b is None or any(blobs.get(p) == b for p in parents[c]):"),
    ("anchor reachability not checked",
     '    if anchor and not identity.git_ok(root, "merge-base", "--is-ancestor", anchor, "HEAD"):', "    if False:"),
    ("TWO-HOP: no default anchor (stamps chain inside a branch)",
     '    tip = anchor or main_anchor or "HEAD"', '    tip = anchor or "HEAD"'),
    ("TWO-HOP: stamps off the first-parent line count", "        if c not in line or b is None or all(",
     "        if b is None or all("),
    ("LIMIT (b): plain commits' stamps count on the line",
     "        if not landing and (len(parents[c]) < 2 or b == blobs.get(parents[c][0])):", "        if False:"),
    ("LIMIT (b): a merge counts a version its first parent already had",
     "(len(parents[c]) < 2 or b == blobs.get(parents[c][0])):", "(len(parents[c]) < 2):"),
    ("the step-7 landing never counts", "        landing = set(inherited) == {ORIGIN_CONTENT}",
     "        landing = False"),
    ("ADVISORY [anchor-none] removed", "    if not anchor and not main_anchor:", "    if False:"),
    ("ADVISORY [anchor-before-landing] removed", '    if set(final) == {ORIGIN_CONTENT} and tip != "HEAD":',
     "    if False:"),
    ("NOTE [readded] removed", "            notes.extend(readded_notes(b, k, lineage, known))", "            pass"),
    ("superseded references not pruned",
     "        inherited = {k: v for k, v in inherited.items() if not superseded(k, inherited)}",
     "        inherited = dict(inherited)"),
    ("toolchain not compared", "    if prov.get(\"lean_toolchain\") != head.get(\"lean_toolchain\") or \\",
     "    if False and \\"),
    ("toolchain compared with the platform", "    m = LEAN_VERSION.search(str(v))", "    m = None"),
    ("runner scripts not compared", "        if here != there:", "        if False:"),
    ("the judge puts the tree on its import path", "    FOUND = Path(path).resolve()",
     '    FOUND = Path(path).resolve()\n    sys.path.insert(0, str(FOUND / "tools" / "machsig"))'),
    ("restatement passes again (pre-2026-10-13)",
     '("restated", "statement CHANGED: a different claim the baseline has not reviewed"),', ""),
    ("removal passes again (pre-2026-10-13)",
     '("removed", "theorem LEFT the watched set (deleted, renamed, made private or moved): unreviewed"),', ""),
    ("definition-closure comparison removed", 'if b.get("c") != v.get("c"):', "if False:"),
    ("sorryAx outside the allowlist accepted", '(a == SORRY and k not in allowed) or ', ""),
    ("compiler-trust axioms accepted", "or is_compiler_trust(a)\n", "\n"),
    ("undeclared axioms accepted", "or (a != SORRY and a not in declared))", ")"),
    ("axiom statements not compared", "and base[\"axioms\"][a] != cur[\"axioms\"][a])", "and False)"),
    ("trustedFootprint growth ignored", 'res["policy-widened"] = [f"trustedFootprint + {a}" for a in cur["policy"]["trusted"]',
     'res["policy-widened"] = [f"trustedFootprint + {a}" for a in []'),
    ("run binding removed", 'if run_id and head.get("run_id") != run_id:', "if False:"),
    ("committed-report check removed",
     'if not identity.git_ok(root, "ls-files", "--error-unmatch", "--", rep) \\\n'
     '                or identity.git(root, "status", "--porcelain", "--", rep).strip():', "if False:"),
    ("set ratchet weakened to the pre-2026-10-13 count rule", "        if entered:",
     '        if v["ax"] > b["ax"]:'),
    ("stale refusal stops naming what moved",
     "Moved: {', '.join(moved) or '(file list unavailable)'}", "Moved: (not named)"),
    ("REVIEWED stamp may cite any file on the machine",
     'elif Path(rep).is_absolute() or ".." in Path(rep).parts \\\n            or not (FOUND / rep).resolve().is_relative_to(FOUND.resolve()):',
     "elif False:"),
    ("duplicate records accepted (last write wins)", "        if j.get(\"object\") in seen:", "        if False:"),
    ("self-contradicting baseline entries accepted",
     'axs is None or len(axs) != e.get("ax") or not isinstance(e.get("d"), str) \\\n'
     '                or not HEX64.match(str(e.get("c"))):', "axs is None:"),
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
    n_b = sum(1 for ln in b_lines if ln.startswith("  [") and "control" not in ln)
    n_bc = sum(1 for ln in b_lines if ln.startswith("  [") and "control" in ln)
    if a_ok is False or not b_ok:
        print("  SELFTEST FAIL — a red path did not fire as specified, or a control fired")
        return tg.FAIL
    if a_ok is None:
        print(f"  SELFTEST UNAVAILABLE — Part B passed ({n_b} injected faults + {n_bc} controls); Part A needs a "
              "readable real signature set")
        return tg.UNAVAILABLE
    n_a = sum(1 for ln in a_lines if ln.startswith("  [ok] INJECTED"))
    n_ac = sum(1 for ln in a_lines if ln.startswith(("  [ok]", "  [BROKEN]"))) - n_a
    print(f"  SELFTEST PASS — Part A: {n_a} injections + {n_ac} controls on the real set; "
          f"Part B: {n_b} injected faults + {n_bc} controls")
    return tg.OK


if __name__ == "__main__":
    sys.exit(mutate() if "--mutate" in sys.argv else run())
