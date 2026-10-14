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
    ctl = tg.judge(whole, cur)
    check(not convictions(ctl), f"control: the real set judged against itself: no conviction, no policy violation "
                                f"({len(cur['axioms'])} axioms pinned, allowlisted sorry {cur['policy']['allowed_sorry']})")
    inj7 = copy.deepcopy(whole)
    inj7["theorems"][swap]["c"] = "0" * 64
    r7 = tg.judge(inj7, cur)
    check(convictions(r7) == ["redefined"] and [x["theorem"] for x in r7["redefined"]] == [swap],
          f"INJECTED definition change under {swap.split('.')[-1]} (E3, clamp): convicted as `redefined`")
    ax = sorted(a for a in cur["axioms"] if a.startswith(("MachLib", "Certcom")))[0]
    inj8 = copy.deepcopy(whole)
    inj8["axioms"][ax] = "0" * 64
    r8 = tg.judge(inj8, cur)
    check(convictions(r8) == ["axiom-restated"] and r8["axiom-restated"] == [ax],
          f"INJECTED restatement of axiom {ax.split('.')[-1]} under its own name: convicted as `axiom-restated`")
    cur9 = copy.deepcopy(cur)
    cur9["theorems"][swap]["axioms"] = sorted(cur9["theorems"][swap]["axioms"] + [tg.SORRY])
    inj9 = copy.deepcopy(whole)
    inj9["theorems"][swap]["axioms"] = list(cur9["theorems"][swap]["axioms"])   # grandfathered in the baseline
    r9 = tg.judge(inj9, cur9)
    check(convictions(r9) == ["policy-violation"] and [x["theorem"] for x in r9["policy-violation"]] == [swap],
          "INJECTED sorryAx into a theorem the baseline already holds that way: `policy-violation` anyway")
    promoted = "MachLib.Real.pi_lower_bound" if "MachLib.Real.pi_lower_bound" in cur["policy"]["trusted"] \
        else cur["policy"]["trusted"][-1]                                  # E1's own axiom when present
    inj10 = copy.deepcopy(whole)
    inj10["policy"]["trusted"] = [a for a in inj10["policy"]["trusted"] if a != promoted]
    r10 = tg.judge(inj10, cur)
    check(convictions(r10) == ["policy-widened"] and r10["policy-widened"] == [f"trustedFootprint + {promoted}"],
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


def write_sigs(found: Path, theorems: dict, header: bool = True, digests: dict | None = None,
               closures: dict | None = None, axioms: dict | None = None, policy: dict | None = None,
               run_id: str | None = None) -> None:
    """A synthetic v0.4 signature set with the real writer's provenance header. `digests` / `closures`
    perturb a theorem's StatementDigest / DefClosureDigest by name; `axioms` / `policy` replace the pins
    and the declared policy."""
    sys.path.insert(0, str(found / "tools" / "machsig"))
    import sig                                         # the real writer's provenance format
    live = identity.live_identity(found)
    ext = dict(live, lean_version="selftest", raw={}, policy=policy or POLICY, run_id=run_id)
    records = {}
    for name in theorems:
        axs = sorted(theorems[name])
        records[name] = {"kind": "theorem", "object": name, "version": sig.VERSION,
                         "StatementDigest": hashlib.sha256((name + (digests or {}).get(name, "")).encode()).hexdigest(),
                         "DefClosureDigest": hashlib.sha256(("c:" + name + (closures or {}).get(name, "")).encode()).hexdigest(),
                         "TrustSig": f"AX{len(axs)}-S0", "TrustAxioms": axs}
    for a, h in (axioms or AXIOMS).items():
        records[a] = {"kind": "axiom", "object": a, "version": sig.VERSION, "AxiomStatementDigest": h}
    lines = [json.dumps(records[k], sort_keys=True) + "\n" for k in sorted(records)]
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
    # The fixture's own pre-review origin: a counts-only baseline committed first, as c3046961's is in
    # MachLib; the fixture's gate copy is pointed at it (ORIGIN_CONTENT is a constant of the gate).
    gp = found / "tools/machsig/trust_gate.py"
    gp.write_text(re.sub(r'^ORIGIN_CONTENT = ".*"$', f'ORIGIN_CONTENT = "{tg.baseline_content_digest(LEGACY)}"',
                         gp.read_text(), count=1, flags=re.M))
    (found / tg.BASE_REL).write_text(json.dumps(LEGACY, sort_keys=True, indent=0))
    sh(repo, "init", "-q", "-b", "main")
    sh(repo, "add", "-A")
    sh(repo, "commit", "-q", "-m", "fixture, with the counts-only origin baseline")
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
    (found / REPORT).write_text(json.dumps(report, sort_keys=True) + "\n")
    b["review"] = {"status": "REVIEWED", "reviewer": reviewer, "transition_report": REPORT, "baseline_sha256": mine}
    p.write_text(tg.dump_baseline(b))


def run_gate(found: Path, extra: dict | None = None) -> tuple[int, str]:
    r = subprocess.run([sys.executable, str(found / "tools/machsig/trust_gate.py")], cwd=found, env=env(extra),
                       capture_output=True, text=True)
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
        # control: two reviewed rebaselines in a row; the second's report starts at the first
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
         "review-report-mismatch", "an unreviewed --update in between does not count"),
        ("B47 H1, an unreviewed intermediate under an honest stamp", h1_intermediate, 3,
         "review-report-mismatch", "an unreviewed --update in between does not count"),
        ("B48 control: --update, then a stamp reporting from the last reviewed baseline", honest_two_step, 0,
         None, "MACHSIG-TRUST OK"),
        ("B49 control: two reviewed rebaselines, the second reporting from the first", honest_chain, 0, None,
         "MACHSIG-TRUST OK"),
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
    ("H1 pre-fix: the reference is the previous committed version",
     "    label, ref = ORIGIN_LABEL, hist[starts[-1]][1]",
     "    label, ref = ORIGIN_LABEL, (hist[-2][1] if len(hist) > 1 else hist[starts[-1]][1])"),
    ("historical stamps counted without checking their reports",
     "if not review_problems(doc, ref, label, _report_at(root, c)):",
     'if (doc.get("review") or {}).get("status") == "REVIEWED" if isinstance(doc, dict) else False:'),
    ("the walk never advances past the origin",
     'label, ref = f"the baseline reviewed at {c[:12]}", doc', "pass"),
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
    print(f"  SELFTEST PASS — Part A: {n_a} injections + {len(a_lines) - n_a} controls on the real set; "
          f"Part B: {n_b} injected faults + {n_bc} controls")
    return tg.OK


if __name__ == "__main__":
    sys.exit(mutate() if "--mutate" in sys.argv else run())
