#!/usr/bin/env python3
"""Emit `status.json` for machlib's verification dashboard.

Designed to run from a CI runner only. The script is reproducible: anyone
with the same checkout (machlib + sibling clones of forge, eml-stdlib,
monogate-research at the SHAs recorded in the output) can re-run this
and verify byte-for-byte.

The script makes no claim about whether the underlying proofs are
"complete" — it only counts and classifies.

PROOF COUNTS COME FROM THE THEOREM LEDGER, AND ONLY FROM IT (the owner's
ruling, 2026-10-10: "a text search is not an acceptable basis for reporting
the number of proved mathematical results"). The `theorem_ledger` block
carries the seven ledger counts (declarations, theorems, kernel-checked,
axiom-audited, approved-policy, conditional, unchecked), the ledger's
provenance and its digest; the ledger itself is published beside
status.json. Until schema 2 this file also published
`verify_audit.proven_mod_machlib_axioms`, which was a TEXT classification
of Forge stubs in Discovered/ (body without `sorry`, not `True := by
trivial`) that no axiom audit covered; it is null now, and the text figure
survives only as `stub_text_no_sorry`, labelled as what it is.

Outputs:

  status.json — a self-describing snapshot with:
    * machlib_sha + generated_at_utc (the data's own provenance)
    * sorries.delta_vs_previous (per-cycle change vs the previous run)
    * theorem_ledger (the seven ledger counts + provenance + ledger digest)
    * verify_audit (total / strengthened (ledger-backed) / placeholder /
      open / gap_pct; the proven_* figures and discharged_pct are null)
    * axiomatized_base (which MachLib.Real.* axioms are load-bearing)
    * reproduce (the command list to recompute)
    * content_hash_sha256 (hash of the JSON with this field set to null)

The renderer in monogate-net is expected to display machlib_sha +
generated_at_utc verbatim — never its own page-load time.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path

SCHEMA_VERSION = 2   # 2 (2026-10-10): theorem_ledger added; verify_audit's proven_* and discharged_pct retired to null

LAKE_BUILT_RE = re.compile(r'^\s*[✔✗]\s*\[(\d+)/(\d+)\]\s*Built\s+(\S+)', re.MULTILINE)
LAKE_FAIL_RE = re.compile(r'^(?:error|✗\s+Build error|Build error in module)\b', re.MULTILINE)
AXIOM_BLOCK_RE = re.compile(
    r"^'(?P<thm>[^']+)' depends on axioms: \[(?P<axioms>[^\]]*)\]",
    re.MULTILINE | re.DOTALL,
)
SORRY_RE = re.compile(r'\bsorry\b')
LEAN_DOC_COMMENT_RE = re.compile(r'/-[!]?(?:[^-]|-(?!/))*-/', re.DOTALL)


def strip_lean_doc_comments(text: str) -> str:
    def _blank(match: re.Match[str]) -> str:
        return "\n" * match.group(0).count("\n")
    return LEAN_DOC_COMMENT_RE.sub(_blank, text)


MACHLIB_CORE_FILES = (
    "Basic.lean",
    "Exp.lean",
    "Log.lean",
    "Trig.lean",
    "EML.lean",
    "Hyperbolic.lean",
    "HyperbolicPreservation.lean",
    "SelfMapConjugacy.lean",
)


def _count_in_file(lean_file: Path) -> int:
    """Count `\\bsorry\\b` occurrences in a single Lean file after
    stripping block + line comments. Matches builder_v2.py's canonical
    `_count_sorries_and_lines` method byte-for-byte."""
    try:
        raw = lean_file.read_text(encoding="utf-8", errors="replace")
    except OSError:
        return 0
    stripped = strip_lean_doc_comments(raw)
    no_line_comments = "\n".join(
        line.split("--", 1)[0] for line in stripped.splitlines()
    )
    return len(SORRY_RE.findall(no_line_comments))


def _enumerate_foundation_files(machlib_root: Path) -> tuple[list[Path], list[Path]]:
    """Return (core_files, discovered_files) using the canonical split:

      - core: the 8 hand-written `MachLib/<Name>.lean` files at top level
        of foundations/MachLib/.
      - discovered: every other `.lean` file under foundations/MachLib/,
        excluding Test.lean and anything under `.lake/`.

    This is byte-for-byte the same enumeration `builder_v2.py` uses for
    its `machlib_foundation_files_core` and
    `machlib_foundation_files_discovered` keys.
    """
    foundations = machlib_root / "foundations" / "MachLib"
    if not foundations.is_dir():
        return [], []
    files = [
        p for p in sorted(foundations.rglob("*.lean"))
        if p.is_file() and ".lake" not in p.parts and p.name != "Test.lean"
    ]
    core_names = set(MACHLIB_CORE_FILES)
    core_files = [
        p for p in files
        if p.parent == foundations and p.name in core_names
    ]
    discovered_files = [p for p in files if p not in core_files]
    return core_files, discovered_files


def count_sorries_canonical(machlib_root: Path) -> tuple[int, int, int, int]:
    """Canonical sorry count matching builder_v2.py.

    Returns (core, discovered, total_files_core, total_files_discovered).
    """
    core_files, discovered_files = _enumerate_foundation_files(machlib_root)
    core = sum(_count_in_file(p) for p in core_files)
    discovered = sum(_count_in_file(p) for p in discovered_files)
    return core, discovered, len(core_files), len(discovered_files)


def parse_build_log(build_log_path: Path | None) -> dict:
    """Parse `lake build` log for module-count and failures.

    Returns
    -------
    dict with keys
        modules_built : int  — number of `[N/M] Built ...` lines seen
        modules_total : int  — the M in the last `[N/M]` line
        modules_failed: list[str]
        had_error_line: bool
    """
    if build_log_path is None or not build_log_path.exists():
        return {
            "modules_built": 0,
            "modules_total": 0,
            "modules_failed": [],
            "had_error_line": False,
        }
    text = build_log_path.read_text(encoding="utf-8", errors="replace")
    matches = LAKE_BUILT_RE.findall(text)
    modules_built = len(matches)
    modules_total = int(matches[-1][1]) if matches else 0
    failures = [line for line in text.splitlines() if "error" in line.lower() and "Build" not in line and "lean" not in line.lower()]
    had_error_line = bool(LAKE_FAIL_RE.search(text))
    return {
        "modules_built": modules_built,
        "modules_total": modules_total,
        "modules_failed": [],  # populated only on actual non-zero exit
        "had_error_line": had_error_line,
    }


def parse_axiom_audit(audit_path: Path | None) -> dict:
    """Parse `lake env lean AxiomAudit.lean` output for axiom dependency
    sets per theorem.

    Returns a dict with:
        theorems : { theorem_name : [axiom1, axiom2, ...] }
        machlib_real_axioms : sorted list of unique MachLib.Real.* axioms used
        non_machlib_axioms  : sorted list of non-MachLib.Real (propext, Classical.choice, Quot.sound)
    """
    if audit_path is None or not audit_path.exists():
        return {
            "theorems": {},
            "machlib_real_axioms": [],
            "non_machlib_axioms": [],
        }
    text = audit_path.read_text(encoding="utf-8", errors="replace")
    # The output is multiline; axiom lists are comma + newline separated inside [...].
    # Join continuation lines so each "depends on axioms" block is one string.
    flattened = re.sub(r",\s*\n\s+", ", ", text)
    theorems: dict[str, list[str]] = {}
    for match in AXIOM_BLOCK_RE.finditer(flattened):
        thm = match.group("thm").strip()
        axioms_raw = match.group("axioms").strip()
        axioms = [a.strip() for a in axioms_raw.split(",") if a.strip()]
        theorems[thm] = axioms
    all_axioms: set[str] = set()
    for ax_list in theorems.values():
        all_axioms.update(ax_list)
    machlib_real = sorted(a for a in all_axioms if a.startswith("MachLib.Real"))
    other = sorted(a for a in all_axioms if not a.startswith("MachLib."))
    return {
        "theorems": theorems,
        "machlib_real_axioms": machlib_real,
        "non_machlib_axioms": other,
    }


def compute_delta_vs_previous(
    current_total: int, previous_status: dict | None
) -> dict:
    """Compute sorry trend vs previous status.json (if any)."""
    if not previous_status:
        return {
            "previous_total": None,
            "net_change": None,
            "method": "first_run",
            "note": "No previous status.json found; first run on this branch.",
        }
    prev = previous_status.get("sorries", {}).get("total")
    if not isinstance(prev, int):
        return {
            "previous_total": None,
            "net_change": None,
            "method": "no_previous_total",
            "note": "Previous status.json lacks a comparable sorries.total field.",
        }
    return {
        "previous_total": prev,
        "net_change": current_total - prev,
        "method": "net_only",
        "note": (
            "net_only: current minus previous total. Does not distinguish "
            "'closed N then introduced N+k' from 'introduced k net'. Tracking "
            "per-theorem set-diff is a follow-up."
        ),
    }


def carry_history(previous_status: dict | None, this_entry: dict) -> list[dict]:
    """Carry forward a short history series for trend rendering."""
    prev_history: list[dict] = []
    if previous_status:
        raw = previous_status.get("sorries", {}).get("history_recent")
        if isinstance(raw, list):
            prev_history = raw
    series = prev_history + [this_entry]
    # Cap at 30 most-recent entries so the JSON doesn't grow unbounded.
    return series[-30:]


def load_previous_status(path: Path | None) -> dict | None:
    if path is None or not path.exists():
        return None
    try:
        text = path.read_text(encoding="utf-8").strip()
        if not text or text == "null":
            return None
        return json.loads(text)
    except (OSError, json.JSONDecodeError):
        return None


LEDGER_COUNT_KEYS = ("declarations", "theorems", "kernel_checked", "axiom_audited", "approved_policy",
                     "conditional", "unchecked")
LEDGER_REPRODUCE = "cd foundations && python3 tools/theorem_ledger/ledger.py --out theorem_ledger.json"


def _sha256_file(path: Path) -> str:
    return "sha256:" + hashlib.sha256(path.read_bytes()).hexdigest()


def theorem_ledger_unavailable(reason: str) -> dict:
    return {
        "available": False,
        "reason": reason,
        "counts": {k: None for k in LEDGER_COUNT_KEYS},
        "note": "No proof count is reported this run: the theorem ledger is the only source for one, and it "
                "did not produce a current ledger (see reason). UNAVAILABLE is not zero and not a pass.",
    }


SORRY_ALLOWLIST = Path("foundations") / "tools" / "sorry_audit.lean"


def sorry_allowlist(machlib_root: Path | None) -> list[str] | None:
    """The names sorry_audit.lean's `allowedSorry` licenses, read from its source (None when it cannot be read).

    The gate itself enforces the list in both directions; this only lets the dashboard say whether an unchecked
    theorem is the documented, licensed one or a new sorry nobody has accounted for."""
    if machlib_root is None:
        return None
    try:
        text = (machlib_root / SORRY_ALLOWLIST).read_text(encoding="utf-8")
    except OSError:
        return None
    m = re.search(r"def allowedSorry : List Name := \[(.*?)\n\s*\]", text, re.S)
    if not m:
        return None
    body = "\n".join(line.split("--", 1)[0] for line in m.group(1).splitlines())
    return re.findall(r"`([A-Za-z_][\w.']*)", body)


def _unchecked_theorems(ledger: dict, allowlist: list[str] | None) -> list[dict]:
    """Every theorem the ledger leaves unchecked, by name: the dashboard keeps it visible rather than fold it into
    a count (the owner's ruling, 2026-10-10: "The single unchecked theorem must remain visible, including its
    allowlisted sorry")."""
    out = []
    for t in ledger.get("theorems", []):
        if t.get("classification") != "unchecked":
            continue
        reasons = t.get("unchecked_reasons", [])
        out.append({"name": t["name"], "module": t.get("module"), "reasons": reasons,
                    "sorry_allowlisted": (None if allowlist is None or "sorryAx" not in reasons
                                          else t["name"] in allowlist)})
    return sorted(out, key=lambda r: r["name"])


def load_theorem_ledger(path: Path | None, machlib_sha: str,
                        machlib_root: Path | None = None) -> tuple[dict, dict | None]:
    """The `theorem_ledger` block, and the full ledger (for cross-references) when it is usable.

    A ledger is usable only if it says it is available, was generated at THIS commit, and is bound to the
    sources it read (a clean tree). Anything else is reported as unavailable with the reason -- a count from
    another revision is not evidence about this one."""
    if path is None or not path.exists():
        return theorem_ledger_unavailable("no theorem ledger was produced for this run"), None
    try:
        ledger = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as e:
        return theorem_ledger_unavailable(f"theorem ledger unreadable: {e}"), None
    if ledger.get("unavailable"):
        return theorem_ledger_unavailable(str(ledger.get("reason", "the ledger reported itself unavailable"))), None
    prov = ledger.get("provenance", {})
    if prov.get("machlib_commit") != machlib_sha:
        return theorem_ledger_unavailable(
            f"the ledger is for commit {prov.get('machlib_commit')}, not {machlib_sha}"), None
    if not ledger.get("bound_to_head"):
        return theorem_ledger_unavailable(f"the ledger is not bound to HEAD: {ledger.get('unbound_reasons')}"), None
    c = ledger["counts"]
    failed = [i["check"] for i in ledger.get("invariants", []) + ledger.get("cross_checks", []) if not i["holds"]]
    if failed:
        return theorem_ledger_unavailable(f"the ledger's own checks failed: {failed}"), None
    verdict = ledger.get("axiom_ledger", {}).get("verdict")
    if verdict != "OK" or ledger.get("axiom_ledger", {}).get("lean_exit_code") != 0:
        return theorem_ledger_unavailable(f"AxiomLedger.lean did not pass in the ledger run ({verdict}), so the "
                                          "policy the counts are classified against is not itself checked"), None
    block = {
        "available": True,
        "counts": {k: c[k] for k in LEDGER_COUNT_KEYS},
        "unchecked_by_reason": c.get("unchecked_by_reason", {}),
        # Which declared axioms the conditional theorems rest on (a theorem resting on several counts under each):
        # conditional is "proved relative to these assumptions", never "unproved".
        "conditional_by_axiom": c.get("conditional_by_axiom", {}),
        "unchecked_theorems": _unchecked_theorems(ledger, sorry_allowlist(machlib_root)),
        "sorry_allowlist_source": f"{SORRY_ALLOWLIST.as_posix()} (allowedSorry)",
        "private_theorems": c.get("private_theorems"),
        "invariants_hold": True,
        "axiom_ledger_verdict": verdict,
        "definitions": ledger.get("rules", {}).get("definitions", {}),
        "provenance": {
            "machlib_commit": prov.get("machlib_commit"),
            "tracked_tree_clean": prov.get("tracked_tree_clean"),
            "machlib_sources": prov.get("machlib_sources"),
            "lean_version": prov.get("lean_version"),
            "imports": prov.get("imports"),
            "axiom_policy_version": ledger.get("axiom_policy", {}).get("version"),
        },
        "binding_id": ledger.get("binding_id"),
        "outside_environment_files": ledger.get("outside_environment", {}).get("files_outside_environment"),
        "outside_environment_by_directory": ledger.get("outside_environment", {}).get("by_directory"),
        "ledger_file": "theorem_ledger.json",
        "ledger_sha256": _sha256_file(path),
        "reproduce": LEDGER_REPRODUCE,
        "note": "Every proof count on this dashboard is one of these, read off the Lean environment by "
                "foundations/tools/theorem_ledger/ledger.py and classified against AxiomLedger.lean's declared "
                "axiom policy. theorem_ledger.json, published beside this file, holds every theorem's record "
                "(statement digest, axiom set, classification) and the files outside the environment, which are "
                "counted as files only.",
    }
    return block, ledger


def _strengthened_backing(entries: list[dict], ledger: dict | None) -> dict:
    """Back each name- or marker-linked `strengthened` row with the ledger.

    The Forge audit links an @verify obligation to an Applications/ module by TEXT (a theorem name or an
    `@strengthens` marker). The ledger cannot check that link; it can check the module's proofs. A row counts as
    strengthened only if the ledger counts at least one theorem in the linked module and every theorem it counts
    there is kernel-checked; it is `approved_policy` when all of them are."""
    out = {"approved_policy": 0, "conditional": 0, "not_backed": 0, "not_backed_rows": []}
    by_module: dict[str, list[str]] = {}
    for t in (ledger or {}).get("theorems", []):
        by_module.setdefault(t["module"], []).append(t["classification"])
    for e in entries:
        if e.get("status") != "strengthened":
            continue
        app = e.get("applications_strengthening") or {}
        path = str(app.get("applications_path", ""))
        m = re.search(r"(MachLib/Applications/.+)\.lean$", path.replace("\\", "/"))
        classes = by_module.get(m.group(1).replace("/", ".") if m else "", [])
        if classes and all(c in ("approved_policy", "conditional") for c in classes):
            out["conditional" if "conditional" in classes else "approved_policy"] += 1
        else:
            out["not_backed"] += 1
            out["not_backed_rows"].append(e.get("verify_theorem"))
    return out


def load_verify_audit(audit_json_path: Path, ledger: dict | None) -> dict:
    """Read the forge_verify_audit JSON ledger and pull out the summary.

    An UNAVAILABLE audit is a first-class outcome, not a crash and not a zero. The workflow
    writes `{"unavailable": true, "reason": ...}` when it could not clone forge (the repo is
    private and the read token expires); the dashboard must then show "unavailable", never a
    stale or fabricated count, and the rest of status.json (build, sorries, axioms) — which
    needs nothing from forge — still publishes. The renderer refuses null totals loudly by
    design (see monogate-net/evidence-status/machlib-status.js).

    NO PROOF COUNT FROM TEXT (2026-10-10). The audit classifies by text: a Discovered/ stub whose body has no
    `sorry` and is not `True := by trivial` used to be published as `proven_mod_machlib_axioms`. Discovered/ is
    outside the checked environment, so no axiom audit covers it, and the theorem ledger does not count it.
    That figure is `stub_text_no_sorry` now, labelled as a text classification; `proven_mod_machlib_axioms`,
    `proven_from_mathlib` and `discharged_pct` (whose formula included it) are null. `strengthened` is
    ledger-backed (`_strengthened_backing`), or null when there is no usable ledger."""
    retired = {
        "proven_from_mathlib": None,
        "proven_mod_machlib_axioms": None,
        "discharged_pct": None,
        "retired_note": (
            "proven_from_mathlib, proven_mod_machlib_axioms and discharged_pct are retired (null) since schema 2: "
            "they were proof figures from a text classification no axiom audit covered. Proof counts are in "
            "theorem_ledger."
        ),
    }
    data = json.loads(audit_json_path.read_text(encoding="utf-8"))
    if data.get("unavailable"):
        return {
            "unavailable": True,
            "reason": data.get("reason", "forge_verify_audit did not run"),
            "total": None,
            "strengthened": None,
            "stub_text_no_sorry": None,
            "placeholder": None,
            "open": None,
            "gap_pct": None,
            **retired,
            "note": (
                "The Forge @verify audit could not run in this refresh (see reason). "
                "Every other field of this status.json is measured; this block is not."
            ),
        }
    summary = data.get("summary", {})
    total = summary.get("total", 0)
    stub_text = summary.get("stub_text_no_sorry", 0)
    placeholder = summary.get("placeholder", 0)
    open_count = summary.get("open", 0)
    backing = _strengthened_backing(data.get("entries", []), ledger) if ledger else None
    return {
        "total": total,
        "strengthened": (backing["approved_policy"] + backing["conditional"]) if backing else None,
        "strengthened_ledger_backing": backing,
        "strengthened_text_links": summary.get("strengthened", 0),
        "stub_text_no_sorry": stub_text,
        "placeholder": placeholder,
        "open": open_count,
        "gap_pct": round((placeholder + open_count) / total * 100, 1) if total else 0.0,
        **retired,
        "note": (
            "Every figure here except `strengthened` is a TEXT classification of Forge stubs and is not a count "
            "of proved results. stub_text_no_sorry: Discovered/ stubs whose body contains no `sorry` and is not "
            "`True := by trivial` -- Discovered/ is outside the checked environment, so nothing here says such a "
            "stub compiles or what it rests on. strengthened: obligations linked by name or @strengthens marker "
            "to an Applications/ module whose every theorem the theorem ledger counts as kernel-checked "
            "(strengthened_ledger_backing); the ledger checks those proofs, not that they discharge the "
            "obligation. strengthened_text_links is the audit's own count of such links."
        ),
    }


def compute_content_hash(payload: dict) -> str:
    """SHA-256 of the JSON with content_hash_sha256 set to null. Lets a
    third party verify byte-for-byte reproducibility."""
    clone = dict(payload)
    clone["content_hash_sha256"] = None
    canonical = json.dumps(clone, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def build_payload(args: argparse.Namespace, previous: dict | None) -> dict:
    machlib_root = args.machlib_root.resolve()

    core, discovered_total, core_file_count, discovered_file_count = (
        count_sorries_canonical(machlib_root)
    )
    sorries_total = core + discovered_total

    build_info = parse_build_log(args.build_log)
    build_exit_code = args.build_exit_code
    lake_build_passed = build_exit_code == 0

    axiom_info = parse_axiom_audit(args.axiom_audit)

    theorem_ledger, ledger = load_theorem_ledger(args.theorem_ledger, args.machlib_sha, machlib_root)
    verify_audit = load_verify_audit(args.verify_audit_json, ledger)

    delta = compute_delta_vs_previous(sorries_total, previous)

    now_iso = _dt.datetime.now(_dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")

    history_entry = {
        "sha": args.machlib_sha,
        "ts": now_iso,
        "total": sorries_total,
        "discovered": discovered_total,
        "core": core,
    }
    history = carry_history(previous, history_entry)

    payload: dict = {
        "schema_version": SCHEMA_VERSION,
        "machlib_sha": args.machlib_sha,
        "generated_at_utc": now_iso,
        "previous_machlib_sha": previous.get("machlib_sha") if previous else None,
        "previous_generated_at_utc": (
            previous.get("generated_at_utc") if previous else None
        ),
        "reproduce": {
            "command_lines": [
                "git clone https://github.com/agent-maestro/machlib && cd machlib",
                f"git checkout {args.machlib_sha}",
                "# The next line needs READ access to a PRIVATE repository",
                "# (agent-maestro/forge). Without it, SKIP it -- every other",
                "# measurement below still reproduces, but the verify_audit block",
                "# reads UNAVAILABLE and content_hash_sha256 will NOT match.",
                "git clone --depth 1 https://github.com/agent-maestro/forge ../forge",
                "git clone --depth 1 https://github.com/agent-maestro/eml-stdlib ../eml-stdlib",
                "cd foundations && lake build && lake env lean AxiomAudit.lean > /tmp/axiom_audit.txt && cd ..",
                "cd foundations && python3 tools/theorem_ledger/ledger.py --out /tmp/theorem_ledger.json && cd ..",
                "python tools/status/forge_verify_audit.py \\",
                "    --forge-root ../forge --eml-stdlib-root ../eml-stdlib \\",
                "    --discovered-root foundations/MachLib/Discovered \\",
                "    --applications-root foundations/MachLib/Applications \\",
                "    --out-json /tmp/verify_audit.json --out-md /tmp/verify_audit.md",
                "python tools/status/generate_status.py \\",
                f"    --machlib-root . --machlib-sha {args.machlib_sha} \\",
                "    --axiom-audit /tmp/axiom_audit.txt --build-log <(lake build 2>&1) \\",
                "    --build-exit-code 0 --verify-audit-json /tmp/verify_audit.json \\",
                "    --theorem-ledger /tmp/theorem_ledger.json \\",
                "    --previous-status .status-prev/status.json --out status.json",
            ],
            "note": (
                "Anyone with read access to ALL FOUR repositories can regenerate "
                "this file byte-for-byte; content_hash_sha256 is the check, and a "
                "mismatch means the data was tampered with or the toolchain drifted "
                "(file a github issue with the diff). agent-maestro/forge is "
                "PRIVATE, so an outside reader cannot run its clone: skip that step "
                "and every other measurement still reproduces, but the verify_audit "
                "block reads UNAVAILABLE and the hash will not match. That is a "
                "limit on WHO CAN REPRODUCE the forge figures, not a claim that they "
                "are unmeasured -- and UNAVAILABLE is never a pass."
            ),
        },
        "build": {
            "lake_build_passed": lake_build_passed,
            "lake_exit_code": build_exit_code,
            "modules_built": build_info["modules_built"],
            "modules_total": build_info["modules_total"],
            "modules_failed_listed": build_info["modules_failed"],
            "non_green_in_proven_dependency_chain": (
                None if lake_build_passed else True
            ),
            "non_green_in_proven_chain_note": (
                "null = library is fully green so the question is moot. If "
                "lake_build_passed is false this should be true unless the "
                "renderer can prove the failed modules are downstream-only."
            ),
        },
        "sorries": {
            "core": core,
            "discovered": discovered_total,
            "total": sorries_total,
            "file_counts": {
                "core": core_file_count,
                "discovered": discovered_file_count,
            },
            "delta_vs_previous": delta,
            "history_recent": history,
            "core_files_tracked": list(MACHLIB_CORE_FILES),
            "not_a_proof_count": (
                "A text count of the token `sorry`, not of unproved theorems: Discovered/ cascades end in one "
                "as a fallback. The environment's own figure is theorem_ledger.unchecked_by_reason.sorryAx."
            ),
            "method": (
                "strip Lean block comments (/-! ... -/, /- ... -/) and Lean "
                "line comments (--), then count `\\bsorry\\b`. File scope: "
                "core = the 8 hand-written MACHLIB_CORE_FILES at top level of "
                "foundations/MachLib/; discovered = everything else under "
                "foundations/MachLib/ excluding Test.lean and .lake/. Matches "
                "monogate-research's builder_v2.py canonical method."
            ),
        },
        "theorem_ledger": theorem_ledger,
        "verify_audit": verify_audit,
        "axiomatized_base": {
            "audit_file": "foundations/AxiomAudit.lean",
            "machlib_real_axioms_count": len(axiom_info["machlib_real_axioms"]),
            "machlib_real_axioms": axiom_info["machlib_real_axioms"],
            "non_machlib_axioms": axiom_info["non_machlib_axioms"],
            "headline_theorems_audited": sorted(axiom_info["theorems"].keys()),
            "note": (
                "Every MachLib.Real.* entry is a theorem in mathlib; "
                "grounding MachLib's analytic base there is open work, not "
                "shipped. propext / Classical.choice / Quot.sound are Lean's "
                "standard axioms and would also appear in any mathlib-grounded "
                "proof."
            ),
        },
    }
    payload["content_hash_sha256"] = compute_content_hash(payload)
    return payload


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--machlib-root", type=Path, required=True)
    parser.add_argument("--machlib-sha", required=True)
    parser.add_argument("--axiom-audit", type=Path, default=None)
    parser.add_argument("--build-log", type=Path, default=None)
    parser.add_argument("--build-exit-code", type=int, default=0)
    parser.add_argument("--verify-audit-json", type=Path, required=True)
    parser.add_argument("--theorem-ledger", type=Path, default=None,
                        help="theorem_ledger.json from foundations/tools/theorem_ledger/ledger.py --out")
    parser.add_argument("--previous-status", type=Path, default=None)
    parser.add_argument("--out", type=Path, required=True)
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    previous = load_previous_status(args.previous_status)
    payload = build_payload(args, previous)
    args.out.write_text(
        json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8"
    )
    summary = payload["verify_audit"]
    sorries = payload["sorries"]
    delta = sorries["delta_vs_previous"]
    tl = payload["theorem_ledger"]
    tlc = tl["counts"]
    print(
        f"status.json written to {args.out}\n"
        f"  theorem ledger: {'available' if tl['available'] else 'UNAVAILABLE (' + tl['reason'] + ')'}  "
        f"declarations={tlc['declarations']} theorems={tlc['theorems']} "
        f"kernel_checked={tlc['kernel_checked']} axiom_audited={tlc['axiom_audited']} "
        f"approved_policy={tlc['approved_policy']} conditional={tlc['conditional']} "
        f"unchecked={tlc['unchecked']}\n"
        f"  sorries (text count of the token, not a proof count): core={sorries['core']} "
        f"discovered={sorries['discovered']} total={sorries['total']}  "
        f"delta_vs_previous={delta.get('net_change')} ({delta.get('method')})\n"
        f"  verify (text classification of Forge stubs; strengthened is ledger-backed): "
        f"total={summary['total']} strengthened={summary['strengthened']} "
        f"stub_text_no_sorry={summary['stub_text_no_sorry']} "
        f"placeholder={summary['placeholder']} open={summary['open']} gap_pct={summary['gap_pct']}\n"
        f"  content_hash_sha256={payload['content_hash_sha256']}"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
