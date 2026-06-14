#!/usr/bin/env python3
"""Forge `@verify` propagation audit.

NOTE: this file is a copy of monogate-research/tools/forge_verify_audit/
forge_verify_audit.py, embedded here so machlib's CI is self-sufficient
(monogate-research is a private repo; the default GITHUB_TOKEN cannot
clone it). If you edit this file, sync the change to monogate-research,
or vice-versa. Long-term this should be a published Python package
both repos depend on; for now, duplication is the deliberate trade.


Cross-references three sources:

  1. Forge `.eml` annotations: `@verify(lean, theorem = "X")` lines (and
     their containing `fn`).
  2. `MachLib/Discovered/*.lean`: the Forge backend's emitted theorem stubs.
     A stub is classified as `placeholder_true` (body `True := by trivial`),
     `sorry` (body contains `sorry`), or `proven` (otherwise).
  3. `MachLib/Applications/*.lean`: hand-authored strengthening proofs. We
     extract their theorems and any docstring backreference to a
     `MachLib/Discovered/...` path.

The output is a JSON ledger of every `@verify` obligation and its closure
status, plus an optional human-readable Markdown summary.

This is a read-only audit. It does not edit Lean files, run `lake`, or
mutate `.eml` sources. It exists so the propagation gap from Forge stub
to strengthened Applications/ proof is visible at a glance instead of
being discovered file-by-file.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import asdict, dataclass, field
from pathlib import Path

VERIFY_RE = re.compile(
    r'@verify\s*\(\s*lean\s*,\s*theorem\s*=\s*"(?P<theorem>[^"]+)"\s*\)'
)
LEAN_DOC_COMMENT_RE = re.compile(r'/-[!]?(?:[^-]|-(?!/))*-/', re.DOTALL)


def strip_lean_doc_comments(text: str) -> str:
    """Replace `/- ... -/` and `/-! ... -/` blocks with blank lines so
    theorem-name regexes don't fire on quoted Lean inside docstrings."""

    def _blank(match: re.Match[str]) -> str:
        return "\n" * match.group(0).count("\n")

    return LEAN_DOC_COMMENT_RE.sub(_blank, text)
FN_RE = re.compile(r'^\s*fn\s+(?P<fn>[A-Za-z_][A-Za-z0-9_]*)\s*\(')
LEAN_THEOREM_RE = re.compile(
    r'^\s*theorem\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)\b',
    re.MULTILINE,
)
DISCOVERED_REF_RE = re.compile(r'MachLib[/\.]Discovered[/\.][A-Za-z_][A-Za-z0-9_]*')
# Explicit propagation marker. Format:
#   -- @strengthens verify_theorem_1, verify_theorem_2
# Picked up by the audit so the Applications/ proof is credited even when its
# Lean theorem name doesn't textually match the Forge @verify theorem name.
STRENGTHENS_RE = re.compile(
    r'--\s*@strengthens\s+([A-Za-z_][A-Za-z0-9_,\s]*)$',
    re.MULTILINE,
)


@dataclass
class VerifyObligation:
    """A single `@verify(lean, ...)` annotation in a `.eml` source."""

    eml_path: str
    eml_module: str  # filename stem
    kernel_fn: str | None
    verify_theorem: str
    source_root: str  # "forge" | "eml-stdlib"


@dataclass
class DiscoveredStub:
    """A `theorem` definition in `MachLib/Discovered/*.lean`."""

    discovered_path: str
    discovered_module: str
    theorem_name: str
    status: str  # "placeholder_true" | "sorry" | "proven"


@dataclass
class ApplicationsProof:
    """A `theorem` in `MachLib/Applications/*.lean` plus any Discovered
    backreference."""

    applications_path: str
    applications_module: str
    theorem_name: str
    namespace_path: str  # e.g. "MachLib.Forge.DefibrillatorEnergy"
    discovered_backrefs: list[str] = field(default_factory=list)
    strengthens: list[str] = field(default_factory=list)


@dataclass
class LedgerEntry:
    """One row of the cross-referenced ledger — pivots on
    `verify_theorem`."""

    verify_theorem: str
    obligation: VerifyObligation
    discovered_stub: DiscoveredStub | None
    applications_strengthening: ApplicationsProof | None
    status: str  # "open" | "placeholder" | "strengthened" | "proven_in_place"


def scan_eml_verify(eml_root: Path, source_root_label: str) -> list[VerifyObligation]:
    """Scan a directory tree of `.eml` files for `@verify(lean, ...)`."""
    out: list[VerifyObligation] = []
    if not eml_root.exists():
        return out
    for eml_file in sorted(eml_root.rglob("*.eml")):
        try:
            text = eml_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        last_fn: str | None = None
        for line in text.splitlines():
            fn_match = FN_RE.match(line)
            if fn_match:
                last_fn = fn_match.group("fn")
                continue
            for verify_match in VERIFY_RE.finditer(line):
                out.append(
                    VerifyObligation(
                        eml_path=str(eml_file),
                        eml_module=eml_file.stem,
                        kernel_fn=last_fn,
                        verify_theorem=verify_match.group("theorem"),
                        source_root=source_root_label,
                    )
                )
    return out


def classify_theorem_body(text: str, theorem_start: int) -> str:
    """Return one of `placeholder_true`, `sorry`, `proven`.

    Looks at the body of a `theorem` starting at `theorem_start` up to the
    next top-level `theorem`, `def`, `end`, or end-of-file. The body
    classification cares only about coarse markers, not full parsing."""
    rest = text[theorem_start:]
    # Find the body boundary — next top-level keyword, or 200 lines of safety.
    upper_bound = len(rest)
    for marker in ("\ntheorem ", "\ndef ", "\nnoncomputable def ", "\nend ", "\nnamespace "):
        idx = rest.find(marker, 1)
        if idx != -1 and idx < upper_bound:
            upper_bound = idx
    body = rest[:upper_bound]
    if re.search(r":\s*True\s*:=\s*by\s*trivial", body):
        return "placeholder_true"
    if re.search(r"\bsorry\b", body):
        return "sorry"
    return "proven"


def scan_discovered(discovered_root: Path) -> list[DiscoveredStub]:
    out: list[DiscoveredStub] = []
    if not discovered_root.exists():
        return out
    for lean_file in sorted(discovered_root.rglob("*.lean")):
        try:
            raw = lean_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        text = strip_lean_doc_comments(raw)
        for match in LEAN_THEOREM_RE.finditer(text):
            status = classify_theorem_body(text, match.start())
            out.append(
                DiscoveredStub(
                    discovered_path=str(lean_file),
                    discovered_module=lean_file.stem,
                    theorem_name=match.group("name"),
                    status=status,
                )
            )
    return out


NAMESPACE_RE = re.compile(r'^\s*namespace\s+([A-Za-z_][A-Za-z0-9_.]*)\b', re.MULTILINE)


def scan_applications(applications_root: Path) -> list[ApplicationsProof]:
    out: list[ApplicationsProof] = []
    if not applications_root.exists():
        return out
    for lean_file in sorted(applications_root.rglob("*.lean")):
        try:
            raw = lean_file.read_text(encoding="utf-8")
        except (OSError, UnicodeDecodeError):
            continue
        # The @strengthens markers live in comments; keep them in `raw`.
        # The theorem regex runs on the stripped text so docstring-embedded
        # `theorem` quotes don't get mistaken for real definitions.
        text = strip_lean_doc_comments(raw)
        namespaces = [m.group(1) for m in NAMESPACE_RE.finditer(text)]
        namespace_path = ".".join(namespaces) if namespaces else ""
        discovered_backrefs = sorted(set(DISCOVERED_REF_RE.findall(raw)))
        strengthens: list[str] = []
        for raw_marker in STRENGTHENS_RE.findall(raw):
            for name in raw_marker.split(","):
                name = name.strip()
                if name:
                    strengthens.append(name)
        for match in LEAN_THEOREM_RE.finditer(text):
            out.append(
                ApplicationsProof(
                    applications_path=str(lean_file),
                    applications_module=lean_file.stem,
                    theorem_name=match.group("name"),
                    namespace_path=namespace_path,
                    discovered_backrefs=discovered_backrefs,
                    strengthens=strengthens,
                )
            )
    return out


def build_ledger(
    obligations: list[VerifyObligation],
    discovered: list[DiscoveredStub],
    applications: list[ApplicationsProof],
) -> list[LedgerEntry]:
    discovered_by_name: dict[str, DiscoveredStub] = {}
    for stub in discovered:
        discovered_by_name.setdefault(stub.theorem_name, stub)

    apps_by_theorem: dict[str, ApplicationsProof] = {}
    for proof in applications:
        apps_by_theorem.setdefault(proof.theorem_name, proof)

    # Strengthens map: explicit `-- @strengthens X` markers in Applications/
    # files take precedence over name-based heuristics.
    strengthens_map: dict[str, ApplicationsProof] = {}
    for proof in applications:
        for name in proof.strengthens:
            strengthens_map.setdefault(name, proof)

    def find_strengthening(
        verify_theorem: str, stub: DiscoveredStub | None
    ) -> ApplicationsProof | None:
        # 1. Explicit marker — strongest signal.
        if verify_theorem in strengthens_map:
            return strengthens_map[verify_theorem]
        # 2. Exact theorem-name match.
        if verify_theorem in apps_by_theorem:
            return apps_by_theorem[verify_theorem]
        return None

    entries: list[LedgerEntry] = []
    for ob in obligations:
        stub = discovered_by_name.get(ob.verify_theorem)
        strengthening = find_strengthening(ob.verify_theorem, stub)
        if strengthening is not None:
            status = "strengthened"
        elif stub is None:
            status = "open"
        elif stub.status == "placeholder_true":
            status = "placeholder"
        elif stub.status == "sorry":
            status = "open"
        else:
            status = "proven_in_place"
        entries.append(
            LedgerEntry(
                verify_theorem=ob.verify_theorem,
                obligation=ob,
                discovered_stub=stub,
                applications_strengthening=strengthening,
                status=status,
            )
        )
    return entries


def write_json(entries: list[LedgerEntry], out_path: Path) -> None:
    payload = {
        "entries": [
            {
                "verify_theorem": e.verify_theorem,
                "status": e.status,
                "obligation": asdict(e.obligation),
                "discovered_stub": asdict(e.discovered_stub)
                if e.discovered_stub
                else None,
                "applications_strengthening": asdict(e.applications_strengthening)
                if e.applications_strengthening
                else None,
            }
            for e in entries
        ],
        "summary": summarize(entries),
    }
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=False) + "\n", encoding="utf-8")


def summarize(entries: list[LedgerEntry]) -> dict[str, int]:
    counts: dict[str, int] = {"open": 0, "placeholder": 0, "strengthened": 0, "proven_in_place": 0}
    for e in entries:
        counts[e.status] = counts.get(e.status, 0) + 1
    counts["total"] = len(entries)
    return counts


def write_markdown(entries: list[LedgerEntry], out_path: Path) -> None:
    summary = summarize(entries)
    lines: list[str] = []
    lines.append("# Forge `@verify` propagation status")
    lines.append("")
    lines.append("Generated by `tools/forge_verify_audit/forge_verify_audit.py`.")
    lines.append("")
    lines.append(
        f"**Total `@verify` obligations:** {summary['total']}  "
        f"· strengthened: {summary['strengthened']}  "
        f"· placeholder: {summary['placeholder']}  "
        f"· open: {summary['open']}  "
        f"· proven-in-place: {summary['proven_in_place']}"
    )
    lines.append("")
    lines.append("## Status")
    lines.append("")
    lines.append("| Theorem | Status | EML module | Discovered status | Applications strengthening |")
    lines.append("|---|---|---|---|---|")
    for e in sorted(entries, key=lambda x: (x.status, x.verify_theorem)):
        stub_status = e.discovered_stub.status if e.discovered_stub else "—"
        app = (
            e.applications_strengthening.applications_module
            if e.applications_strengthening
            else "—"
        )
        lines.append(
            f"| `{e.verify_theorem}` | {e.status} | `{e.obligation.eml_module}` "
            f"| {stub_status} | {app} |"
        )
    lines.append("")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--forge-root", type=Path, required=True, help="path to forge/")
    parser.add_argument(
        "--eml-stdlib-root", type=Path, required=True, help="path to eml-stdlib/"
    )
    parser.add_argument(
        "--discovered-root",
        type=Path,
        required=True,
        help="path to machlib/foundations/MachLib/Discovered/",
    )
    parser.add_argument(
        "--applications-root",
        type=Path,
        required=True,
        help="path to machlib/foundations/MachLib/Applications/",
    )
    parser.add_argument("--out-json", type=Path, required=True, help="output JSON ledger path")
    parser.add_argument(
        "--out-md", type=Path, default=None, help="optional human-readable Markdown summary"
    )
    parser.add_argument(
        "--gaps-only",
        action="store_true",
        help="print only obligations with status open|placeholder to stdout",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    obligations = (
        scan_eml_verify(args.forge_root, "forge")
        + scan_eml_verify(args.eml_stdlib_root, "eml-stdlib")
    )
    discovered = scan_discovered(args.discovered_root)
    applications = scan_applications(args.applications_root)
    entries = build_ledger(obligations, discovered, applications)
    write_json(entries, args.out_json)
    if args.out_md is not None:
        write_markdown(entries, args.out_md)
    summary = summarize(entries)
    print(
        f"forge_verify_audit: total={summary['total']} "
        f"strengthened={summary['strengthened']} "
        f"placeholder={summary['placeholder']} "
        f"open={summary['open']} "
        f"proven_in_place={summary['proven_in_place']}"
    )
    if args.gaps_only:
        for e in entries:
            if e.status in ("open", "placeholder"):
                print(
                    f"  {e.status:<11} {e.verify_theorem:<55} "
                    f"({e.obligation.source_root}:{e.obligation.eml_module})"
                )
    return 0


if __name__ == "__main__":
    sys.exit(main())
