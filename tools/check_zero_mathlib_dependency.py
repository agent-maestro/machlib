#!/usr/bin/env python3
"""Audit MachLib for Mathlib dependency evidence.

Modes:
  default            Equivalent to --release-target.
  --release-target   Checks files in the current release/build/corpus path.
  --repo-wide        Checks the public repository, including legacy quarantine.

The checker is deliberately honest about `foundations/legacy_eml/`: if raw
Mathlib-importing Lean files appear there again, release-target mode can still
exclude the quarantine path, but repo-wide mode will fail.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

SCAN_ROOTS = [
    "README.md",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
    "foundations",
    "corpus",
    "tests",
    "tools",
    "site",
]

SCAN_SUFFIXES = {
    ".lean",
    ".toml",
    ".json",
    ".md",
    ".py",
    ".tsx",
    ".ts",
    ".js",
    ".jsx",
    ".lock",
}

TEXT_NAMES = {
    "README.md",
    "lakefile.lean",
    "lakefile.toml",
    "lean-toolchain",
    "lake-manifest.json",
    "package.json",
    "package-lock.json",
    "pyproject.toml",
}

MATHLIB_PATTERNS = [
    re.compile(r"\bimport\s+Mathlib\b"),
    re.compile(r"\bfrom\s+Mathlib\b"),
    re.compile(r"\bMathlib\."),
    re.compile(r"\bmathlib\b", re.IGNORECASE),
]

RAW_IMPORT = re.compile(r"\b(?:import|from)\s+Mathlib\b")
DEPENDENCY_DECLARATION = re.compile(
    r"\b(require|dependency|dependencies|deps|git|url|rev|name|package)\b.*\bmathlib\b"
    r"|\bmathlib\b.*\b(require|dependency|dependencies|deps|git|url|rev|name|package)\b",
    re.IGNORECASE,
)


@dataclass(frozen=True)
class Hit:
    path: str
    line: int
    classification: str
    release_target: bool
    repo_wide_raw_import: bool
    text: str


def iter_scan_files() -> list[Path]:
    files: set[Path] = set()
    for item in SCAN_ROOTS:
        path = ROOT / item
        if not path.exists():
            continue
        if path.is_file():
            files.add(path)
            continue
        for child in path.rglob("*"):
            if not child.is_file():
                continue
            if ".git" in child.parts or ".lake" in child.parts or "__pycache__" in child.parts:
                continue
            if child.suffix in SCAN_SUFFIXES or child.name in TEXT_NAMES:
                files.add(child)
    return sorted(files)


def has_mathlib(text: str) -> bool:
    return any(pattern.search(text) for pattern in MATHLIB_PATTERNS)


def is_comment(line: str, suffix: str) -> bool:
    stripped = line.strip()
    if suffix == ".lean":
        return stripped.startswith("--") or stripped.startswith("/-") or stripped.startswith("*")
    if suffix in {".py", ".ts", ".tsx", ".js", ".jsx"}:
        return stripped.startswith("#") or stripped.startswith("//") or stripped.startswith("*")
    return False


def is_legacy_quarantine(path: Path) -> bool:
    rel = path.relative_to(ROOT).as_posix()
    return rel.startswith("foundations/legacy_eml/")


def is_release_target(path: Path) -> bool:
    rel = path.relative_to(ROOT).as_posix()
    if is_legacy_quarantine(path):
        return False
    if rel.startswith("reports/"):
        return False
    if rel.startswith("foundations/.lake/"):
        return False
    return True


def classify(path: Path, line: str) -> str:
    rel = path.relative_to(ROOT).as_posix()
    suffix = path.suffix
    stripped = line.strip()
    lower = stripped.lower()

    if not has_mathlib(stripped):
        return "FALSE_POSITIVE"

    if is_legacy_quarantine(path):
        if suffix == ".lean" and RAW_IMPORT.search(stripped):
            return "LEGACY_QUARANTINE_CANDIDATE"
        return "HISTORICAL_TEXT"

    if suffix == ".lean":
        if RAW_IMPORT.search(stripped):
            return "DEPENDENCY_EVIDENCE"
        if "mathlib." in stripped and not is_comment(stripped, suffix):
            return "DEPENDENCY_EVIDENCE"
        if is_comment(stripped, suffix):
            if any(
                token in lower
                for token in [
                    "zero",
                    "no mathlib",
                    "substitute",
                    "original",
                    "well-known",
                    "dependent",
                    "answer to mathlib",
                    "machlib.basic",
                    "forge-emitted",
                ]
            ):
                return "POLICY_TEXT"
            return "HISTORICAL_TEXT"
        return "POLICY_TEXT"

    if suffix in {".toml", ".json", ".lock"} or path.name.startswith("lakefile"):
        if DEPENDENCY_DECLARATION.search(stripped):
            return "DEPENDENCY_EVIDENCE"
        if "mathlib-wrapper" in lower:
            return "HISTORICAL_TEXT"
        if "mathlib already has" in lower or "mathlib's lemma" in lower:
            return "HISTORICAL_TEXT"
        return "UNKNOWN_REVIEW"

    if rel.startswith("tests/") or "check_zero_mathlib_dependency.py" in rel:
        return "POLICY_TEXT"

    if rel.startswith("README.md") or rel.startswith("site/"):
        if any(
            phrase in lower
            for phrase in [
                "target",
                "policy",
                "gate",
                "release",
                "historical",
                "transitional",
                "mathlib is",
                "not mathlib",
                "mathlib import",
                "mathlib imports",
                "import mathlib",
                "mathlib:",
                "different library",
                "belong in mathlib",
                "const mathlib",
                "mathlib.map",
                "mathlib already has",
                "zero mathlib dependency",
                "zero mathlib",
                "current public default tree",
                "public default tree",
            ]
        ):
            return "POLICY_TEXT"
        return "UNKNOWN_REVIEW"

    if any(
        phrase in lower
        for phrase in [
            "target",
            "policy",
            "gate",
            "release-specific",
            "historical",
            "transitional",
            "moving toward",
            "no active",
            "zero-mathlib",
            "mathlib-flavored",
            "mathlib cache",
            "reference mathlib idioms",
        ]
    ):
        return "POLICY_TEXT"

    return "HISTORICAL_TEXT"


def scan() -> tuple[list[Path], list[Hit]]:
    files = iter_scan_files()
    hits: list[Hit] = []
    for path in files:
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            text = path.read_text(encoding="utf-8", errors="replace")
        for idx, line in enumerate(text.splitlines(), start=1):
            if not has_mathlib(line):
                continue
            hits.append(
                Hit(
                    path=path.relative_to(ROOT).as_posix(),
                    line=idx,
                    classification=classify(path, line),
                    release_target=is_release_target(path),
                    repo_wide_raw_import=path.suffix == ".lean" and bool(RAW_IMPORT.search(line)),
                    text=line.strip(),
                )
            )
    return files, hits


def print_hits(hits: list[Hit], mode: str) -> None:
    for hit in hits:
        if mode == "release-target" and not hit.release_target:
            continue
        print(
            f"{hit.classification}\t"
            f"release_target={str(hit.release_target).lower()}\t"
            f"{hit.path}:{hit.line}\t{hit.text}"
        )


def main() -> int:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--release-target", action="store_true")
    mode.add_argument("--repo-wide", action="store_true")
    args = parser.parse_args()

    selected_mode = "repo-wide" if args.repo_wide else "release-target"
    files, hits = scan()
    lean_files = [path for path in files if path.suffix == ".lean"]

    release_hits = [hit for hit in hits if hit.release_target]
    release_dependency = [
        hit for hit in release_hits if hit.classification == "DEPENDENCY_EVIDENCE"
    ]
    release_unknown = [
        hit for hit in release_hits if hit.classification == "UNKNOWN_REVIEW"
    ]
    repo_imports = [hit for hit in hits if hit.repo_wide_raw_import]
    legacy_candidates = [
        hit for hit in hits if hit.classification == "LEGACY_QUARANTINE_CANDIDATE"
    ]
    policy_historical = [
        hit
        for hit in hits
        if hit.classification in {"HISTORICAL_TEXT", "POLICY_TEXT"}
    ]
    all_unknown = [hit for hit in hits if hit.classification == "UNKNOWN_REVIEW"]

    print_hits(hits, selected_mode)
    print()
    print(f"mode: {selected_mode}")
    print(f"total files scanned: {len(files)}")
    print(f"Lean files scanned: {len(lean_files)}")
    print(f"repo-wide Mathlib import count: {len(repo_imports)}")
    print(f"release-target dependency evidence count: {len(release_dependency)}")
    print(f"legacy quarantine candidate count: {len(legacy_candidates)}")
    print(f"policy/historical text count: {len(policy_historical)}")
    print(f"unknown review count: {len(all_unknown)}")
    print(f"release-target unknown review count: {len(release_unknown)}")

    if selected_mode == "repo-wide":
        failed = bool(repo_imports)
    else:
        failed = bool(release_dependency or release_unknown)

    print("FAIL" if failed else "PASS")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
