"""Small local scanner for direct Mathlib dependency evidence."""

from __future__ import annotations

from dataclasses import dataclass, field
from fnmatch import fnmatch
from pathlib import Path
from typing import Iterable


DIRECT_PATTERNS = {
    "IMPORT_MATHLIB": "import " + "Mathlib",
    "FROM_MATHLIB": "from " + "Mathlib",
    "MATHLIB_DOT_REFERENCE": "Mathlib" + ".",
}
DEPENDENCY_FILENAMES = {"lakefile.lean", "lake-manifest.json", "lakefile.toml"}
DEPENDENCY_HINTS = ("mathlib", "leanprover-community/mathlib")
POLICY_MARKERS = ("POLICY_TEXT", "HISTORICAL_TEXT", "NO_DEPENDENCY_CLAIM_TEXT")
DEFAULT_EXCLUDE_DIRS = {
    ".git",
    ".venv",
    "__pycache__",
    "node_modules",
    "dist",
    "build",
    ".mypy_cache",
    ".pytest_cache",
}
DEFAULT_TEXT_SUFFIXES = {
    ".lean",
    ".toml",
    ".json",
    ".md",
    ".txt",
    ".py",
    ".yml",
    ".yaml",
    ".cfg",
    ".ini",
}


@dataclass
class Evidence:
    path: str
    line: int
    pattern: str
    text: str
    evidence_type: str


@dataclass
class ScanResult:
    root: str
    scanned_files: int = 0
    skipped_files: int = 0
    direct_match_count: int = 0
    dependency_evidence_count: int = 0
    policy_text_count: int = 0
    evidence: list[Evidence] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return self.dependency_evidence_count == 0

    def to_dict(self) -> dict[str, object]:
        return {
            "root": self.root,
            "scanned_files": self.scanned_files,
            "skipped_files": self.skipped_files,
            "direct_match_count": self.direct_match_count,
            "dependency_evidence_count": self.dependency_evidence_count,
            "policy_text_count": self.policy_text_count,
            "passed": self.passed,
            "evidence": [item.__dict__ for item in self.evidence],
        }


def iter_files(root: Path, exclude_dirs: set[str]) -> Iterable[Path]:
    for path in root.rglob("*"):
        if path.is_file() and not any(part in exclude_dirs for part in path.parts):
            yield path


def is_policy_line(text: str) -> bool:
    return any(marker in text for marker in POLICY_MARKERS)


def suffix_allowed(path: Path, include: tuple[str, ...]) -> bool:
    if include:
        return any(fnmatch(path.name, pattern) or fnmatch(str(path), pattern) for pattern in include)
    if path.name in DEPENDENCY_FILENAMES:
        return True
    return path.suffix.lower() in DEFAULT_TEXT_SUFFIXES


def scan_path(
    root: Path,
    *,
    allow_policy_text: bool = False,
    include: tuple[str, ...] = (),
    exclude_dirs: tuple[str, ...] = (),
) -> ScanResult:
    root = root.resolve()
    all_exclude_dirs = DEFAULT_EXCLUDE_DIRS | set(exclude_dirs)
    result = ScanResult(root=str(root))
    for path in iter_files(root, all_exclude_dirs):
        if not suffix_allowed(path, include):
            result.skipped_files += 1
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            result.skipped_files += 1
            continue
        result.scanned_files += 1
        rel = str(path.relative_to(root))
        for lineno, line in enumerate(lines, start=1):
            if allow_policy_text and is_policy_line(line):
                result.policy_text_count += 1
                continue
            for evidence_type, pattern in DIRECT_PATTERNS.items():
                if pattern in line:
                    result.direct_match_count += 1
                    result.dependency_evidence_count += 1
                    result.evidence.append(Evidence(rel, lineno, pattern, line.strip(), evidence_type))
            if path.name in DEPENDENCY_FILENAMES:
                lower = line.lower()
                if any(hint in lower for hint in DEPENDENCY_HINTS):
                    result.dependency_evidence_count += 1
                    result.evidence.append(
                        Evidence(
                            rel,
                            lineno,
                            "mathlib dependency text",
                            line.strip(),
                            "MATHLIB_DEPENDENCY_DECLARATION",
                        )
                    )
    return result


def scan_root(root: Path, allow_policy_text: bool = False) -> ScanResult:
    return scan_path(root, allow_policy_text=allow_policy_text)
