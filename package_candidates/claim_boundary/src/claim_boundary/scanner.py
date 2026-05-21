"""Local scanner for claim-boundary and no-go text."""

from __future__ import annotations

from dataclasses import dataclass, field
from fnmatch import fnmatch
from pathlib import Path
from typing import Iterable

from .patterns import (
    BOUNDARY_PATTERNS,
    DEFAULT_EXCLUDE_DIRS,
    DEFAULT_TEXT_SUFFIXES,
    POLICY_MARKERS,
    SUSPICIOUS_PATTERNS,
    TOKEN_PATTERNS,
)


@dataclass
class ClaimFinding:
    path: str
    line: int
    finding_class: str
    text: str
    suspicious: bool


@dataclass
class ClaimScanResult:
    root: str
    scanned_file_count: int = 0
    skipped_file_count: int = 0
    suspicious_finding_count: int = 0
    boundary_text_count: int = 0
    policy_text_count: int = 0
    token_like_secret_count: int = 0
    findings: list[ClaimFinding] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return self.suspicious_finding_count == 0

    def to_dict(self) -> dict[str, object]:
        return {
            "root": self.root,
            "scanned_file_count": self.scanned_file_count,
            "skipped_file_count": self.skipped_file_count,
            "suspicious_finding_count": self.suspicious_finding_count,
            "boundary_text_count": self.boundary_text_count,
            "policy_text_count": self.policy_text_count,
            "token_like_secret_count": self.token_like_secret_count,
            "passed": self.passed,
            "findings": [item.__dict__ for item in self.findings],
        }


def iter_files(root: Path, exclude_dirs: set[str]) -> Iterable[Path]:
    for path in root.rglob("*"):
        if path.is_file() and not any(part in exclude_dirs for part in path.parts):
            yield path


def suffix_allowed(path: Path, include: tuple[str, ...]) -> bool:
    if include:
        return any(fnmatch(path.name, pattern) or fnmatch(str(path), pattern) for pattern in include)
    return path.suffix.lower() in DEFAULT_TEXT_SUFFIXES


def is_boundary_text(line: str) -> bool:
    lower = line.lower()
    return any(pattern.lower() in lower for pattern in BOUNDARY_PATTERNS)


def is_policy_text(line: str) -> bool:
    return any(marker in line for marker in POLICY_MARKERS)


def add_suspicious(result: ClaimScanResult, rel: str, lineno: int, finding_class: str, line: str) -> None:
    result.suspicious_finding_count += 1
    result.findings.append(ClaimFinding(rel, lineno, finding_class, line.strip(), True))


def scan_path(
    root: Path,
    *,
    include: tuple[str, ...] = (),
    exclude_dirs: tuple[str, ...] = (),
) -> ClaimScanResult:
    root = root.resolve()
    result = ClaimScanResult(root=str(root))
    all_exclude_dirs = DEFAULT_EXCLUDE_DIRS | set(exclude_dirs)

    for path in iter_files(root, all_exclude_dirs):
        if not suffix_allowed(path, include):
            result.skipped_file_count += 1
            continue
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            result.skipped_file_count += 1
            continue
        result.scanned_file_count += 1
        rel = str(path.relative_to(root))
        for lineno, line in enumerate(lines, start=1):
            if is_boundary_text(line):
                result.boundary_text_count += 1
                result.findings.append(ClaimFinding(rel, lineno, "NEGATED_NO_GO_TEXT", line.strip(), False))
                continue
            if is_policy_text(line):
                result.policy_text_count += 1
                result.findings.append(ClaimFinding(rel, lineno, "POLICY_BOUNDARY_TEXT", line.strip(), False))
                continue
            for finding_class, patterns in SUSPICIOUS_PATTERNS.items():
                lower = line.lower()
                if any(pattern.lower() in lower for pattern in patterns):
                    add_suspicious(result, rel, lineno, finding_class, line)
            for token_pattern in TOKEN_PATTERNS:
                if token_pattern.search(line):
                    result.token_like_secret_count += 1
                    add_suspicious(result, rel, lineno, "TOKEN_LIKE_SECRET", line)
    return result


def scan_root(root: Path) -> ClaimScanResult:
    return scan_path(root)
