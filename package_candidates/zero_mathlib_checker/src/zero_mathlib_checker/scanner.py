"""Small local scanner for direct Mathlib dependency evidence."""

from __future__ import annotations

from dataclasses import dataclass, field
from pathlib import Path
from typing import Iterable


DIRECT_PATTERNS = ("import " + "Mathlib", "from " + "Mathlib", "Mathlib" + ".")
DEPENDENCY_FILENAMES = {"lakefile.lean", "lake-manifest.json", "lakefile.toml"}
DEPENDENCY_HINTS = ("mathlib", "leanprover-community/mathlib")
POLICY_MARKERS = ("POLICY_TEXT", "HISTORICAL_TEXT", "NO_DEPENDENCY_CLAIM_TEXT")


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
    direct_match_count: int = 0
    dependency_evidence_count: int = 0
    policy_text_count: int = 0
    evidence: list[Evidence] = field(default_factory=list)

    @property
    def passed(self) -> bool:
        return self.direct_match_count == 0 and self.dependency_evidence_count == 0

    def to_dict(self) -> dict[str, object]:
        return {
            "root": self.root,
            "scanned_files": self.scanned_files,
            "direct_match_count": self.direct_match_count,
            "dependency_evidence_count": self.dependency_evidence_count,
            "policy_text_count": self.policy_text_count,
            "passed": self.passed,
            "evidence": [item.__dict__ for item in self.evidence],
        }


def iter_files(root: Path) -> Iterable[Path]:
    for path in root.rglob("*"):
        if path.is_file() and ".git" not in path.parts and "__pycache__" not in path.parts:
            yield path


def is_policy_line(text: str) -> bool:
    return any(marker in text for marker in POLICY_MARKERS)


def scan_root(root: Path, allow_policy_text: bool = False) -> ScanResult:
    root = root.resolve()
    result = ScanResult(root=str(root))
    for path in iter_files(root):
        try:
            lines = path.read_text(encoding="utf-8").splitlines()
        except UnicodeDecodeError:
            continue
        result.scanned_files += 1
        rel = str(path.relative_to(root))
        for lineno, line in enumerate(lines, start=1):
            if allow_policy_text and is_policy_line(line):
                result.policy_text_count += 1
                continue
            for pattern in DIRECT_PATTERNS:
                if pattern in line:
                    result.direct_match_count += 1
                    result.evidence.append(Evidence(rel, lineno, pattern, line.strip(), "direct_import"))
            if path.name in DEPENDENCY_FILENAMES:
                lower = line.lower()
                if any(hint in lower for hint in DEPENDENCY_HINTS):
                    result.dependency_evidence_count += 1
                    result.evidence.append(Evidence(rel, lineno, "mathlib dependency text", line.strip(), "dependency"))
    return result
