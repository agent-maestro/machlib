"""Theorem extraction + scratch synthesis for the C-239 sweep.

Walks ``foundations/MachLib/Discovered/*.lean`` and yields one
:class:`ExtractedTheorem` per ``sorry  -- TODO: prove against MachLib
foundations`` site. The instrumenter then produces a per-target
"theorem statement" string suitable for handing to
:class:`gym.verifiers.LeanKernelVerifier` — the target theorem's sorry
is replaced by the verifier's ``TARGET_SORRY_MARKER`` while sibling
sorries in the same file are left intact (they're tolerated by lake
build with a warning; the verifier's sorry-count delta check ensures
we only credit a closure for the actual target).

The Discovered/ files are codegen output and follow a uniform shape
(verified across abrams_strength, tanh, softmax, relativistic_doppler,
etc.). The extractor uses line-anchored scanning rather than a
multi-line regex to stay robust against goal-text linebreaks.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterator


# The sorry placeholder that codegen emits. Two-space indent + the
# "TODO: prove against MachLib foundations" tail is the discriminator.
_TARGET_SORRY = "sorry  -- TODO: prove against MachLib foundations"

# Sentinel inserted in place of the target sorry. Must match
# ``LeanKernelVerifier.TARGET_SORRY_MARKER`` exactly.
TARGET_SORRY_MARKER = "sorry /-TARGET-/"

# Theorem-header start. Anchored at column 0 so we don't pick up
# `theorem` mentions inside comments/docstrings.
_THEOREM_START_RE = re.compile(r"^theorem\s+(\w+)")

# Goal-shape buckets — heuristic classification on the trimmed goal text.
_BUCKET_PATTERNS = (
    ("positivity",   re.compile(r">=\s*\(?\s*-?0(?:\.0)?")),
    ("lower_bound",  re.compile(r">=\s*\(?\s*-\(?\s*1(?:\.0)?")),
    ("upper_bound",  re.compile(r"<=\s*\(?\s*-?\d")),
    ("equality",     re.compile(r"^[^<>]*=[^<>]*$")),
)


@dataclass(frozen=True)
class ExtractedTheorem:
    """One sorry site, fully described.

    Attributes:
      source_file: path relative to the machlib repo root.
      theorem_name: the identifier following `theorem`.
      file_text: full contents of the containing .lean file (used by
        the instrumenter — passing the whole file preserves any
        sibling defs / theorems the target may reference).
      target_offset: character offset of the target sorry's first
        char within ``file_text``.
      goal_text: the goal type, as a single normalised line.
      pre_tactics: list of tactic lines between `:= by` and the
        target sorry (typically `["unfold <fn>"]`).
      sorry_line_number: 1-indexed line number of the target sorry.
      goal_bucket: heuristic classification of ``goal_text``.
    """
    source_file: str
    theorem_name: str
    file_text: str
    target_offset: int
    goal_text: str
    pre_tactics: tuple[str, ...]
    sorry_line_number: int
    goal_bucket: str


def classify_goal(goal_text: str) -> str:
    """Heuristic bucket for a goal type. First match wins."""
    for label, pattern in _BUCKET_PATTERNS:
        if pattern.search(goal_text):
            return label
    return "other"


def _find_enclosing_theorem(
    lines: list[str], sorry_line_idx: int
) -> tuple[int, str] | None:
    """Walk backwards from ``sorry_line_idx`` to the nearest ``^theorem``.

    Returns (theorem_line_idx, theorem_name) or None if no theorem
    header is found above (which would mean the codegen shape is
    broken and the target should be skipped).
    """
    for i in range(sorry_line_idx, -1, -1):
        m = _THEOREM_START_RE.match(lines[i])
        if m:
            return i, m.group(1)
    return None


def _extract_goal_text(theorem_block: str) -> str:
    """Pull the goal type from the theorem header.

    The header has the shape:
       theorem NAME (param) ... (param) : GOAL := by

    Goal may span multiple lines. We collapse whitespace and trim.
    Returns "" if `:= by` isn't found (defensive — extractor will
    skip such theorems).
    """
    by_idx = theorem_block.find(":= by")
    if by_idx < 0:
        return ""
    header = theorem_block[:by_idx]
    # Strip the leading `theorem NAME` and the param/hyp blocks.
    # We want everything after the LAST top-level `:` before `:= by`.
    # Top-level meaning: not inside parens. Track depth.
    depth = 0
    last_top_colon = -1
    for i, ch in enumerate(header):
        if ch == "(":
            depth += 1
        elif ch == ")":
            depth -= 1
        elif ch == ":" and depth == 0:
            last_top_colon = i
    if last_top_colon < 0:
        return ""
    goal = header[last_top_colon + 1:]
    # Collapse newlines + repeated whitespace into single spaces.
    return re.sub(r"\s+", " ", goal).strip()


def extract_from_file(
    file_path: Path,
    *,
    repo_root: Path | None = None,
) -> list[ExtractedTheorem]:
    """Extract every TODO-sorry from a single Discovered/ file."""
    text = file_path.read_text(encoding="utf-8")
    lines = text.split("\n")
    out: list[ExtractedTheorem] = []

    rel_path = (
        str(file_path.relative_to(repo_root)) if repo_root else str(file_path)
    )

    for i, line in enumerate(lines):
        if _TARGET_SORRY not in line:
            continue
        # Found a sorry line. Find its enclosing theorem.
        enclosing = _find_enclosing_theorem(lines, i)
        if enclosing is None:
            continue
        theorem_line_idx, name = enclosing
        # The theorem block runs from theorem_line_idx through the
        # sorry line (inclusive). Pre-tactics are the lines between
        # `:= by` and the sorry.
        block_lines = lines[theorem_line_idx : i + 1]
        block_text = "\n".join(block_lines)
        goal = _extract_goal_text(block_text)
        # Pre-tactics: everything between the `:= by` line and the
        # sorry line.
        pre = []
        seen_by = False
        for bl in block_lines:
            if not seen_by:
                if ":= by" in bl:
                    seen_by = True
                continue
            stripped = bl.strip()
            if stripped == "" or _TARGET_SORRY in stripped:
                continue
            pre.append(stripped)

        # Compute the character offset of the sorry within file_text.
        offset = sum(len(ln) + 1 for ln in lines[:i]) + line.find(_TARGET_SORRY)

        out.append(ExtractedTheorem(
            source_file=rel_path,
            theorem_name=name,
            file_text=text,
            target_offset=offset,
            goal_text=goal,
            pre_tactics=tuple(pre),
            sorry_line_number=i + 1,
            goal_bucket=classify_goal(goal),
        ))
    return out


def extract_all(
    discovered_dir: Path,
    *,
    repo_root: Path | None = None,
) -> Iterator[ExtractedTheorem]:
    """Walk every .lean file under ``discovered_dir`` and yield theorems.

    Files are visited in sorted order so runs are deterministic.
    """
    for path in sorted(discovered_dir.glob("*.lean")):
        yield from extract_from_file(path, repo_root=repo_root)


def instrument_for_target(theorem: ExtractedTheorem) -> str:
    """Produce the source string the verifier should consume.

    The target theorem's ``sorry  -- TODO: ...`` is replaced by
    ``TARGET_SORRY_MARKER``; sibling sorries in the same file remain
    untouched. The verifier substitutes its own tactic candidates
    for the marker.
    """
    text = theorem.file_text
    end = theorem.target_offset + len(_TARGET_SORRY)
    return text[:theorem.target_offset] + TARGET_SORRY_MARKER + text[end:]


# ── CLI for triage / Tier-0 sample selection ──────────────────────


def _default_discovered_dir() -> Path:
    here = Path(__file__).resolve()
    return here.parent.parent.parent / "foundations" / "MachLib" / "Discovered"


def _cli_list() -> int:
    """Print one line per extracted theorem, with goal bucket."""
    disc = _default_discovered_dir()
    if not disc.is_dir():
        print(f"Discovered/ not found at {disc}")
        return 1
    n_total = 0
    by_bucket: dict[str, int] = {}
    for thm in extract_all(disc, repo_root=disc.parent.parent.parent):
        n_total += 1
        by_bucket[thm.goal_bucket] = by_bucket.get(thm.goal_bucket, 0) + 1
        goal_short = (
            thm.goal_text[:80] + "..." if len(thm.goal_text) > 80 else thm.goal_text
        )
        print(f"{thm.goal_bucket:12s}  {thm.source_file:60s}  {thm.theorem_name:40s}  {goal_short}")
    print()
    print(f"Total: {n_total} sorries extracted.")
    print("By bucket:")
    for k, v in sorted(by_bucket.items(), key=lambda x: -x[1]):
        print(f"  {k:12s}  {v}")
    return 0


if __name__ == "__main__":
    raise SystemExit(_cli_list())
