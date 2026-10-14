#!/usr/bin/env python3
"""MachSig source and extractor identity -- what a signature set or a baseline was derived FROM.

WHY THIS EXISTS (the owner's ruling, 2026-10-13). From 2026-09-03 to 2026-10-13 the trust gate
compared a signature set extracted on 2026-09-03 with the baseline committed the same day, and
passed. The signature set is generated and gitignored; nothing recorded which tree it described,
so nothing could notice that it described a tree forty days and 215 commits old. A regenerated
set showed 1,810 footprint growths the gate had never seen. "A gate that cannot fire must not read
as checked and clean."

So every signature set now carries the identity of the tree and the extractor that produced it,
and the gate recomputes both from the live tree before it compares anything.

THE IDENTITY
  content_digest     sha256 over (path, sha256(bytes)) of every file under MACHLIB_SOURCES that git
                     does not ignore -- tracked or not, committed or not. This is the staleness key:
                     it describes the bytes Lean was given, so an uncommitted edit moves it and a
                     docs-only commit does not.
  machlib_sources    Forge's definition (tools/scripts/proof_discharge.py there, and
                     tools/theorem_ledger/ledger.py here), byte for byte: `sha256:` over
                     `path objectid` lines of MACHLIB_SOURCES at HEAD. Recorded so a signature set
                     can be cross-referenced with Forge's proof bindings and the theorem ledger. It
                     describes the COMMIT, not the bytes on disk, so it is not the staleness key.
  extractor_digest   sha256 over (path, sha256(bytes)) of EXTRACTOR_FILES: everything that decides
                     what a signature says. A comparison across two extractors is not a trust
                     comparison -- that is the second way this gate went blind (AX moved from
                     ProofSig to TrustSig in v0.2 and the gate read an empty field).
  lean_toolchain     the pin. It is also inside content_digest (lean-toolchain is a source).
"""
from __future__ import annotations

import hashlib
import os
import subprocess
from pathlib import Path

FOUND = Path(__file__).resolve().parent.parent.parent

#: What a Lean check against MachLib reads, relative to foundations/. MUST equal Forge's
#: `machlib_sources` and tools/theorem_ledger/ledger.py's MACHLIB_SOURCES.
MACHLIB_SOURCES = ("MachLib", "MachLib.lean", "CertcomLibm.lean", "lakefile.lean", "lean-toolchain",
                   "lake-manifest.json")

#: Everything that decides what a signature SAYS. trust_gate.py (the comparator) and the report tools
#: are deliberately absent: changing how signatures are COMPARED does not change what they record.
EXTRACTOR_FILES = ("tools/machsig/extract.lean", "tools/machsig/extract_statement.lean",
                   "tools/machsig/census.py", "tools/machsig/sig.py", "tools/machsig/regen.py",
                   "tools/machsig/identity.py")

PROVENANCE_KIND = "machsig-provenance"
PROVENANCE_SCHEMA = "machsig-provenance/v1"


class Unavailable(Exception):
    """The identity cannot be computed (no git, no checkout). Never a pass."""


def _git_env() -> dict:
    env = dict(os.environ)
    env.pop("GIT_DIR", None)
    env.pop("GIT_WORK_TREE", None)
    env.pop("GIT_INDEX_FILE", None)
    return env


def git(root: Path, *args: str, check: bool = True) -> str:
    try:
        r = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, env=_git_env())
    except FileNotFoundError as e:
        raise Unavailable("git is not installed") from e
    if check and r.returncode != 0:
        raise Unavailable(f"git {' '.join(args)} failed: {r.stderr.strip()[:200]}")
    return r.stdout


def git_ok(root: Path, *args: str) -> bool:
    try:
        r = subprocess.run(["git", *args], cwd=root, capture_output=True, text=True, env=_git_env())
    except FileNotFoundError:
        return False
    return r.returncode == 0


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _listing_digest(entries: list[tuple[str, str]]) -> str:
    h = hashlib.sha256()
    for path, digest in entries:
        h.update(path.encode("utf-8") + b"\0" + digest.encode() + b"\n")
    return "sha256:" + h.hexdigest()


def content_files(root: Path = FOUND) -> dict[str, str]:
    """{path relative to foundations/: sha256 hex or 'absent'} for every non-ignored file under
    MACHLIB_SOURCES. A tracked file deleted on disk is recorded as 'absent', never skipped."""
    out = git(root, "ls-files", "-z", "--cached", "--others", "--exclude-standard", "--",
              *MACHLIB_SOURCES)
    files: dict[str, str] = {}
    for rel in sorted(set(p for p in out.split("\0") if p)):
        p = root / rel
        files[rel] = sha256_file(p) if p.is_file() else "absent"
    if not files:
        raise Unavailable(f"no MachLib sources found under {root} (is this foundations/?)")
    return files


def content_digest(files: dict[str, str]) -> str:
    return _listing_digest(sorted(files.items()))


def extractor_files(root: Path = FOUND) -> dict[str, str]:
    files = {}
    for rel in EXTRACTOR_FILES:
        p = root / rel
        files[rel] = sha256_file(p) if p.is_file() else "absent"
    return files


def extractor_digest(root: Path = FOUND) -> str:
    return _listing_digest(sorted(extractor_files(root).items()))


def forge_sources_digest(root: Path = FOUND, commit: str = "HEAD") -> str:
    """Forge's definition, byte for byte (see tools/theorem_ledger/ledger.py sources_digest)."""
    lines = []
    for rel in MACHLIB_SOURCES:
        r = subprocess.run(["git", "rev-parse", f"{commit}:./{rel}"], cwd=root, capture_output=True,
                           text=True, env=_git_env())
        lines.append(f"{rel} {r.stdout.strip() if r.returncode == 0 else 'absent'}")
    return "sha256:" + hashlib.sha256("\n".join(lines).encode()).hexdigest()


def dirty_sources(root: Path = FOUND) -> list[str]:
    out = git(root, "status", "--porcelain", "--untracked-files=all", "--", *MACHLIB_SOURCES)
    return sorted(line[3:] for line in out.splitlines() if line.strip())


def toolchain(root: Path = FOUND) -> str:
    p = root / "lean-toolchain"
    return p.read_text(encoding="utf-8").strip() if p.is_file() else "absent"


def live_identity(root: Path = FOUND) -> dict:
    """The identity of the tree as it is NOW. Raises Unavailable without git."""
    files = content_files(root)
    dirty = dirty_sources(root)
    return {
        "machlib_commit": git(root, "rev-parse", "HEAD").strip(),
        "machlib_sources": forge_sources_digest(root),
        "sources_clean": not dirty,
        "dirty_source_paths": dirty,
        "content_digest": content_digest(files),
        "content_files": files,
        "extractor_digest": extractor_digest(root),
        "extractor_files": extractor_files(root),
        "lean_toolchain": toolchain(root),
    }


def changed_files(old: dict[str, str], new: dict[str, str], limit: int = 10) -> list[str]:
    """Paths whose recorded digest differs, for a refusal message that names what moved."""
    keys = sorted(set(old) | set(new))
    moved = [k for k in keys if old.get(k) != new.get(k)]
    return moved[:limit] + ([f"... and {len(moved) - limit} more"] if len(moved) > limit else [])
