"""Live Lean 4 verification worker.

VENDORED from monogate-research/petal/lean_worker/worker.py
(C-239, 2026-05-03). Kept verbatim except for this header so machlib
remains self-contained — see exploration/C239_bfs_proof_sweep/PLAN.md
§4 for the rationale (Q2: "vendor for self-containedness").

The worker accepts a free-form Lean source string, writes it into a
scratch module inside a pre-built ``monogate-lean`` Lake project,
runs ``lake build`` targeted at the scratch module, parses the
output, and returns a frozen :class:`VerifyResult`.

Design constraints
==================

  * **Scratch module isolation.** Each ``verify()`` call uses a
    unique-per-process scratch filename (``MonogateEML/_AgentScratch_<n>.lean``)
    so concurrent requests on the same repo do not race each
    other. The file is deleted in ``finally``; if a previous run
    left a stale copy, the worker overwrites it.

  * **No source-tree mutation.** The scratch file is the *only* file
    the worker writes. Existing files in ``monogate-lean`` are
    never modified — the worker can run alongside the canonical
    grading pipeline without cross-talk.

  * **Targeted lake build.** ``lake build MonogateEML._AgentScratch_N``
    skips re-checking the rest of the library. Mathlib oleans live
    in the Lake build cache and are reused across requests; warm
    response time is dominated by elaboration of the new file.

  * **Sandboxing.** ``lake build`` runs as a subprocess with a
    timeout, captured output, and no shell. The user-supplied
    source is written verbatim to disk and only ``lake`` parses
    it; we do not interpret the source ourselves beyond a
    ``sorry`` count.

  * **No goal-state extraction yet.** The :meth:`get_goal_state`
    method is a stub that returns the last *unsolved goals* block
    found in stderr. A real LSP integration is a follow-up
    (Phase 1.4 of the roadmap).
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional, Sequence


__all__ = [
    "LeanWorker",
    "VerifyResult",
    "parse_lake_output",
]


# ─── Module-level counter for unique scratch filenames per process ───

_scratch_counter_lock = threading.Lock()
_scratch_counter = 0


def _next_scratch_id() -> int:
    """Process-wide monotonically increasing scratch counter."""
    global _scratch_counter
    with _scratch_counter_lock:
        _scratch_counter += 1
        return _scratch_counter


# ─── Result type ─────────────────────────────────────────────────────


@dataclass(frozen=True)
class VerifyResult:
    """Structured outcome of a single verification attempt."""

    status: str
    """One of ``"success"``, ``"error"``, ``"timeout"``, ``"unavailable"``.

    ``success`` means ``lake build`` returned exit code 0. Note that
    success does NOT necessarily mean the proof is closed —
    ``sorry_count`` may still be > 0; the kernel accepts it as a
    well-typed admission.
    """

    goals_remaining: int
    """Number of unsolved goals reported by ``lake build``. ``0``
    after a successful proof; ``-1`` when goals could not be
    extracted (e.g. on syntax error)."""

    goal_state: Optional[str]
    """The first ``unsolved goals`` block from stderr, if any.
    ``None`` when there are no unsolved-goals errors."""

    error_messages: tuple[str, ...]
    """Distinct error lines from stderr, in order of appearance."""

    sorry_count: int
    """Count of ``sorry`` / ``admit`` tokens in the user-supplied
    source after stripping comments. ``-1`` on parse failure."""

    timing: dict[str, float]
    """``kernel_check_ms``, ``total_ms`` for the call."""

    raw_stdout: str = ""
    raw_stderr: str = ""

    eml_metrics: dict = field(default_factory=dict)
    """Best-effort EML profile extracted from the source. Empty
    when the source isn't recognisable as a single expression
    eml-cost can analyse."""

    suggestions: dict = field(default_factory=dict)
    """PETAL-context enrichment: ``next_tactics``, ``similar_proofs``,
    ``common_mistakes``. Populated by :func:`enrich_with_petal_context`
    in the API layer."""


# ─── Output parsing ──────────────────────────────────────────────────


# Lean compiler form: ``Foo.lean:42:7: error: ...``
_LEAN_DIAG_RE = re.compile(
    r"^(?P<file>[^\s:]+\.lean):(?P<line>\d+):(?P<col>\d+):\s*"
    r"(?P<level>error|warning):\s*(?P<message>.+)$",
    re.MULTILINE,
)
# Lake wrapper form: ``error: Foo.lean:42:7: ...``
# The path may use backslashes on Windows and may include leading
# ``.\`` segments. We capture loosely and trust the trailing
# `.lean:LINE:COL` shape.
_LAKE_DIAG_RE = re.compile(
    r"^(?P<level>error|warning):\s*(?P<file>[^\s:]+\.lean):"
    r"(?P<line>\d+):(?P<col>\d+):\s*(?P<message>.+)$",
    re.MULTILINE,
)
# Lake also emits standalone summary lines like
# ``error: build failed`` and ``error: Lean exited with code 1``;
# these are NOT useful diagnostics and we filter them out.
_LAKE_SUMMARY_RE = re.compile(
    r"^error:\s*(build failed|Lean exited with code|"
    r"Some required builds logged failures)",
    re.MULTILINE,
)
_UNSOLVED_GOALS_RE = re.compile(
    r"unsolved goals\s*\n(?P<body>(?:.+\n?)*?)(?=\n\s*\n|\Z|^[^\s])",
    re.MULTILINE,
)


def parse_lake_output(stderr: str, stdout: str = "") -> dict:
    """Parse ``lake build`` output into structured fields.

    Returns a dict with ``error_messages``, ``goal_state``,
    ``goals_remaining``, ``warnings``. Defensive against the
    quirks of Lean 4 / Lake stderr formatting.
    """
    text = (stderr or "") + ("\n" + stdout if stdout else "")

    error_messages: list[str] = []
    warnings: list[str] = []
    seen: set[str] = set()
    for pattern in (_LEAN_DIAG_RE, _LAKE_DIAG_RE):
        for m in pattern.finditer(text):
            msg = (
                f"{m.group('file')}:{m.group('line')}:{m.group('col')}: "
                f"{m.group('message').rstrip()}"
            )
            if msg in seen:
                continue
            seen.add(msg)
            if m.group("level") == "error":
                error_messages.append(msg)
            else:
                warnings.append(msg)
    # If lake reported a summary failure but we have no per-line
    # diagnostics, surface the summary line so the caller has
    # something to log.
    if not error_messages and _LAKE_SUMMARY_RE.search(text):
        m = _LAKE_SUMMARY_RE.search(text)
        if m:
            error_messages.append(m.group(0).strip())

    # Unsolved goals — Lean 4 emits a multi-line block after the
    # "unsolved goals" header. We grab everything until the next
    # blank line or non-indented line (heuristic).
    goal_match = _UNSOLVED_GOALS_RE.search(text)
    goal_state = goal_match.group("body").strip() if goal_match else None
    goals_remaining = 1 if goal_state else 0

    # If lake reported any errors but no unsolved-goals block, we
    # still treat the proof as not complete.
    if error_messages and goals_remaining == 0:
        goals_remaining = -1

    return {
        "error_messages": tuple(error_messages),
        "warnings": tuple(warnings),
        "goal_state": goal_state,
        "goals_remaining": goals_remaining,
    }


def _strip_comments(text: str) -> str:
    """Strip Lean ``--`` and nested ``/- -/`` comments."""
    out = re.sub(r"--[^\n]*", "", text)
    while True:
        m = re.search(r"/-(?:(?!/-|-/)[\s\S])*?-/", out)
        if not m:
            break
        out = out[: m.start()] + out[m.end():]
    return out


def _count_sorries(source: str) -> int:
    cleaned = _strip_comments(source)
    return len(re.findall(r"\bsorry\b|\badmit\b", cleaned))


# ─── Worker ──────────────────────────────────────────────────────────


class LeanWorker:
    """Runs ``lake build`` on free-form Lean source.

    Construct once with the path to a pre-built ``monogate-lean``
    Lake project. Each :meth:`verify` call writes a scratch module
    into ``MonogateEML/`` (relative to ``lean_repo``) and runs
    ``lake build`` targeted at that single module.

    Example
    -------

        >>> worker = LeanWorker(lean_repo="D:/monogate-lean")
        >>> r = worker.verify(
        ...     "theorem t : 1 + 1 = 2 := by norm_num",
        ...     imports=["Mathlib.Tactic.NormNum"],
        ... )
        >>> r.status
        'success'
    """

    def __init__(
        self,
        lean_repo: str | Path,
        *,
        scratch_namespace: str = "MonogateEML",
        scratch_basename: str = "_AgentScratch",
        default_imports: Sequence[str] = ("MonogateEML.EMLDepth",),
        default_timeout: float = 60.0,
    ) -> None:
        self.lean_repo = Path(lean_repo).resolve()
        self.scratch_namespace = scratch_namespace
        self.scratch_basename = scratch_basename
        self.default_imports = tuple(default_imports)
        self.default_timeout = default_timeout

    # ── Availability ───────────────────────────────────────────────

    def is_available(self) -> bool:
        """``True`` when ``lake`` is on PATH and the repo exists.

        Cheap — used by the API health endpoint and by tests to
        decide whether to skip a real-build smoke test.
        """
        if shutil.which("lake") is None:
            return False
        if not (self.lean_repo / "lakefile.lean").exists():
            return False
        return True

    # ── Scratch-file plumbing ──────────────────────────────────────

    def _scratch_path(self, scratch_id: int) -> Path:
        ns_dir = self.lean_repo / self.scratch_namespace
        return ns_dir / f"{self.scratch_basename}_{scratch_id}.lean"

    def _scratch_module(self, scratch_id: int) -> str:
        return f"{self.scratch_namespace}.{self.scratch_basename}_{scratch_id}"

    @staticmethod
    def _compose_source(
        user_source: str,
        imports: Sequence[str],
    ) -> str:
        """Prepend imports to the user source, idempotently.

        If the user already wrote ``import X`` lines, we don't
        duplicate them; we add only the imports that aren't
        already present at the top of the file.
        """
        existing = {
            m.group(1)
            for m in re.finditer(r"^import\s+([\w.]+)", user_source, re.MULTILINE)
        }
        to_add = [imp for imp in imports if imp not in existing]
        if not to_add:
            return user_source
        block = "\n".join(f"import {imp}" for imp in to_add)
        # If the user starts with their own imports, keep them on
        # top; the prepended block goes ABOVE them.
        return f"{block}\n\n{user_source}"

    # ── verify() ───────────────────────────────────────────────────

    def verify(
        self,
        lean_source: str,
        *,
        imports: Optional[Sequence[str]] = None,
        timeout: Optional[float] = None,
    ) -> VerifyResult:
        """Verify ``lean_source`` and return a :class:`VerifyResult`.

        The source is written into a unique scratch file inside
        the Lake project, ``lake build`` is invoked targeted at
        that module, and the output is parsed into the result.
        """
        t0 = time.time()
        timeout_s = float(timeout if timeout is not None else self.default_timeout)
        imports_to_use = tuple(imports) if imports is not None else self.default_imports

        if not self.is_available():
            return VerifyResult(
                status="unavailable",
                goals_remaining=-1,
                goal_state=None,
                error_messages=("lake not on PATH or monogate-lean repo missing",),
                sorry_count=-1,
                timing={"kernel_check_ms": 0.0, "total_ms": 0.0},
            )

        sorry_count = _count_sorries(lean_source)

        scratch_id = _next_scratch_id()
        scratch_path = self._scratch_path(scratch_id)
        scratch_path.parent.mkdir(parents=True, exist_ok=True)
        full_source = self._compose_source(lean_source, imports_to_use)

        kernel_t0 = time.time()
        try:
            scratch_path.write_text(full_source, encoding="utf-8")
            try:
                # Lean emits Unicode output (⊢, →, ε, ...) regardless
                # of the host locale. Forcing utf-8 with replacement
                # avoids the Windows cp1252 reader-thread crash that
                # would otherwise drop stderr entirely on a build with
                # an unsolved-goals block.
                proc = subprocess.run(
                    ["lake", "build", self._scratch_module(scratch_id)],
                    cwd=str(self.lean_repo),
                    capture_output=True,
                    text=True,
                    encoding="utf-8",
                    errors="replace",
                    timeout=timeout_s,
                    check=False,
                )
            except subprocess.TimeoutExpired:
                kernel_ms = (time.time() - kernel_t0) * 1000
                return VerifyResult(
                    status="timeout",
                    goals_remaining=-1,
                    goal_state=None,
                    error_messages=(f"lake build exceeded {timeout_s}s",),
                    sorry_count=sorry_count,
                    timing={
                        "kernel_check_ms": kernel_ms,
                        "total_ms": (time.time() - t0) * 1000,
                    },
                )
            kernel_ms = (time.time() - kernel_t0) * 1000

            parsed = parse_lake_output(proc.stderr or "", proc.stdout or "")
            ok = proc.returncode == 0 and not parsed["error_messages"]
            status = "success" if ok else "error"

            # If the build was clean BUT sorry_count > 0, the proof
            # type-checks under admission — make that visible.
            if status == "success" and sorry_count > 0:
                # Compose a synthetic message rather than mutate
                # status; downstream callers can decide what to do.
                msgs = parsed["error_messages"] + (
                    f"build succeeded with {sorry_count} sorry/admit"
                    " (proof is admitted, not closed)",
                )
                parsed = dict(parsed, error_messages=msgs)

            return VerifyResult(
                status=status,
                goals_remaining=parsed["goals_remaining"]
                    if status != "success" else 0,
                goal_state=parsed["goal_state"],
                error_messages=tuple(parsed["error_messages"]),
                sorry_count=sorry_count,
                timing={
                    "kernel_check_ms": round(kernel_ms, 1),
                    "total_ms": round((time.time() - t0) * 1000, 1),
                },
                raw_stdout=proc.stdout or "",
                raw_stderr=proc.stderr or "",
            )
        finally:
            try:
                if scratch_path.exists():
                    scratch_path.unlink()
            except OSError:
                pass

    # ── get_goal_state() ───────────────────────────────────────────

    def get_goal_state(
        self,
        lean_source: str,
        *,
        imports: Optional[Sequence[str]] = None,
        timeout: Optional[float] = None,
    ) -> dict:
        """Return the current tactic state (best-effort).

        The MVP implementation uses :meth:`verify` and extracts the
        ``unsolved goals`` block from the kernel output. A future
        version (Phase 1.4) will use Lean's LSP to report the
        goal state at a specific cursor position.
        """
        result = self.verify(lean_source, imports=imports, timeout=timeout)
        return {
            "goal_state": result.goal_state,
            "goals_remaining": result.goals_remaining,
            "status": result.status,
            "sorry_count": result.sorry_count,
            "timing": result.timing,
        }
