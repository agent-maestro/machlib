"""BFS proof sweep driver — C-239.

Walks ``MachLib/Discovered/*.lean``, drives ``MultiProofSearch`` against
each sorry site via ``LeanKernelVerifier``, and writes one JSONL record
per theorem to the configured output path.

Modes
-----
``tier0`` — runs only the 10 hand-picked theorems from
``TIER0_SAMPLE`` (PLAN §9). Serial, verbose output. Used as the
gate before Tier-1.

``tier1`` — runs all 226 extracted theorems with the same Tier-1
vocabulary, parallelised across ``--workers`` processes. (Wired in
this file for completeness; PLAN §14 requires user approval after
Tier-0 before Tier-1 may be invoked.)

Usage
-----
    python3 -m tools.sweep.bfs_sweep --mode tier0
    python3 -m tools.sweep.bfs_sweep --mode tier1 --workers 12 --approved
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from pathlib import Path

# Ensure ~/.elan/bin is on PATH for any subprocess we invoke.
_ELAN_BIN = Path.home() / ".elan" / "bin"
if _ELAN_BIN.is_dir():
    _path = os.environ.get("PATH", "")
    if str(_ELAN_BIN) not in _path:
        os.environ["PATH"] = f"{_ELAN_BIN}{os.pathsep}{_path}"

# These imports come AFTER the PATH adjustment so child processes
# inherit it (ProcessPoolExecutor copies os.environ at fork).
from gym.multi_proof import MultiProofSearch  # noqa: E402
from gym.verifiers import LeanKernelVerifier  # noqa: E402

from .extract import (  # noqa: E402
    ExtractedTheorem,
    extract_all,
    instrument_for_target,
)
from .tactic_shortlist import (  # noqa: E402
    TIER0_SAMPLE,
    TIER1_TACTICS,
    TIER2_TACTICS,
)


def _machlib_root() -> Path:
    here = Path(__file__).resolve()
    return here.parent.parent.parent


def _discovered_dir() -> Path:
    return _machlib_root() / "foundations" / "MachLib" / "Discovered"


def _default_output_path(mode: str) -> Path:
    research = _machlib_root().parent / "monogate-research"
    out_dir = research / "exploration" / "C239_bfs_proof_sweep"
    return out_dir / f"results_{mode}.jsonl"


# ── Per-theorem worker ─────────────────────────────────────────────


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def _attempt_one(
    theorem: ExtractedTheorem,
    *,
    tier: int,
    tactics: tuple[str, ...],
    max_depth: int,
    max_proofs: int,
    per_tactic_timeout: float,
    per_theorem_budget: float,
) -> dict:
    """Run BFS on a single theorem; return a JSONL-ready dict."""
    started = time.perf_counter()
    record: dict = {
        "theorem_id": f"{Path(theorem.source_file).stem}.{theorem.theorem_name}",
        "source_file": theorem.source_file,
        "source_line": theorem.sorry_line_number,
        "goal_shape": theorem.goal_text,
        "goal_shape_bucket": theorem.goal_bucket,
        "pre_tactics": list(theorem.pre_tactics),
        "tier": tier,
        "status": "verifier_error",
        "tactic_sequence": None,
        "tactic_count": None,
        "style": None,
        "verifications_attempted": 0,
        "wall_time_seconds": 0.0,
        "first_lean_error": None,
        "discovered_at": _now_iso(),
    }
    try:
        instrumented = instrument_for_target(theorem)
        verifier = LeanKernelVerifier(default_timeout=per_tactic_timeout)
        search = MultiProofSearch(
            tactic_vocab=tactics,
            verifier=verifier,
            max_depth=max_depth,
            max_proofs=max_proofs,
            timeout_seconds=per_theorem_budget,
        )
        proofs, stats = search.find_all_proofs(instrumented)
        record["verifications_attempted"] = stats.candidates_verified
        record["wall_time_seconds"] = round(stats.elapsed_seconds, 3)
        if proofs:
            top = proofs[0]
            record["status"] = "closed"
            record["tactic_sequence"] = list(top.tactic_sequence)
            record["tactic_count"] = top.tactic_count
            record["style"] = top.style
        elif stats.hit_timeout:
            record["status"] = "timeout"
        else:
            record["status"] = "open"
    except Exception as exc:  # noqa: BLE001
        record["status"] = "verifier_error"
        record["first_lean_error"] = repr(exc)[:400]
        record["wall_time_seconds"] = round(time.perf_counter() - started, 3)
    return record


# ── Tier 0 (serial) ────────────────────────────────────────────────


def run_tier0(
    *,
    output_path: Path,
    per_tactic_timeout: float = 30.0,
    per_theorem_budget: float = 300.0,
) -> tuple[int, int]:
    """Run the 10-theorem Tier-0 dry run. Returns (closures, total)."""
    sample_keys = set(TIER0_SAMPLE)

    theorems: list[ExtractedTheorem] = []
    for thm in extract_all(_discovered_dir(), repo_root=_machlib_root()):
        key = (Path(thm.source_file).name, thm.theorem_name)
        if key in sample_keys:
            theorems.append(thm)

    found_keys = {(Path(t.source_file).name, t.theorem_name) for t in theorems}
    missing = sample_keys - found_keys
    if missing:
        print(f"WARNING: {len(missing)} sample theorems not extracted:")
        for f, n in sorted(missing):
            print(f"  - {f} :: {n}")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    closures = 0
    print(f"Running Tier-0 on {len(theorems)} theorems "
          f"(vocab: {len(TIER1_TACTICS)} tactics, depth=1) -> {output_path}")
    print("-" * 78)
    with output_path.open("w", encoding="utf-8") as out:
        for i, thm in enumerate(theorems, 1):
            print(f"[{i:2d}/{len(theorems)}] {thm.source_file} :: {thm.theorem_name}")
            print(f"         goal:   {thm.goal_text[:80]}")
            t0 = time.perf_counter()
            rec = _attempt_one(
                thm,
                tier=0,
                tactics=TIER1_TACTICS,
                max_depth=1,
                max_proofs=1,
                per_tactic_timeout=per_tactic_timeout,
                per_theorem_budget=per_theorem_budget,
            )
            elapsed = time.perf_counter() - t0
            marker = "OK   CLOSED" if rec["status"] == "closed" else f"{rec['status'].upper():12s}"
            tactic_str = (
                rec["tactic_sequence"][0]
                if rec["tactic_sequence"] else "—"
            )
            print(f"         {marker}  ({rec['verifications_attempted']:2d} tried, {elapsed:5.1f}s)  "
                  f"{tactic_str}")
            out.write(json.dumps(rec) + "\n")
            out.flush()
            if rec["status"] == "closed":
                closures += 1
    return closures, len(theorems)


# ── Tier 1 (parallel) ──────────────────────────────────────────────


def _tier1_worker(theorem: ExtractedTheorem) -> dict:
    """Top-level so ProcessPoolExecutor can pickle it."""
    return _attempt_one(
        theorem,
        tier=1,
        tactics=TIER1_TACTICS,
        max_depth=1,
        max_proofs=1,
        per_tactic_timeout=30.0,
        per_theorem_budget=300.0,
    )


# ── Tier-2 worker variants (configurable depth) ────────────────────


def _tier2_worker_d1(theorem: ExtractedTheorem) -> dict:
    return _attempt_one(
        theorem,
        tier=2,
        tactics=TIER2_TACTICS,
        max_depth=1,
        max_proofs=1,
        per_tactic_timeout=30.0,
        per_theorem_budget=300.0,
    )


def _tier2_worker_d2(theorem: ExtractedTheorem) -> dict:
    # 600s per-theorem cap so a 209-theorem sweep at 12-way parallel
    # stays under ~3h wall (what the user authorised).
    return _attempt_one(
        theorem,
        tier=2,
        tactics=TIER2_TACTICS,
        max_depth=2,
        max_proofs=1,
        per_tactic_timeout=30.0,
        per_theorem_budget=600.0,
    )


def run_tier2(
    *,
    output_path: Path,
    workers: int = 12,
    max_depth: int = 1,
    only_open: Path | None = None,
) -> tuple[int, int]:
    """Run Tier-2 sweep with the extended vocab.

    If ``only_open`` is given, restrict to theorems whose status in
    that JSONL is not 'closed' (lets us run only on still-open
    theorems from a prior tier).
    """
    theorems = list(extract_all(_discovered_dir(), repo_root=_machlib_root()))
    if only_open is not None and only_open.is_file():
        already_closed: set[str] = set()
        for line in only_open.open(encoding="utf-8"):
            r = json.loads(line)
            if r.get("status") == "closed":
                already_closed.add(r["theorem_id"])
        before = len(theorems)
        theorems = [
            t for t in theorems
            if f"{Path(t.source_file).stem}.{t.theorem_name}" not in already_closed
        ]
        print(f"Filtering: {before} -> {len(theorems)} theorems "
              f"(skipped {len(already_closed)} already-closed)")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    closures = 0
    worker = _tier2_worker_d1 if max_depth == 1 else _tier2_worker_d2
    print(f"Running Tier-2 on {len(theorems)} theorems "
          f"(vocab: {len(TIER2_TACTICS)} tactics, depth={max_depth}, "
          f"workers={workers}) -> {output_path}")
    print("-" * 78)
    with output_path.open("w", encoding="utf-8") as out, \
            ProcessPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(worker, t): t for t in theorems}
        for i, fut in enumerate(as_completed(futures), 1):
            rec = fut.result()
            out.write(json.dumps(rec) + "\n")
            out.flush()
            marker = "OK" if rec["status"] == "closed" else "  "
            tag = rec["status"][:8]
            print(f"  [{i:3d}/{len(theorems)}] {marker} {tag:8s} "
                  f"{rec['theorem_id']}")
            if rec["status"] == "closed":
                closures += 1
    return closures, len(theorems)


def run_tier1(
    *,
    output_path: Path,
    workers: int = 12,
) -> tuple[int, int]:
    """Run the full 226-theorem sweep, parallel."""
    theorems = list(extract_all(_discovered_dir(), repo_root=_machlib_root()))
    output_path.parent.mkdir(parents=True, exist_ok=True)
    closures = 0
    print(f"Running Tier-1 on {len(theorems)} theorems "
          f"(vocab: {len(TIER1_TACTICS)} tactics, depth=1, workers={workers}) "
          f"-> {output_path}")
    print("-" * 78)
    with output_path.open("w", encoding="utf-8") as out, \
            ProcessPoolExecutor(max_workers=workers) as pool:
        futures = {pool.submit(_tier1_worker, t): t for t in theorems}
        for i, fut in enumerate(as_completed(futures), 1):
            rec = fut.result()
            out.write(json.dumps(rec) + "\n")
            out.flush()
            marker = "OK" if rec["status"] == "closed" else "  "
            tag = rec["status"][:8]
            print(f"  [{i:3d}/{len(theorems)}] {marker} {tag:8s} "
                  f"{rec['theorem_id']}")
            if rec["status"] == "closed":
                closures += 1
    return closures, len(theorems)


# ── CLI ────────────────────────────────────────────────────────────


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mode", choices=("tier0", "tier1", "tier2"), required=True)
    p.add_argument("--output", type=Path, default=None,
                   help="JSONL output path (default: exploration/C239.../results_<mode>.jsonl)")
    p.add_argument("--workers", type=int, default=12,
                   help="parallel worker processes (tier1/tier2 only)")
    p.add_argument("--approved", action="store_true",
                   help="required to run tier1/tier2; signals user has reviewed prior tier")
    p.add_argument("--max-depth", type=int, default=1,
                   help="BFS depth for tier2 (default 1; 2 ≈ 30-60min wall)")
    p.add_argument("--only-open-from", type=Path, default=None,
                   help="tier2 only: skip theorems already marked closed in this JSONL")
    args = p.parse_args(argv)

    output = args.output or _default_output_path(args.mode)
    if args.mode == "tier0":
        closures, total = run_tier0(output_path=output)
    elif args.mode == "tier1":
        if not args.approved:
            print("Tier-1 requires --approved (PLAN §14 gate).", file=sys.stderr)
            return 2
        closures, total = run_tier1(output_path=output, workers=args.workers)
    else:  # tier2
        if not args.approved:
            print("Tier-2 requires --approved.", file=sys.stderr)
            return 2
        closures, total = run_tier2(
            output_path=output,
            workers=args.workers,
            max_depth=args.max_depth,
            only_open=args.only_open_from,
        )

    print()
    print("=" * 78)
    print(f"  {args.mode.upper()} done. Closed {closures}/{total}.")
    print(f"  Results: {output}")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
