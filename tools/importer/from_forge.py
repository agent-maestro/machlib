"""from_forge -- mine MachLib theorem records from the Forge corpus.

Every .eml file in monogate-forge/industries/ has been profiled by the
Forge optimizer; the per-function profile (chain_order, node_count,
fpga_cycles, mac_units, trig_units) lives in
``tools/benchmarks/vertical_baseline.json``. Each property + each
``@verify`` contract on the .eml source becomes a MachLib theorem.

This is the Phase A-001 deliverable from
``monogate-research/roadmap/machlib-v2-strength.md``. Output records
follow MachLib's ``schema_version: 1.0.0`` shape; proofs are stubbed
``sorry`` and filled later by the BFS engine (Phase B-001) and RL
agent (Phase B-003).

Usage:

    # Default: read forge baseline, write to corpus/forge_mined/
    python tools/importer/from_forge.py

    # Smoke test on a few entries
    python tools/importer/from_forge.py --limit 5 --dry-run

    # Custom roots
    python tools/importer/from_forge.py \\
        --forge-root D:/monogate-forge \\
        --output corpus/forge_mined

The script is idempotent — re-running overwrites existing output files
in-place. No state is carried between runs except the file artifacts.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict
from datetime import date
from pathlib import Path
from typing import Any

# ─── constants ─────────────────────────────────────────────────────

GENERATOR_VERSION = "from_forge_importer_v1"
SCHEMA_VERSION = "1.0.0"
DOMAIN = "forge_mined"

# Chain order → MachLib lane mapping. Forge functions are application-
# grade kernels traceable to real engineering equations; they live
# above lane-1 (foundations) and below lane-7 (PETAL biology).
_CHAIN_LANE = {0: 2, 1: 2, 2: 3, 3: 3}
_DEFAULT_LANE = 4

# Chain order → structural class label.
_CHAIN_CLASS = {
    0: "polynomial",
    1: "exponential",
    2: "oscillatory",
}


# ─── data loading ──────────────────────────────────────────────────

def _load_baseline(path: Path) -> dict[str, dict[str, int]]:
    """Load Forge's vertical_baseline.json. Keys: '<file>::<func>'."""
    raw = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(raw, dict):
        raise ValueError(f"baseline at {path} is not a dict")
    return raw


def _build_eml_index(industries_root: Path) -> dict[str, Path]:
    """Map .eml file stems → absolute paths under industries/."""
    out: dict[str, Path] = {}
    for p in industries_root.rglob("*.eml"):
        if p.is_file():
            out.setdefault(p.stem, p)
    return out


# ─── @verify block parsing ─────────────────────────────────────────

_VERIFY_HEADER = re.compile(
    r'@verify\s*\(\s*lean\s*,\s*theorem\s*=\s*"([^"]+)"\s*\)'
)


def _balanced_paren_content(src: str, after_open: int) -> tuple[str, int]:
    """Return (inner_text, idx_after_close) for the paren opened at
    position ``after_open - 1``. ``after_open`` points to the char
    right after the '(' opener."""
    depth = 1
    i = after_open
    n = len(src)
    while i < n and depth > 0:
        c = src[i]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                return src[after_open:i], i + 1
        i += 1
    return src[after_open:i], i  # unbalanced; salvage what we have


def _extract_clauses(src: str, keyword: str) -> list[str]:
    """Extract every ``keyword (...)`` body from ``src`` (balanced parens)."""
    out: list[str] = []
    pat = re.compile(rf'\b{re.escape(keyword)}\s*\(')
    pos = 0
    while True:
        m = pat.search(src, pos)
        if not m:
            return out
        body, next_pos = _balanced_paren_content(src, m.end())
        out.append(body.strip())
        pos = next_pos


def _parse_verify_blocks(eml_src: str) -> list[dict[str, Any]]:
    """Extract one entry per @verify block in the .eml source."""
    out: list[dict[str, Any]] = []
    for header in _VERIFY_HEADER.finditer(eml_src):
        theorem_name = header.group(1)
        # Find the function header that follows. Body opens at next '{'.
        rest = eml_src[header.end():]
        brace_idx = rest.find("{")
        if brace_idx < 0:
            continue
        block_src = rest[:brace_idx]
        fn_match = re.search(r"\bfn\s+(\w+)", block_src)
        if not fn_match:
            continue
        out.append({
            "theorem_name": theorem_name,
            "fn_name": fn_match.group(1),
            "requires": _extract_clauses(block_src, "requires"),
            "ensures": _extract_clauses(block_src, "ensures"),
        })
    return out


# ─── theorem record builders ───────────────────────────────────────

def _make_record(
    *,
    theorem_id: str,
    file_stem: str,
    fn_name: str,
    informal: str,
    formal_lean: str,
    profile: dict[str, int],
    extra_tags: list[str],
    eml_path: Path,
) -> dict[str, Any]:
    """Construct a v1.0.0 MachLib record for a forge-mined theorem.

    Proof body is left as ``sorry`` — Phase B's BFS engine and RL
    agent fill these in later. Difficulty is calibrated from chain
    order; structural_profile carries the full Forge profile.
    """
    chain = profile.get("chain_order", 0)
    lane = _CHAIN_LANE.get(chain, _DEFAULT_LANE)
    structural_class = _CHAIN_CLASS.get(chain, "higher_order")
    return {
        "schema_version": SCHEMA_VERSION,
        "theorem": {
            "id": theorem_id,
            "base_id": theorem_id,
            "variant_strategy": None,
            "statement": {
                "informal": informal,
                "formal_lean": formal_lean,
                "formal_eml_lang": None,
            },
            "domain": DOMAIN,
            "lane": lane,
            "tags": [
                "forge_mined",
                f"file::{file_stem}",
                f"function::{fn_name}",
                f"chain_order::{chain}",
                f"class::{structural_class}",
                *extra_tags,
            ],
        },
        "proofs": [],
        "difficulty": {
            "lane": lane,
            "label": _difficulty_label(chain),
            "calibrated_from_attempts": 0,
            "average_hint_level_at_solve": 0.0,
            "prerequisite_skills": _prerequisites_for(chain, extra_tags),
        },
        "common_mistakes": [],
        "tactic_trace": {
            "successful": {},
            "failed": {},
            "success_rate_by_tactic": {},
        },
        "structural_profile": {
            "chain_order": chain,
            "cost_class": None,
            "eml_depth": None,
            "dynamics": {
                "oscillations": 1 if chain >= 2 else 0,
                "decays": 1 if chain == 1 else 0,
            },
            "drift_risk": "LOW" if chain <= 1 else "MEDIUM",
            "fpga_estimate": {
                "cycles": profile.get("fpga_cycles"),
                "mac_units": profile.get("mac_units"),
                "trig_units": profile.get("trig_units"),
            },
        },
        "relationships": {
            "parent": None,
            "siblings": [],
            "depends_on": [],
            "structural_siblings": [],
        },
        "metadata": {
            "verified": False,
            "verification_method": "pending",
            "generated_by": GENERATOR_VERSION,
            "creation_date": date.today().isoformat(),
            "source_eml_file": str(eml_path).replace("\\", "/"),
            "source_function": fn_name,
        },
    }


def _difficulty_label(chain: int) -> str:
    if chain == 0:
        return "beginner"
    if chain == 1:
        return "intermediate"
    if chain == 2:
        return "intermediate"
    return "advanced"


def _prerequisites_for(chain: int, extra_tags: list[str]) -> list[str]:
    skills = ["chain_order_definition"]
    if chain >= 1:
        skills.append("exp_log_axioms")
    if chain >= 2:
        skills.append("trig_axioms")
    if any(t.startswith("property::contract") for t in extra_tags):
        skills.append("hoare_contract_reasoning")
    return skills


def _build_chain_order_theorem(
    file_stem: str, fn_name: str, profile: dict[str, int], eml_path: Path,
) -> dict[str, Any]:
    chain = profile.get("chain_order", 0)
    return _make_record(
        theorem_id=f"forge__{file_stem}__{fn_name}__chain_order",
        file_stem=file_stem,
        fn_name=fn_name,
        informal=(
            f"`{fn_name}` (from `{file_stem}.eml`) has EML chain order {chain}. "
            f"Chain order is the depth of nested transcendental operators in the "
            f"function's EML routing tree; chain {chain} means the function is "
            f"{_CHAIN_CLASS.get(chain, 'higher_order')} in structure."
        ),
        formal_lean=(
            f"-- Pending MachLib infrastructure for forge function imports.\n"
            f"-- theorem {fn_name}_chain_order : "
            f"chain_order {fn_name} = {chain} := sorry"
        ),
        profile=profile,
        extra_tags=["property::chain_order"],
        eml_path=eml_path,
    )


def _build_node_count_theorem(
    file_stem: str, fn_name: str, profile: dict[str, int], eml_path: Path,
) -> dict[str, Any]:
    nodes = profile.get("node_count", 0)
    return _make_record(
        theorem_id=f"forge__{file_stem}__{fn_name}__node_count",
        file_stem=file_stem,
        fn_name=fn_name,
        informal=(
            f"`{fn_name}` compiles to {nodes} EML routing nodes after "
            f"SuperBEST optimization. This is the canonical, minimal "
            f"node count Forge produces for the function as written."
        ),
        formal_lean=(
            f"-- Pending MachLib infrastructure for forge function imports.\n"
            f"-- theorem {fn_name}_node_count : "
            f"node_count {fn_name} = {nodes} := sorry"
        ),
        profile=profile,
        extra_tags=["property::node_count"],
        eml_path=eml_path,
    )


def _build_structural_class_theorem(
    file_stem: str, fn_name: str, profile: dict[str, int], eml_path: Path,
) -> dict[str, Any]:
    chain = profile.get("chain_order", 0)
    cls = _CHAIN_CLASS.get(chain, "higher_order")
    return _make_record(
        theorem_id=f"forge__{file_stem}__{fn_name}__structural_class",
        file_stem=file_stem,
        fn_name=fn_name,
        informal=(
            f"`{fn_name}` is structurally {cls}: chain order {chain} implies "
            f"the function lives in the {cls} regime of the EML hierarchy. "
            f"This is a definitional consequence of `{fn_name}_chain_order`."
        ),
        formal_lean=(
            f"-- theorem {fn_name}_is_{cls} : "
            f"is_{cls} {fn_name} := sorry"
        ),
        profile=profile,
        extra_tags=["property::structural_class"],
        eml_path=eml_path,
    )


def _build_fpga_cycles_theorem(
    file_stem: str, fn_name: str, profile: dict[str, int], eml_path: Path,
) -> dict[str, Any]:
    cycles = profile.get("fpga_cycles", 0)
    macs = profile.get("mac_units", 0)
    return _make_record(
        theorem_id=f"forge__{file_stem}__{fn_name}__fpga_cycles",
        file_stem=file_stem,
        fn_name=fn_name,
        informal=(
            f"`{fn_name}` is implementable in {cycles} FPGA pipeline cycles "
            f"using {macs} MAC units (Forge's FPGA allocator estimate). "
            f"This bounds the latency of the hardware-emitted Verilog."
        ),
        formal_lean=(
            f"-- theorem {fn_name}_fpga_cycles : "
            f"fpga_cycles {fn_name} ≤ {cycles} := sorry"
        ),
        profile=profile,
        extra_tags=["property::fpga_cycles"],
        eml_path=eml_path,
    )


def _build_verify_contract_theorem(
    file_stem: str, fn_name: str, profile: dict[str, int],
    verify_block: dict[str, Any], eml_path: Path,
) -> dict[str, Any]:
    requires_lines = verify_block.get("requires", [])
    ensures_lines = verify_block.get("ensures", [])
    requires_str = " ∧ ".join(requires_lines) if requires_lines else "True"
    ensures_str = " ∧ ".join(ensures_lines) if ensures_lines else "True"
    informal = (
        f"`{fn_name}` satisfies its @verify contract: under preconditions "
        f"({requires_str}), the function's result satisfies ({ensures_str}). "
        f"This is the obligation Forge ships to a Lean target for "
        f"DO-178C / IEC-61508 / ISO-26262 certification evidence."
    )
    formal = (
        f"-- @verify obligation pulled from {eml_path.name}\n"
        f"-- theorem {verify_block['theorem_name']} : "
        f"\\u2200 args, ({requires_str}) \\u2192 ({ensures_str}) := sorry"
    )
    return _make_record(
        theorem_id=f"forge__{file_stem}__{fn_name}__verify_contract",
        file_stem=file_stem,
        fn_name=fn_name,
        informal=informal,
        formal_lean=formal,
        profile=profile,
        extra_tags=[
            "property::contract",
            f"contract::{verify_block['theorem_name']}",
        ],
        eml_path=eml_path,
    )


# ─── orchestration ─────────────────────────────────────────────────

def _records_for_function(
    file_stem: str, fn_name: str, profile: dict[str, int],
    verify_blocks_by_fn: dict[str, list[dict[str, Any]]], eml_path: Path,
) -> list[dict[str, Any]]:
    records = [
        _build_chain_order_theorem(file_stem, fn_name, profile, eml_path),
        _build_node_count_theorem(file_stem, fn_name, profile, eml_path),
        _build_structural_class_theorem(file_stem, fn_name, profile, eml_path),
        _build_fpga_cycles_theorem(file_stem, fn_name, profile, eml_path),
    ]
    for verify_block in verify_blocks_by_fn.get(fn_name, []):
        records.append(_build_verify_contract_theorem(
            file_stem, fn_name, profile, verify_block, eml_path,
        ))
    return records


def _process_baseline(
    baseline: dict[str, dict[str, int]],
    eml_index: dict[str, Path],
    output_root: Path,
    *,
    limit: int | None,
    dry_run: bool,
) -> dict[str, int]:
    """Walk the baseline, emit records, return a stats dict."""
    written = Counter()
    skipped: list[str] = []
    verify_cache: dict[str, dict[str, list[dict[str, Any]]]] = {}

    items = list(baseline.items())
    if limit is not None:
        items = items[:limit]

    for key, profile in items:
        if "::" not in key:
            skipped.append(f"malformed key: {key}")
            continue
        file_stem, fn_name = key.split("::", 1)
        eml_path = eml_index.get(file_stem)
        if eml_path is None:
            skipped.append(f"no .eml for {file_stem}")
            continue

        if file_stem not in verify_cache:
            try:
                src = eml_path.read_text(encoding="utf-8", errors="replace")
                blocks = _parse_verify_blocks(src)
            except OSError:
                blocks = []
            by_fn: dict[str, list[dict[str, Any]]] = defaultdict(list)
            for b in blocks:
                by_fn[b["fn_name"]].append(b)
            verify_cache[file_stem] = by_fn

        records = _records_for_function(
            file_stem, fn_name, profile, verify_cache[file_stem], eml_path,
        )

        if not dry_run:
            file_dir = output_root / file_stem
            file_dir.mkdir(parents=True, exist_ok=True)
            for r in records:
                target = file_dir / f"{r['theorem']['id']}.json"
                target.write_text(
                    json.dumps(r, indent=2, ensure_ascii=False),
                    encoding="utf-8",
                )

        written["functions"] += 1
        written["records"] += len(records)
        for prop_tag in (t for r in records for t in r["theorem"]["tags"]
                         if t.startswith("property::")):
            written[prop_tag] += 1

    return {
        "functions_processed": written["functions"],
        "records_written": written["records"],
        "skipped_count": len(skipped),
        "skipped_reasons": skipped[:10],
        "by_property": {k: v for k, v in written.items()
                        if k.startswith("property::")},
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="from_forge",
        description=__doc__.split("\n\n", 1)[0],
    )
    parser.add_argument(
        "--forge-root",
        default="D:/monogate-forge",
        help="path to monogate-forge clone",
    )
    parser.add_argument(
        "--output",
        default="corpus/forge_mined",
        help="output directory for generated MachLib records",
    )
    parser.add_argument("--limit", type=int, default=None,
                        help="cap on number of baseline entries to process")
    parser.add_argument("--dry-run", action="store_true",
                        help="walk and report stats; write nothing")
    args = parser.parse_args(argv)

    forge_root = Path(args.forge_root)
    baseline_path = forge_root / "tools" / "benchmarks" / "vertical_baseline.json"
    industries_root = forge_root / "industries"

    if not baseline_path.is_file():
        print(f"baseline not found: {baseline_path}", file=sys.stderr)
        return 1
    if not industries_root.is_dir():
        print(f"industries dir not found: {industries_root}", file=sys.stderr)
        return 1

    baseline = _load_baseline(baseline_path)
    eml_index = _build_eml_index(industries_root)

    print(
        f"forge-root: {forge_root}\n"
        f"baseline entries: {len(baseline)}\n"
        f"eml files indexed: {len(eml_index)}\n"
        f"output: {args.output}{' [DRY RUN]' if args.dry_run else ''}",
    )

    output_root = Path(args.output)
    if not args.dry_run:
        output_root.mkdir(parents=True, exist_ok=True)

    stats = _process_baseline(
        baseline, eml_index, output_root,
        limit=args.limit, dry_run=args.dry_run,
    )

    print()
    print("=== summary ===")
    print(f"  functions processed: {stats['functions_processed']}")
    print(f"  records written:     {stats['records_written']}")
    print(f"  skipped:             {stats['skipped_count']}")
    if stats["skipped_reasons"]:
        print("  skipped reasons (first 10):")
        for r in stats["skipped_reasons"]:
            print(f"    - {r}")
    print("  by property:")
    for prop, n in sorted(stats["by_property"].items()):
        print(f"    {prop:30s} {n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
