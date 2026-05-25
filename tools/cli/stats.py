"""`machlib stats` — corpus statistics."""
from __future__ import annotations

import json
from collections import Counter
from pathlib import Path
from typing import Any


def _walk_records(corpus_root: Path) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for path in corpus_root.rglob("*.json"):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            continue
        if (
            isinstance(data, dict)
            and "schema_version" in data
            and isinstance(data.get("theorem"), dict)
        ):
            out.append(data)
    return out


def compute_stats(records: list[dict[str, Any]]) -> dict[str, Any]:
    domains = Counter(r["theorem"]["domain"] for r in records)
    lanes = Counter(r["theorem"]["lane"] for r in records)
    proof_styles = Counter(
        p.get("style", "unknown") for r in records for p in r.get("proofs", [])
    )
    proofs_per_record = [len(r.get("proofs", [])) for r in records]
    discovered_by = Counter(
        p.get("discovered_by", "unknown")
        for r in records
        for p in r.get("proofs", [])
    )
    verified = sum(1 for r in records if r.get("metadata", {}).get("verified"))
    return {
        "total_records": len(records),
        "verified_records": verified,
        "domains": dict(domains),
        "lanes": dict(sorted(lanes.items())),
        "proof_styles": dict(proof_styles),
        "discovered_by": dict(discovered_by),
        "proofs_total": sum(proofs_per_record),
        "proofs_per_record_mean": (
            sum(proofs_per_record) / len(proofs_per_record)
            if proofs_per_record else 0.0
        ),
    }


def render_text(stats: dict[str, Any]) -> str:
    lines = [
        "MachLib corpus statistics",
        "=" * 30,
        f"  total records      : {stats['total_records']}",
        f"  verified           : {stats['verified_records']}",
        f"  total proofs       : {stats['proofs_total']}",
        f"  proofs / record    : {stats['proofs_per_record_mean']:.2f}",
        "",
        "  by domain:",
    ]
    for k, v in stats["domains"].items():
        lines.append(f"    {k:20s} {v}")
    lines.append("  by lane:")
    for k, v in stats["lanes"].items():
        lines.append(f"    lane {k}              {v}")
    lines.append("  by proof style:")
    for k, v in stats["proof_styles"].items():
        lines.append(f"    {k:20s} {v}")
    lines.append("  by discoverer:")
    for k, v in stats["discovered_by"].items():
        lines.append(f"    {k:20s} {v}")
    return "\n".join(lines)


def run(corpus: str, fmt: str) -> int:
    root = Path(corpus)
    if not root.exists():
        print(f"corpus not found: {root}")
        return 1
    records = _walk_records(root)
    stats = compute_stats(records)
    if fmt == "json":
        print(json.dumps(stats, indent=2))
    else:
        print(render_text(stats))
    return 0
