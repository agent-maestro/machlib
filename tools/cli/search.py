"""`machlib search` — keyword + facet search over the corpus.

Walks every ``corpus/**/*.json`` record, scores against the query,
and prints the top N hits. Designed for fast triage:

    machlib search "exp_log"
    machlib search "logistic" --domain physics --limit 5
    machlib search "" --tag composition_depth --lane 1

Scoring is dumb-but-useful substring matching (case-insensitive):

    +10  query in theorem.id
    + 5  query in theorem.statement.formal_lean
    + 3  query in theorem.statement.informal
    + 2  query in any theorem.tags entry
    + 1  query in theorem.base_id

Facet filters (``--domain``, ``--lane``, ``--tag``) are AND-combined
before scoring. An empty query passes everything; combined with
facets that's how to "list all lane-1 records".
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


def add_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "query",
        nargs="?",
        default="",
        help='free-text query (empty allowed when using --domain/--lane/--tag)',
    )
    parser.add_argument(
        "--corpus",
        default="corpus",
        help="corpus root directory (default: ./corpus)",
    )
    parser.add_argument(
        "--domain",
        help="restrict to a domain (eml, physics, finance, ...)",
    )
    parser.add_argument(
        "--lane",
        type=int,
        help="restrict to a lane number (1, 2, ...)",
    )
    parser.add_argument(
        "--tag",
        help="restrict to records with this tag",
    )
    parser.add_argument(
        "--limit",
        type=int,
        default=20,
        help="maximum hits to print (default: 20)",
    )
    parser.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
    )


def _load_records(corpus_root: Path) -> list[tuple[Path, dict[str, Any]]]:
    out: list[tuple[Path, dict[str, Any]]] = []
    for path in corpus_root.rglob("*.json"):
        try:
            data = json.loads(path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError):
            continue
        if isinstance(data, dict) and "schema_version" in data:
            out.append((path, data))
    return out


def _score(record: dict[str, Any], query_lower: str) -> int:
    if not query_lower:
        return 0
    thm = record.get("theorem", {})
    statement = thm.get("statement", {})
    score = 0
    if query_lower in str(thm.get("id", "")).lower():
        score += 10
    if query_lower in str(statement.get("formal_lean", "")).lower():
        score += 5
    if query_lower in str(statement.get("informal", "")).lower():
        score += 3
    for tag in thm.get("tags", []) or []:
        if query_lower in str(tag).lower():
            score += 2
            break
    if query_lower in str(thm.get("base_id", "")).lower():
        score += 1
    return score


def _passes_facets(
    record: dict[str, Any],
    domain: str | None,
    lane: int | None,
    tag: str | None,
) -> bool:
    thm = record.get("theorem", {})
    if domain is not None and thm.get("domain") != domain:
        return False
    if lane is not None and thm.get("lane") != lane:
        return False
    if tag is not None:
        tags = thm.get("tags", []) or []
        if tag not in tags:
            return False
    return True


def _render_text(hits: list[tuple[Path, dict[str, Any], int]]) -> str:
    if not hits:
        return "(no matches)"
    lines = []
    for path, record, score in hits:
        thm = record.get("theorem", {})
        rel = path
        try:
            rel = path.relative_to(Path.cwd())
        except ValueError:
            pass
        lines.append(
            f"  [{score:>3}]  {thm.get('id', '?')}  "
            f"(domain={thm.get('domain', '?')}, lane={thm.get('lane', '?')})"
        )
        informal = (thm.get("statement", {}) or {}).get("informal") or ""
        if informal:
            short = informal.strip().splitlines()[0][:120]
            lines.append(f"         {short}")
        lines.append(f"         {rel}")
        lines.append("")
    return "\n".join(lines).rstrip()


def _render_json(hits: list[tuple[Path, dict[str, Any], int]]) -> str:
    payload = []
    for path, record, score in hits:
        thm = record.get("theorem", {})
        payload.append({
            "score": score,
            "id": thm.get("id"),
            "base_id": thm.get("base_id"),
            "domain": thm.get("domain"),
            "lane": thm.get("lane"),
            "tags": thm.get("tags", []),
            "informal": (thm.get("statement", {}) or {}).get("informal"),
            "path": str(path),
        })
    return json.dumps(payload, indent=2)


def run(args: argparse.Namespace) -> int:
    root = Path(args.corpus)
    if not root.exists():
        print(f"corpus not found: {root}")
        return 1
    query_lower = args.query.lower().strip()
    records = _load_records(root)
    hits: list[tuple[Path, dict[str, Any], int]] = []
    for path, record in records:
        if not _passes_facets(record, args.domain, args.lane, args.tag):
            continue
        score = _score(record, query_lower)
        if query_lower and score == 0:
            continue
        hits.append((path, record, score))
    # Stable sort: highest score first, then by id alphabetically.
    hits.sort(
        key=lambda h: (-h[2], h[1].get("theorem", {}).get("id", "")),
    )
    hits = hits[: args.limit]
    if args.format == "json":
        print(_render_json(hits))
    else:
        print(_render_text(hits))
        if len(hits) == args.limit:
            print(f"\n  (showing first {args.limit}; raise --limit for more)")
    return 0
