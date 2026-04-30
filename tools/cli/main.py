"""MachLib CLI entry point.

Usage:

    python -m tools.cli.main stats
    python -m tools.cli.main generate --strategy constant_swap
    python -m tools.cli.main verify --batch corpus/eml
    python -m tools.cli.main rank   --by cost
    python -m tools.cli.main export --format jsonl
    python -m tools.cli.main serve

Phase 0 ships `stats` only with a real implementation; the others
are stubs that print "not implemented in Phase 0".
"""
from __future__ import annotations

import argparse
import sys

from tools.cli import stats as stats_cmd


def _make_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(prog="machlib")
    sub = p.add_subparsers(dest="cmd", required=True)

    s_stats = sub.add_parser("stats", help="Dataset statistics")
    s_stats.add_argument(
        "--corpus",
        default="corpus",
        help="Corpus root directory (default: ./corpus)",
    )
    s_stats.add_argument(
        "--format",
        choices=("text", "json"),
        default="text",
    )

    sub.add_parser("generate", help="Generate synthetic variants (stub)")
    sub.add_parser("verify", help="Lean-kernel verify (stub)")
    sub.add_parser("rank", help="Rank proofs by cost (stub)")
    sub.add_parser("export", help="Export to HF / parquet (stub)")
    sub.add_parser("serve", help="Run the API server (stub)")

    return p


def main(argv: list[str] | None = None) -> int:
    args = _make_parser().parse_args(argv)
    if args.cmd == "stats":
        return stats_cmd.run(corpus=args.corpus, fmt=args.format)
    print(f"`machlib {args.cmd}` is not implemented in Phase 0.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
