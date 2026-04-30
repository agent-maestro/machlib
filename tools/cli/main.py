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
from pathlib import Path

# Allow running both as `python -m tools.cli.main` and as
# `python tools/cli/main.py` (direct invocation needs the repo
# root on sys.path before the `tools.*` import resolves).
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.cli import stats as stats_cmd  # noqa: E402
from tools.cli import generate as generate_cmd  # noqa: E402


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

    s_gen = sub.add_parser("generate", help="Generate synthetic variants")
    generate_cmd.add_arguments(s_gen)
    sub.add_parser("verify", help="Lean-kernel verify (stub)")
    sub.add_parser("rank", help="Rank proofs by cost (stub)")
    sub.add_parser("export", help="Export to HF / parquet (stub)")
    sub.add_parser("serve", help="Run the API server (stub)")

    return p


def main(argv: list[str] | None = None) -> int:
    args = _make_parser().parse_args(argv)
    if args.cmd == "stats":
        return stats_cmd.run(corpus=args.corpus, fmt=args.format)
    if args.cmd == "generate":
        return generate_cmd.run(args)
    print(f"`machlib {args.cmd}` is not implemented in Phase 0.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
