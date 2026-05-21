from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

from .trace import increments, transition_counts


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="hybrid-trace-eml")
    subparsers = parser.add_subparsers(dest="command", required=True)
    summarize = subparsers.add_parser("summarize")
    summarize.add_argument("path")
    summarize.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "summarize":
        payload = json.loads(Path(args.path).read_text())
        result = {
            "increments": increments([float(value) for value in payload.get("values", [])]),
            "transition_counts": transition_counts([str(value) for value in payload.get("states", [])]),
        }
        if args.json:
            print(json.dumps(result, indent=2, sort_keys=True))
        else:
            print(f"increments={len(result['increments'])} transitions={len(result['transition_counts'])}")
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
