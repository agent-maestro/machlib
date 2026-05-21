from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Sequence

from .runner import summarize_results


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="eml-harness")
    subparsers = parser.add_subparsers(dest="command", required=True)
    summarize = subparsers.add_parser("summarize")
    summarize.add_argument("path")
    summarize.add_argument("--json", action="store_true")
    return parser


def _load_results(path: str) -> list[dict[str, object]]:
    payload = json.loads(Path(path).read_text())
    if isinstance(payload, list):
        return payload
    if isinstance(payload, dict):
        return [payload]
    raise ValueError("expected JSON object or list")


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "summarize":
        summary = summarize_results(_load_results(args.path))
        if args.json:
            print(json.dumps(summary, indent=2, sort_keys=True))
        else:
            print(f"total={summary['total']} pass={summary['pass']} fail={summary['fail']} skip={summary['skip']}")
        return 0 if summary["invalid"] == 0 and summary["fail"] == 0 else 1
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
