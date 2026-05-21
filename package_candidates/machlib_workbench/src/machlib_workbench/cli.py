from __future__ import annotations

import argparse
import json
from typing import Sequence

from .summary import summarize_path


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="machlib-workbench")
    subparsers = parser.add_subparsers(dest="command", required=True)
    summarize = subparsers.add_parser("summarize")
    summarize.add_argument("path")
    summarize.add_argument("--json", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)
    if args.command == "summarize":
        summary = summarize_path(args.path)
        if args.json:
            print(json.dumps(summary.to_dict(), indent=2, sort_keys=True))
        else:
            print(f"files={summary.file_count} md={summary.markdown_count} json={summary.json_count}")
        return 0
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
