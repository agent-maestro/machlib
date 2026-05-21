from __future__ import annotations

import argparse
import json
from typing import Sequence

from .boundaries import boundary_lines
from .summary import package_summary, toolchain


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(prog="machlib")
    subparsers = parser.add_subparsers(dest="command", required=True)

    info = subparsers.add_parser("info")
    info.add_argument("--json", action="store_true")

    subparsers.add_parser("boundaries")
    subparsers.add_parser("toolchain")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = build_parser().parse_args(argv)

    if args.command == "info":
        summary = package_summary()
        if args.json:
            print(json.dumps(summary, indent=2, sort_keys=True))
        else:
            print(f"{summary['package_name']} {summary['version']} ({summary['status']})")
            print(summary["purpose"])
        return 0

    if args.command == "boundaries":
        for line in boundary_lines():
            print(f"- {line}")
        return 0

    if args.command == "toolchain":
        for row in toolchain():
            print(f"{row['package_name']}: {row['purpose']}")
        return 0

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
