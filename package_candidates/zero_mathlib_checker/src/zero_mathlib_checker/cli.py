"""CLI for the local draft zero-Mathlib checker."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .scanner import scan_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="zero-mathlib-checker")
    sub = parser.add_subparsers(dest="command", required=True)
    scan = sub.add_parser("scan")
    scan.add_argument("root", type=Path)
    scan.add_argument("--json", action="store_true", dest="as_json")
    scan.add_argument("--allow-policy-text", action="store_true")
    scan.add_argument("--include", action="append", default=[])
    scan.add_argument("--exclude-dir", action="append", default=[])
    args = parser.parse_args(argv)

    result = scan_path(
        args.root,
        allow_policy_text=args.allow_policy_text,
        include=tuple(args.include),
        exclude_dirs=tuple(args.exclude_dir),
    )
    if args.as_json:
        print(json.dumps(result.to_dict(), indent=2, sort_keys=True))
    else:
        status = "PASS" if result.passed else "FAIL"
        print(f"ZERO_MATHLIB_CHECKER {status} {result.scanned_files} files")
        print(f"direct_matches={result.direct_match_count}")
        print(f"dependency_evidence={result.dependency_evidence_count}")
        print(f"policy_text={result.policy_text_count}")
        print(f"skipped_files={result.skipped_files}")
    return 0 if result.passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
