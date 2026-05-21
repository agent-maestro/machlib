"""CLI for the local draft claim-boundary scanner."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .scanner import scan_path


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="claim-boundary")
    sub = parser.add_subparsers(dest="command", required=True)
    scan = sub.add_parser("scan")
    scan.add_argument("root", type=Path)
    scan.add_argument("--json", action="store_true", dest="as_json")
    scan.add_argument("--include", action="append", default=[])
    scan.add_argument("--exclude-dir", action="append", default=[])
    scan.add_argument("--fail-on", choices=["suspicious", "never"], default="suspicious")
    args = parser.parse_args(argv)

    result = scan_path(args.root, include=tuple(args.include), exclude_dirs=tuple(args.exclude_dir))
    if args.as_json:
        print(json.dumps(result.to_dict(), indent=2, sort_keys=True))
    else:
        status = "PASS" if result.passed else "FAIL"
        print(f"CLAIM_BOUNDARY {status} {result.scanned_file_count} files")
        print(f"suspicious_findings={result.suspicious_finding_count}")
        print(f"boundary_text={result.boundary_text_count}")
        print(f"policy_text={result.policy_text_count}")
        print(f"token_like_secret={result.token_like_secret_count}")

    if args.fail_on == "suspicious" and result.suspicious_finding_count:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
