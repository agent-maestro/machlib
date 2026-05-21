"""CLI for the local draft eml-records package."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .loaders import load_records
from .schema import RecordFamily
from .validators import validate_records


FAMILY_ALIASES = {
    "lane-seed": RecordFamily.LANE_SEED.value,
    "function-class": RecordFamily.FUNCTION_CLASS.value,
    "stochastic-hybrid": RecordFamily.STOCHASTIC_HYBRID.value,
    "evidence-record": RecordFamily.EVIDENCE_RECORD.value,
    "unknown": RecordFamily.UNKNOWN.value,
}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="eml-records")
    sub = parser.add_subparsers(dest="command", required=True)
    validate = sub.add_parser("validate")
    validate.add_argument("path", type=Path)
    validate.add_argument("--json", action="store_true", dest="as_json")
    validate.add_argument("--family", choices=sorted(FAMILY_ALIASES))
    validate.add_argument("--strict", action="store_true")
    args = parser.parse_args(argv)

    records, load_failures, scanned_file_count = load_records(args.path)
    result = validate_records(records, strict=args.strict)
    failures = [*load_failures, *result.failures]
    family_counts = dict(result.family_counts)
    if args.family:
        wanted = FAMILY_ALIASES[args.family]
        missing = result.record_count > 0 and family_counts.get(wanted, 0) == 0
        if missing:
            failures.append(f"expected family {wanted} was not found")

    summary = result.to_dict()
    summary.update(
        {
            "scanned_file_count": scanned_file_count,
            "failure_count": len(failures),
            "failures": failures,
            "valid": not failures,
            "family_filter": FAMILY_ALIASES.get(args.family) if args.family else None,
        }
    )
    if args.as_json:
        print(json.dumps(summary, indent=2, sort_keys=True))
    else:
        status = "PASS" if summary["valid"] else "FAIL"
        print(f"EML_RECORDS {status} {scanned_file_count} files {result.record_count} records")
        print(f"valid_count={result.valid_count}")
        print(f"warning_count={result.warning_count}")
        print(f"failure_count={summary['failure_count']}")
        print(f"family_counts={json.dumps(family_counts, sort_keys=True)}")

    if args.strict and failures:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
