"""CLI for the local draft review-branch-packet package."""

from __future__ import annotations

import argparse
from pathlib import Path

from .git_inspect import inspect_repo
from .packet import build_packet_from_inspection
from .render import render_json_packet, render_markdown_packet


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="review-branch-packet")
    sub = parser.add_subparsers(dest="command", required=True)
    inspect = sub.add_parser("inspect")
    inspect.add_argument("--target", required=True)
    inspect.add_argument("--remote", default="origin")
    inspect.add_argument("--repo", type=Path, default=Path("."))
    inspect.add_argument("--log-limit", type=int, default=10)
    inspect.add_argument("--json", action="store_true", dest="as_json")
    inspect.add_argument("--out", type=Path)
    inspect.add_argument("--markdown-out", type=Path)
    inspect.add_argument("--include-validation-placeholder", action="store_true")
    args = parser.parse_args(argv)

    inspection = inspect_repo(
        target_review_branch=args.target,
        cwd=args.repo,
        remote_name=args.remote,
        log_limit=args.log_limit,
    )
    validation_summaries = None
    if args.include_validation_placeholder:
        validation_summaries = [{"name": "validation placeholder", "status": "NOT_RUN"}]
    packet = build_packet_from_inspection(inspection, validation_summaries=validation_summaries)

    json_text = render_json_packet(packet)
    markdown_text = render_markdown_packet(packet)

    if args.out:
        args.out.write_text(json_text, encoding="utf-8")
    if args.markdown_out:
        args.markdown_out.write_text(markdown_text, encoding="utf-8")
    if args.as_json or not args.markdown_out:
        print(json_text, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
