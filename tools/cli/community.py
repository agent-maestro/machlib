"""`machlib new` / `machlib validate` — frictionless contribution helpers.

Phase E from monogate-research/roadmap/machlib-v2-strength.md.

The promise: anyone can add a record in <5 minutes. ``new`` writes a
schema-conformant skeleton with ``TODO`` markers; ``validate`` checks
the result against ``corpus/schema/v1.0.0.json`` before submission.

Usage::

    machlib new my_theorem_about_exp
    # → corpus/community/my_theorem_about_exp.json (skeleton)

    machlib validate corpus/community/my_theorem_about_exp.json
    # → "valid" or detailed errors

The ``submit`` subcommand is intentionally absent today: it requires
the API endpoint at api.monogate.dev to accept community records,
which is a deployment concern outside Phase E's scope. Until then,
contributors open a PR with their record under ``corpus/community/``.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from datetime import date
from pathlib import Path

# Default skeleton fields.
SCHEMA_VERSION = "1.0.0"
DEFAULT_DOMAIN = "community"
DEFAULT_LANE = 2
SCHEMA_PATH_PARTS = ("corpus", "schema", "v1.0.0.json")
COMMUNITY_DIR_PARTS = ("corpus", "community")

_VALID_ID = re.compile(r"^[A-Za-z][A-Za-z0-9_]*$")


# ─── `new` ─────────────────────────────────────────────────────────


def add_new_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument(
        "name",
        help="theorem id (snake_case, letters/digits/underscores only)",
    )
    parser.add_argument(
        "--out-dir",
        default=str(Path(*COMMUNITY_DIR_PARTS)),
        help=f"output directory (default: {Path(*COMMUNITY_DIR_PARTS).as_posix()})",
    )
    parser.add_argument(
        "--domain",
        default=DEFAULT_DOMAIN,
        help=f"theorem domain (default: {DEFAULT_DOMAIN!r})",
    )
    parser.add_argument(
        "--lane",
        type=int,
        default=DEFAULT_LANE,
        choices=range(1, 10),
        help=f"difficulty lane 1-9 (default: {DEFAULT_LANE})",
    )
    parser.add_argument(
        "--force",
        action="store_true",
        help="overwrite if file already exists",
    )


def _skeleton(name: str, domain: str, lane: int) -> dict:
    return {
        "schema_version": SCHEMA_VERSION,
        "theorem": {
            "id":                name,
            "base_id":           name,
            "variant_strategy":  None,
            "statement": {
                "informal":         "TODO: one-sentence plain-English statement",
                "formal_lean":      "theorem {0} : TODO := sorry".format(name),
                "formal_eml_lang":  None
            },
            "domain":  domain,
            "lane":    lane,
            "tags":    ["community", f"lane-{lane}"]
        },
        "proofs": [],
        "difficulty": {
            "lane":                          lane,
            "label":                         _lane_label(lane),
            "calibrated_from_attempts":      0,
            "average_hint_level_at_solve":   0.0,
            "prerequisite_skills":           []
        },
        "common_mistakes": [],
        "tactic_trace": {
            "successful":              {},
            "failed":                  {},
            "success_rate_by_tactic":  {}
        },
        "structural_profile": {
            "chain_order":  None,
            "cost_class":   None,
            "eml_depth":    None,
            "dynamics":     {"oscillations": 0, "decays": 0},
            "drift_risk":   "LOW",
            "fpga_estimate": None
        },
        "relationships": {
            "parent":               None,
            "siblings":             [],
            "depends_on":           [],
            "structural_siblings":  []
        },
        "metadata": {
            "verified":              False,
            "verification_method":   "pending",
            "generated_by":          "machlib_new_v1",
            "creation_date":         date.today().isoformat()
        }
    }


def _lane_label(lane: int) -> str:
    if lane <= 1:
        return "beginner"
    if lane <= 3:
        return "intermediate"
    if lane <= 5:
        return "advanced"
    if lane <= 7:
        return "expert"
    return "open"


def run_new(args: argparse.Namespace) -> int:
    if not _VALID_ID.match(args.name):
        print(
            f"error: invalid name {args.name!r}; must be snake_case "
            f"(letters / digits / underscores; first char a letter)",
            file=sys.stderr,
        )
        return 2

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    target = out_dir / f"{args.name}.json"

    if target.exists() and not args.force:
        print(
            f"error: {target} already exists; pass --force to overwrite",
            file=sys.stderr,
        )
        return 1

    skeleton = _skeleton(args.name, args.domain, args.lane)
    target.write_text(
        json.dumps(skeleton, indent=2, ensure_ascii=False),
        encoding="utf-8",
    )
    print(f"created  {target}")
    print()
    print("next:")
    print("  1. edit the TODO markers in the file")
    print(f"  2. run:  machlib validate {target.as_posix()}")
    print("  3. when valid, open a PR adding the file to the corpus")
    return 0


# ─── `validate` ───────────────────────────────────────────────────


def add_validate_arguments(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("path", help="record file to validate")
    parser.add_argument(
        "--schema",
        default=str(Path(*SCHEMA_PATH_PARTS)),
        help=f"schema file (default: {Path(*SCHEMA_PATH_PARTS).as_posix()})",
    )
    parser.add_argument(
        "--strict-todos",
        action="store_true",
        help="treat any leftover 'TODO' marker as an error",
    )


def _load_json(path: Path, label: str) -> dict | None:
    if not path.is_file():
        print(f"error: {label} not found: {path}", file=sys.stderr)
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as e:
        print(f"error: {label} is not valid JSON: {e}", file=sys.stderr)
        return None


def run_validate(args: argparse.Namespace) -> int:
    record_path = Path(args.path)
    schema_path = Path(args.schema)

    record = _load_json(record_path, "record")
    if record is None:
        return 1
    schema = _load_json(schema_path, "schema")
    if schema is None:
        return 1

    try:
        import jsonschema  # type: ignore
    except ImportError:
        print(
            "error: jsonschema not installed; "
            "pip install jsonschema  (or: pip install machlib[dev])",
            file=sys.stderr,
        )
        return 1

    validator = jsonschema.Draft202012Validator(schema)
    errors = sorted(validator.iter_errors(record), key=lambda e: list(e.absolute_path))

    if errors:
        print(f"INVALID  {record_path}")
        print(f"  {len(errors)} schema error(s):")
        for e in errors:
            location = ".".join(str(p) for p in e.absolute_path) or "<root>"
            print(f"    {location}: {e.message}")
        return 1

    # Soft warnings — schema-valid but contributor likely forgot to fill in.
    warnings: list[str] = []
    informal = record.get("theorem", {}).get("statement", {}).get("informal", "")
    formal_lean = record.get("theorem", {}).get("statement", {}).get("formal_lean", "")

    todo_markers = []
    if "TODO" in informal:
        todo_markers.append("theorem.statement.informal")
    if formal_lean and "TODO" in formal_lean:
        todo_markers.append("theorem.statement.formal_lean")

    if todo_markers:
        msg = (
            "TODO marker still present in: " + ", ".join(todo_markers)
        )
        if args.strict_todos:
            print(f"INVALID  {record_path}")
            print(f"  --strict-todos: {msg}")
            return 1
        warnings.append(msg)

    if not record.get("proofs"):
        warnings.append("no proofs[] entries; record is statement-only")

    print(f"valid    {record_path}")
    if warnings:
        print(f"  {len(warnings)} warning(s):")
        for w in warnings:
            print(f"    - {w}")
    return 0
