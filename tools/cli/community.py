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
import os
import re
import subprocess
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
    parser.add_argument(
        "path",
        help="record file (.json), Lean file (.lean), or directory to "
             "validate. JSON is checked against the corpus schema; "
             "Lean is run through the Lean kernel via `lake env lean`.",
    )
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
    parser.add_argument(
        "--lean", action="store_true",
        help="force Lean kernel verification (auto-detected from .lean "
             "extension; use this when the file has a different suffix)",
    )
    parser.add_argument(
        "--schema-only", action="store_true",
        help="force JSON-schema validation (auto-detected from .json "
             "extension)",
    )
    parser.add_argument(
        "--lean-timeout", type=int, default=120,
        help="seconds to allow per Lean file before timing out "
             "(default: 120)",
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
    """Dispatch on file extension (or explicit flag) to either the
    JSON-schema validator or the Lean kernel verifier."""
    target = Path(args.path)
    if not target.exists():
        print(f"error: path not found: {target}", file=sys.stderr)
        return 1

    if target.is_dir():
        return _run_validate_directory(target, args)

    if args.lean or (target.suffix == ".lean" and not args.schema_only):
        return _run_validate_lean(target, timeout=args.lean_timeout)

    return _run_validate_schema(target, args)


def _run_validate_directory(root: Path, args: argparse.Namespace) -> int:
    """Validate every .json + .lean file under `root`. Returns non-zero
    if any file fails."""
    json_files = sorted(root.rglob("*.json")) if not args.lean else []
    lean_files = sorted(root.rglob("*.lean")) if not args.schema_only else []
    total = len(json_files) + len(lean_files)
    if total == 0:
        print(f"warning: no .json / .lean files found under {root}",
              file=sys.stderr)
        return 0

    print(f"# validating {total} file(s) under {root}")
    n_valid = 0
    n_invalid = 0
    for f in json_files:
        rc = _run_validate_schema(f, args)
        n_valid += int(rc == 0)
        n_invalid += int(rc != 0)
    for f in lean_files:
        rc = _run_validate_lean(f, timeout=args.lean_timeout)
        n_valid += int(rc == 0)
        n_invalid += int(rc != 0)

    print()
    print(f"# summary: {n_valid} valid, {n_invalid} invalid")
    return 0 if n_invalid == 0 else 1


def _find_machlib_foundations() -> Path | None:
    """Locate the MachLib foundations directory that holds the lake
    project. The validator runs `lake env lean` inside this dir so
    the Lean kernel can resolve `import MachLib.*`."""
    # Common locations: the package install path, and the developer
    # checkout `D:/machlib/foundations` on Windows.
    candidates = [
        Path("D:/machlib/foundations"),
        Path(__file__).resolve().parents[2] / "foundations",
        Path.cwd() / "foundations",
    ]
    for c in candidates:
        if (c / "lakefile.lean").is_file() or (c / "lakefile.toml").is_file():
            return c
    return None


def _find_lake_executable() -> Path | None:
    """Resolve the lake binary. Prefer `LAKE` env var, then
    ~/.elan/bin/lake[.exe], then PATH."""
    env_lake = os.environ.get("LAKE")
    if env_lake and Path(env_lake).is_file():
        return Path(env_lake)
    elan_dir = Path.home() / ".elan" / "bin"
    for candidate in ("lake.exe", "lake"):
        candidate_path = elan_dir / candidate
        if candidate_path.is_file():
            return candidate_path
    # Fall back to PATH lookup; subprocess.run will surface the
    # FileNotFoundError if it isn't present.
    return Path("lake")


def _run_validate_lean(lean_path: Path, *, timeout: int) -> int:
    """Run the Lean kernel verifier on a single .lean file. Uses
    `lake env lean -- <file>` from inside the MachLib foundations
    dir so MachLib.* imports resolve against the prebuilt
    `.olean` artefacts."""
    foundations = _find_machlib_foundations()
    if foundations is None:
        print(f"INVALID  {lean_path}", file=sys.stderr)
        print("  cannot locate MachLib foundations directory; "
              "checked D:/machlib/foundations and ../foundations",
              file=sys.stderr)
        return 1

    lake = _find_lake_executable()
    if lake is None:
        print(f"INVALID  {lean_path}", file=sys.stderr)
        print("  cannot locate lake binary; install elan + Lean 4 "
              "or set the LAKE env var",
              file=sys.stderr)
        return 1

    # Resolve to absolute so the subprocess's cwd switch to the
    # foundations dir doesn't break a relative input path.
    lean_abs = lean_path.resolve()
    try:
        result = subprocess.run(
            [str(lake), "env", "lean", "--", str(lean_abs)],
            cwd=str(foundations),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except FileNotFoundError as e:
        print(f"INVALID  {lean_path}", file=sys.stderr)
        print(f"  lake not runnable: {e}", file=sys.stderr)
        return 1
    except subprocess.TimeoutExpired:
        print(f"INVALID  {lean_path}")
        print(f"  Lean kernel timed out after {timeout}s")
        return 1

    # Exit code is the authoritative signal — Lean accepts iff it
    # type-checks and the kernel is satisfied. Stdout output from
    # `#check` / `#eval` directives is not an error and shouldn't
    # flag the file as invalid.
    output = (result.stdout + result.stderr).rstrip()
    if result.returncode == 0:
        print(f"valid    {lean_path}")
        return 0

    print(f"INVALID  {lean_path}  (lake env lean exit={result.returncode})")
    if output:
        for line in output.splitlines():
            print(f"  {line}")
    else:
        print("  (no diagnostics emitted; non-zero exit code only)")
    return 1


def _run_validate_schema(record_path: Path, args: argparse.Namespace) -> int:
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
