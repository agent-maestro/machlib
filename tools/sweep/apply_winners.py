"""Apply Tier-1 closures to MachLib/Discovered/ source files (C-239).

For each closed record in ``results_tier1.jsonl``:
  - look up the theorem fresh via ``extract_all`` (line numbers may
    have shifted after regen, so we don't trust the JSONL's
    ``source_line`` field; we trust ``theorem_name`` instead)
  - replace ONLY that theorem's ``sorry  -- TODO: ...`` line with
    the joined tactic sequence at the same indentation
  - write the file back

Idempotent: running twice on an already-applied file is a no-op
(the target sorry is already gone, so the lookup skips it).

Reports per-file counts, dry-run by default unless ``--apply`` is
passed.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

from .extract import extract_all


def _machlib_root() -> Path:
    return Path(__file__).resolve().parent.parent.parent


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--results", type=Path,
                   default=_machlib_root().parent / "monogate-research" /
                           "exploration" / "C239_bfs_proof_sweep" /
                           "results_tier1.jsonl")
    p.add_argument("--apply", action="store_true",
                   help="actually write the changes (default: dry-run)")
    args = p.parse_args(argv)

    if not args.results.is_file():
        print(f"results file not found: {args.results}")
        return 1

    closures: list[dict] = []
    for line in args.results.open(encoding="utf-8"):
        rec = json.loads(line)
        if rec["status"] == "closed" and rec.get("tactic_sequence"):
            closures.append(rec)
    print(f"Closures to apply: {len(closures)}")

    # Index extracted theorems by (file_basename, theorem_name) for
    # an O(1) lookup against the JSONL records.
    discovered = (
        _machlib_root() / "foundations" / "MachLib" / "Discovered"
    )
    extracted = list(extract_all(discovered, repo_root=_machlib_root()))
    by_key: dict[tuple[str, str], object] = {}
    for thm in extracted:
        key = (Path(thm.source_file).stem, thm.theorem_name)
        by_key[key] = thm

    n_applied = 0
    n_missing = 0
    file_texts: dict[str, str] = {}  # accumulate edits before writing

    # The target sorry text we replace (must match extract.py's
    # _TARGET_SORRY constant).
    TARGET = "sorry  -- TODO: prove against MachLib foundations"

    for rec in closures:
        thm_id = rec["theorem_id"]
        stem, name = thm_id.split(".", 1)
        key = (stem, name)
        thm = by_key.get(key)
        if thm is None:
            print(f"  MISSING in current sources: {thm_id}")
            n_missing += 1
            continue
        tactics = rec["tactic_sequence"]
        text = file_texts.setdefault(thm.source_file, thm.file_text)

        # Find the unique TARGET sorry below `theorem <name>`.
        marker = f"theorem {name}"
        idx = text.find(marker)
        if idx < 0:
            print(f"  could not locate `theorem {name}` in {thm.source_file}")
            n_missing += 1
            continue
        sorry_idx = text.find(TARGET, idx)
        if sorry_idx < 0:
            print(f"  no TARGET sorry below {marker} in {thm.source_file} "
                  f"(already applied?)")
            n_missing += 1
            continue
        replacement = "\n  ".join(tactics) if tactics else ""
        new_text = text[:sorry_idx] + replacement + text[sorry_idx + len(TARGET):]
        file_texts[thm.source_file] = new_text
        n_applied += 1
        print(f"  {'WOULD ' if not args.apply else ''}apply  {thm_id:60s}  "
              f"->  {tactics[0]}")

    if args.apply:
        for rel_path, new_text in file_texts.items():
            abs_path = _machlib_root() / rel_path
            abs_path.write_text(new_text, encoding="utf-8")
        print()
        print(f"Wrote {len(file_texts)} files. {n_applied} edits applied.")
    else:
        print()
        print(f"DRY RUN — would apply {n_applied} edits across "
              f"{len(file_texts)} files. Pass --apply to write.")
    if n_missing:
        print(f"Missing/skipped: {n_missing}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
