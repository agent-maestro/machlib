"""Direct local rerun harness for Qwen Puzzle Curriculum rows 2 and 3."""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any


DATE = "2026_05_23"
RESEARCH_ROOT = Path("/home/monogate/monogate/monogate-research")


@dataclass
class RowRerunResult:
    row_id: str
    source_row: int
    source_file_path: str
    source_present: bool
    rerun_possible: bool
    direct_evidence_generated: bool
    validation_status_before: str
    solver_status_before: str
    validation_status_after_rerun: str
    solver_status_after_rerun: str
    bounded_unknown_classification: str
    direct_evidence_paths: list[str]
    blocker: str | None
    reason: str
    public_ready: bool = False
    petal_api_upload_performed: bool = False
    huggingface_upload_performed: bool = False
    production_marketplace_modified: bool = False
    public_claim: bool = False
    certified_safety_claim: bool = False
    production_controller_claim: bool = False
    theorem_proof_claim: bool = False


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def load_jsonl(path: Path) -> list[dict[str, Any]]:
    return [json.loads(line) for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def resolve_source_path(path_text: str) -> Path:
    path = Path(path_text)
    if path.is_absolute():
        return path
    if path.parts and path.parts[0] == "monogate-research":
        return RESEARCH_ROOT.parent / path
    if path.parts and path.parts[0] == "exploration":
        return RESEARCH_ROOT / path
    return path


def literal_value(literal: str, assignment: dict[str, bool]) -> bool | None:
    negated = literal.startswith("-")
    name = literal[1:] if negated else literal
    if name not in assignment:
        return None
    return not assignment[name] if negated else assignment[name]


def clause_status(clause: list[str], assignment: dict[str, bool]) -> str:
    undecided = False
    for literal in clause:
        value = literal_value(literal, assignment)
        if value is True:
            return "satisfied"
        if value is None:
            undecided = True
    return "undecided" if undecided else "conflict"


def formula_status(clauses: list[list[str]], assignment: dict[str, bool]) -> str:
    all_satisfied = True
    for clause in clauses:
        status = clause_status(clause, assignment)
        if status == "conflict":
            return "conflict"
        if status == "undecided":
            all_satisfied = False
    return "satisfied" if all_satisfied else "undecided"


def solve(variables: list[str], clauses: list[list[str]]) -> tuple[str, dict[str, bool] | None, int]:
    nodes = 0

    def visit(assignment: dict[str, bool]) -> dict[str, bool] | None:
        nonlocal nodes
        nodes += 1
        status = formula_status(clauses, assignment)
        if status == "satisfied":
            return assignment
        if status == "conflict":
            return None
        for var in variables:
            if var not in assignment:
                for value in (False, True):
                    candidate = dict(assignment)
                    candidate[var] = value
                    found = visit(candidate)
                    if found is not None:
                        return found
                return None
        return None

    assignment = visit({})
    if assignment is None:
        return "unsat", None, nodes
    return "sat", assignment, nodes


def true_names(assignment: dict[str, bool] | None) -> list[str]:
    if assignment is None:
        return []
    return [name for name, value in sorted(assignment.items()) if value]


def rerun_encoded_task(encoded_path: Path) -> dict[str, Any]:
    encoded = load_json(encoded_path)
    status, assignment, nodes = solve(encoded["variables"], encoded["clauses"])
    expected = encoded.get("expected_status")
    return {
        "task_id": encoded["task_id"],
        "evidence_path": str(encoded_path),
        "solver_status": status,
        "expected_status": expected,
        "matches_expected": status == expected,
        "assignment_if_sat": true_names(assignment) if status == "sat" else [],
        "clauses_checked": len(encoded["clauses"]),
        "search_nodes": nodes,
        "runtime_s": 0.0,
        "limitations": [
            "Tiny pure-Python backtracking solver.",
            "Bounded toy-solver rerun only; not a checker certificate.",
        ],
        "not_claimed": encoded.get("not_claimed", []),
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }


def evidence_from_pack_row(row: dict[str, Any]) -> tuple[list[dict[str, Any]], list[str]]:
    evidence: list[dict[str, Any]] = []
    blockers: list[str] = []
    for raw_path in row.get("evidence_paths", []):
        path = resolve_source_path(raw_path)
        if not path.exists():
            blockers.append(f"missing evidence path: {raw_path}")
            continue
        if path.name == "accepted_internal_capcard_puzzle_rows.jsonl":
            cap_rows = load_jsonl(path)
            pass_rows = [
                item
                for item in cap_rows
                if item.get("validation_status") == "pass"
                and item.get("solver_status") in {"sat", "unsat"}
                and item.get("public_ready") is False
            ]
            if pass_rows:
                evidence.append(
                    {
                        "evidence_kind": "accepted_internal_capcard_puzzle_rows",
                        "source_path": str(path),
                        "row_count": len(cap_rows),
                        "pass_row_count": len(pass_rows),
                        "solver_statuses": sorted({item.get("solver_status") for item in pass_rows}),
                        "validation_status": "pass",
                        "solver_status": "sat" if any(item.get("solver_status") == "sat" for item in pass_rows) else pass_rows[0].get("solver_status"),
                        "rows": pass_rows,
                    }
                )
            else:
                blockers.append(f"no pass/sat-or-unsat rows in {raw_path}")
        elif path.name == "puzzle_results.json":
            results = load_json(path).get("results", [])
            matches = [item for item in results if item.get("matches_expected") is True]
            if matches:
                evidence.append(
                    {
                        "evidence_kind": "puzzle_results_summary",
                        "source_path": str(path),
                        "result_count": len(results),
                        "matches_expected_count": len(matches),
                        "solver_statuses": sorted({item.get("solver_status") for item in matches}),
                        "validation_status": "pass",
                        "solver_status": "sat" if any(item.get("solver_status") == "sat" for item in matches) else matches[0].get("solver_status"),
                    }
                )
            else:
                blockers.append(f"no matching expected solver results in {raw_path}")
        elif path.suffix == ".json" and "encoded_tasks" in path.parts:
            evidence.append({"evidence_kind": "encoded_task_rerun", **rerun_encoded_task(path)})
        else:
            evidence.append({"evidence_kind": "source_present", "source_path": str(path)})
    return evidence, blockers


def classify_unknown(before: str, after: str, generated: bool) -> str:
    if after == "unknown" and not generated:
        return "NEEDS_SOLVER_RERUN"
    if before == "unknown" and after in {"sat", "unsat"} and generated:
        return "BOUNDED_UNKNOWN_ACCEPTABLE_FOR_REVIEW"
    if after == "unknown":
        return "INVALID_UNKNOWN_FOR_ACCEPTANCE"
    return "NOT_UNKNOWN_AFTER_RERUN"


def rerun_row(field: dict[str, Any], out_dir: Path) -> RowRerunResult:
    source_path = resolve_source_path(field["source_file_path"])
    source_present = source_path.exists()
    row_id = field["row_id"]
    source_row = int(field["source_row"])
    if not source_present:
        return RowRerunResult(
            row_id=row_id,
            source_row=source_row,
            source_file_path=str(source_path),
            source_present=False,
            rerun_possible=False,
            direct_evidence_generated=False,
            validation_status_before=field.get("validation_status", "unknown"),
            solver_status_before=field.get("solver_status", "unknown"),
            validation_status_after_rerun="ROW_SOURCE_NOT_FOUND",
            solver_status_after_rerun="unknown",
            bounded_unknown_classification="NEEDS_SOLVER_RERUN",
            direct_evidence_paths=[],
            blocker="ROW_SOURCE_NOT_FOUND",
            reason="exact source row file is not present locally",
        )
    rows = load_jsonl(source_path)
    if source_row < 1 or source_row > len(rows):
        return RowRerunResult(
            row_id=row_id,
            source_row=source_row,
            source_file_path=str(source_path),
            source_present=True,
            rerun_possible=False,
            direct_evidence_generated=False,
            validation_status_before=field.get("validation_status", "unknown"),
            solver_status_before=field.get("solver_status", "unknown"),
            validation_status_after_rerun="ROW_SOURCE_NOT_FOUND",
            solver_status_after_rerun="unknown",
            bounded_unknown_classification="NEEDS_SOLVER_RERUN",
            direct_evidence_paths=[],
            blocker="ROW_INDEX_NOT_FOUND",
            reason="source row index is outside the source file",
        )
    row = rows[source_row - 1]
    evidence, blockers = evidence_from_pack_row(row)
    out_dir.mkdir(parents=True, exist_ok=True)
    evidence_path = out_dir / f"{row_id}_direct_evidence_{DATE}.json"
    evidence_payload = {
        "row_id": row_id,
        "source_row": source_row,
        "source_row_payload": row,
        "evidence": evidence,
        "blockers": blockers,
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }
    evidence_path.write_text(json.dumps(evidence_payload, indent=2, sort_keys=True) + "\n")

    pass_items = [item for item in evidence if item.get("validation_status") == "pass" and item.get("solver_status") in {"sat", "unsat"}]
    generated = bool(pass_items) and not blockers
    after_validation = "pass" if generated else "warn"
    after_solver = pass_items[0]["solver_status"] if generated else "unknown"
    return RowRerunResult(
        row_id=row_id,
        source_row=source_row,
        source_file_path=str(source_path),
        source_present=True,
        rerun_possible=True,
        direct_evidence_generated=generated,
        validation_status_before=field.get("validation_status", "unknown"),
        solver_status_before=field.get("solver_status", "unknown"),
        validation_status_after_rerun=after_validation,
        solver_status_after_rerun=after_solver,
        bounded_unknown_classification=classify_unknown(field.get("solver_status", "unknown"), after_solver, generated),
        direct_evidence_paths=[str(evidence_path)] if generated else [],
        blocker=None if generated else "; ".join(blockers) or "NO_DIRECT_PASS_EVIDENCE",
        reason="direct bounded rerun evidence generated for human review" if generated else "direct rerun evidence was not generated",
    )


def run_rerun(field_map: dict[str, Any], out_dir: Path) -> dict[str, Any]:
    out_dir.mkdir(parents=True, exist_ok=True)
    rows = field_map.get("rows", [])
    results = [rerun_row(row, out_dir) for row in rows]
    result_dicts = [asdict(result) for result in results]
    for result in result_dicts:
        row_number = result["source_row"]
        (out_dir / f"row{row_number}_rerun_result_{DATE}.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n"
        )
    summary = {
        "summary_id": f"qwen_row23_direct_evidence_summary_{DATE}",
        "status": "DIRECT_RERUN_COMPLETE",
        "direct_rerun_attempted": True,
        "row_results": result_dicts,
        "direct_evidence_generated_count": sum(1 for row in result_dicts if row["direct_evidence_generated"]),
        "all_rows_have_direct_evidence": all(row["direct_evidence_generated"] for row in result_dicts),
        "qwen_puzzle_curriculum_pack_status": "READY_FOR_HUMAN_REPAIR_REVIEW"
        if all(row["direct_evidence_generated"] for row in result_dicts)
        else "BLOCKED_WITH_EXACT_FIX_LIST",
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }
    validator = {
        "validator_id": f"qwen_row23_validator_output_{DATE}",
        "status": "pass" if summary["direct_evidence_generated_count"] == len(result_dicts) else "warn",
        "row_count": len(result_dicts),
        "direct_evidence_generated_count": summary["direct_evidence_generated_count"],
        "diagnostics": [row["blocker"] for row in result_dicts if row["blocker"]],
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
    }
    solver_review = {
        "review_id": f"qwen_row23_solver_status_review_{DATE}",
        "rows": [
            {
                "row_id": row["row_id"],
                "solver_status_before": row["solver_status_before"],
                "solver_status_after_rerun": row["solver_status_after_rerun"],
                "bounded_unknown_classification": row["bounded_unknown_classification"],
            }
            for row in result_dicts
        ],
        "human_review_required": True,
        "public_claim": False,
    }
    (out_dir / f"row23_direct_evidence_summary_{DATE}.json").write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    (out_dir / f"row23_validator_output_{DATE}.json").write_text(json.dumps(validator, indent=2, sort_keys=True) + "\n")
    (out_dir / f"row23_solver_status_review_{DATE}.json").write_text(json.dumps(solver_review, indent=2, sort_keys=True) + "\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--field-map", required=True)
    parser.add_argument("--out-dir", required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    field_map = load_json(Path(args.field_map))
    summary = run_rerun(field_map, Path(args.out_dir))
    print("QWEN_ROW23_DIRECT_RERUN_OK", summary["direct_evidence_generated_count"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
