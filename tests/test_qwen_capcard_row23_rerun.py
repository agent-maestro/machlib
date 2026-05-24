import json
from pathlib import Path

from tools.qwen_capcard_lab.row23_rerun import (
    classify_unknown,
    formula_status,
    resolve_source_path,
    run_rerun,
    solve,
)


def test_resolve_monogate_research_path():
    path = resolve_source_path("monogate-research/exploration/example.json")
    assert str(path).endswith("monogate-research/exploration/example.json")


def test_resolve_exploration_path():
    path = resolve_source_path("exploration/example.json")
    assert str(path).endswith("monogate-research/exploration/example.json")


def test_formula_status_satisfied():
    assert formula_status([["a"], ["-b"]], {"a": True, "b": False}) == "satisfied"


def test_formula_status_conflict():
    assert formula_status([["a"], ["-a"]], {"a": True}) == "conflict"


def test_solver_sat():
    status, assignment, nodes = solve(["a"], [["a"]])
    assert status == "sat"
    assert assignment == {"a": True}
    assert nodes >= 1


def test_solver_unsat():
    status, assignment, _ = solve(["a"], [["a"], ["-a"]])
    assert status == "unsat"
    assert assignment is None


def test_classify_unknown_repaired_to_sat():
    assert classify_unknown("unknown", "sat", True) == "BOUNDED_UNKNOWN_ACCEPTABLE_FOR_REVIEW"


def test_classify_unknown_still_unknown_without_generation():
    assert classify_unknown("unknown", "unknown", False) == "NEEDS_SOLVER_RERUN"


def test_run_rerun_missing_source(tmp_path):
    field_map = {
        "rows": [
            {
                "row_id": "row2",
                "source_row": 2,
                "source_file_path": str(tmp_path / "missing.jsonl"),
                "validation_status": "warn",
                "solver_status": "unknown",
            }
        ]
    }
    summary = run_rerun(field_map, tmp_path / "out")
    assert summary["direct_evidence_generated_count"] == 0
    assert summary["qwen_puzzle_curriculum_pack_status"] == "BLOCKED_WITH_EXACT_FIX_LIST"


def test_run_rerun_generates_from_capcard_puzzle_rows(tmp_path):
    evidence = tmp_path / "accepted_internal_capcard_puzzle_rows.jsonl"
    evidence.write_text(
        json.dumps(
            {
                "validation_status": "pass",
                "solver_status": "sat",
                "public_ready": False,
                "evidence_paths": [],
            }
        )
        + "\n"
    )
    source = tmp_path / "accepted_internal_capcard_pack_rows.jsonl"
    source.write_text(
        json.dumps(
            {
                "evidence_paths": [str(evidence)],
                "validation_status": "warn",
                "solver_status": "unknown",
            }
        )
        + "\n"
    )
    field_map = {
        "rows": [
            {
                "row_id": "row2",
                "source_row": 1,
                "source_file_path": str(source),
                "validation_status": "warn",
                "solver_status": "unknown",
            }
        ]
    }
    summary = run_rerun(field_map, tmp_path / "out")
    assert summary["direct_evidence_generated_count"] == 1
    assert summary["qwen_puzzle_curriculum_pack_status"] == "READY_FOR_HUMAN_REPAIR_REVIEW"


def test_run_rerun_writes_row_file(tmp_path):
    source = tmp_path / "rows.jsonl"
    source.write_text(json.dumps({"evidence_paths": []}) + "\n")
    field_map = {
        "rows": [
            {
                "row_id": "row2",
                "source_row": 1,
                "source_file_path": str(source),
                "validation_status": "warn",
                "solver_status": "unknown",
            }
        ]
    }
    run_rerun(field_map, tmp_path / "out")
    assert (tmp_path / "out" / "row1_rerun_result_2026_05_23.json").exists()
