import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_function_classes_draft")
TOOL = Path("tools/run_function_boundary_harness.py")


def load_harness():
    spec = importlib.util.spec_from_file_location("run_function_boundary_harness", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_loads_three_boundary_records():
    harness = load_harness()
    records = harness.load_boundary_records(ROOT)
    assert len(records) == 3
    assert {row["record_id"] for row in records} == harness.EXPECTED_RECORDS


def test_boundary_spec_ids_present():
    harness = load_harness()
    spec = harness.build_spec_payload()
    ids = {row["spec_id"] for row in spec["boundary_specs"]}
    assert harness.REQUIRED_SPEC_IDS <= ids
    for row in spec["boundary_specs"]:
        assert row["zero_mathlib_dependency"] is True
        assert row["public_ready"] is False
        assert row["upload_allowed"] is False
        assert row["release_ready"] is False
        assert row["mathlib_dependency"] is False


def test_boundary_relation_checks():
    harness = load_harness()
    records = {row["record_id"]: row for row in harness.load_boundary_records(ROOT)}
    smooth = harness.smooth_not_analytic_boundary_check(records["smooth_not_analytic_boundary_record_v0"])
    assert smooth["passed"] is True
    assert smooth["blocked_overclaim"] == "smooth -> analytic"
    analytic = harness.analytic_not_dfinite_boundary_check(records["analytic_not_dfinite_boundary_record_v0"])
    assert analytic["passed"] is True
    assert analytic["blocked_overclaim"] == "analytic -> D-finite"
    dfinite = harness.dfinite_domain_singularity_guard_check(records["dfinite_domain_singularity_guard_v0"])
    assert dfinite["passed"] is True
    assert 0 in dfinite["singularity_candidates"]


def test_derived_gap_is_not_executable_record():
    harness = load_harness()
    gaps = harness.derived_gap_rows()
    assert len(gaps) == 1
    assert gaps[0]["gap_id"] == "continuous_not_differentiable_gap_v0"
    assert gaps[0]["counted_as_executable_record"] is False


def test_build_all_generates_artifacts_and_guardrails(tmp_path):
    harness = load_harness()
    execution, roundtrip, spec = harness.build_all(ROOT, tmp_path)
    assert execution["record_count"] == 3
    assert execution["passed"] == 3
    assert execution["failed"] == 0
    assert execution["zero_mathlib_status"] == "PASS"
    assert execution["guardrails"]["no_subset_overclaim"] is True
    assert execution["guardrails"]["no_real_analysis_completion_claim"] is True
    assert execution["guardrails"]["no_topology_formalization_claim"] is True
    assert all(value is True for value in execution["guardrails"].values())
    assert len(execution["derived_gap_rows"]) == 1
    assert roundtrip["record_count"] == 3
    assert roundtrip["failed"] == 0
    assert roundtrip["zero_mathlib_status"] == "PASS"
    assert roundtrip["guardrails"]["no_subset_overclaim"] is True
    assert spec["spec_count"] >= 7
    artifacts = sorted((tmp_path / "eml").glob("*.eml"))
    assert len(artifacts) == 3
    for path in artifacts:
        text = path.read_text(encoding="utf-8")
        assert "import " + "Mathlib" not in text
        assert "from " + "Mathlib" not in text
        assert "Mathlib" + "." not in text
    allowed_warnings = {"WARN_EXPECTED_DRAFT_SCHEMA_LIMIT", "WARN_NO_DIRECT_FORGE_COMPILE"}
    for row in roundtrip["results"]:
        if row["status"] == "WARN":
            assert row["forge_code"] in allowed_warnings or roundtrip["efrog_status"] == "WARN"


def test_no_forbidden_true_booleans():
    harness = load_harness()
    for record in harness.load_boundary_records(ROOT):
        assert record["public_ready"] is False
        assert record["upload_allowed"] is False
        assert record["release_ready"] is False
        assert record["mathlib_dependency"] is False
        assert record["forge_compiler_change_required"] is False
        assert record["hardware_required"] is False
