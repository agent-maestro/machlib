import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_function_classes_draft")
TOOL = Path("tools/run_analytic_local_series_harness.py")


def load_harness():
    spec = importlib.util.spec_from_file_location("run_analytic_local_series_harness", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_loads_four_analytic_records():
    harness = load_harness()
    records = harness.load_analytic_records(ROOT)
    assert len(records) == 4
    assert {row["record_id"] for row in records} == harness.EXPECTED_RECORDS


def test_local_series_spec_ids_present():
    harness = load_harness()
    spec = harness.build_spec_payload()
    ids = {row["spec_id"] for row in spec["local_series_specs"]}
    assert harness.REQUIRED_SPEC_IDS <= ids
    for row in spec["local_series_specs"]:
        assert row["zero_mathlib_dependency"] is True
        assert row["public_ready"] is False
        assert row["upload_allowed"] is False
        assert row["release_ready"] is False
        assert row["mathlib_dependency"] is False


def test_bounded_coefficient_patterns():
    harness = load_harness()
    exp = harness.exp_series_check()
    assert exp["passed"] is True
    assert exp["coefficients"] == ["1", "1", "1/2", "1/6", "1/24"]
    sin_cos = harness.sin_cos_series_check()
    assert sin_cos["passed"] is True
    assert sin_cos["sin_coefficients"]["x^5"] == "1/120"
    assert sin_cos["cos_coefficients"]["x^4"] == "1/24"
    rational = harness.rational_series_check()
    assert rational["passed"] is True
    assert rational["coefficients"] == ["1", "1", "1", "1", "1"]
    assert "1" in rational["excluded_points"]


def test_records_carry_non_overclaim_boundaries():
    harness = load_harness()
    records = harness.load_analytic_records(ROOT)
    for record in records:
        text = str(record).lower()
        assert "convergence proof" in text
        assert "global" in text
        assert "public proof" in text or "theorem" in text
        assert record["status"] == "DRAFT_INTERNAL"


def test_build_all_generates_artifacts_and_guardrails(tmp_path):
    harness = load_harness()
    execution, roundtrip, spec = harness.build_all(ROOT, tmp_path)
    assert execution["record_count"] == 4
    assert execution["passed"] == 4
    assert execution["failed"] == 0
    assert execution["zero_mathlib_status"] == "PASS"
    assert execution["guardrails"]["no_convergence_claim"] is True
    assert execution["guardrails"]["no_global_analytic_claim"] is True
    assert all(value is True for value in execution["guardrails"].values())
    assert roundtrip["record_count"] == 4
    assert roundtrip["failed"] == 0
    assert roundtrip["zero_mathlib_status"] == "PASS"
    assert spec["spec_count"] >= 8
    artifacts = sorted((tmp_path / "eml").glob("*.eml"))
    assert len(artifacts) == 4
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
    for record in harness.load_analytic_records(ROOT):
        assert record["public_ready"] is False
        assert record["upload_allowed"] is False
        assert record["release_ready"] is False
        assert record["mathlib_dependency"] is False
        assert record["forge_compiler_change_required"] is False
        assert record["hardware_required"] is False
