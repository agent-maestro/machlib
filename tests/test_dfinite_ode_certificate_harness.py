import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_function_classes_draft")
TOOL = Path("tools/run_dfinite_ode_certificate_harness.py")


def load_harness():
    spec = importlib.util.spec_from_file_location("run_dfinite_ode_certificate_harness", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_loads_five_dfinite_records():
    harness = load_harness()
    records = harness.load_dfinite_records(ROOT)
    assert len(records) == 5
    assert {row["record_id"] for row in records} == harness.EXPECTED_RECORDS


def test_ode_spec_ids_present():
    harness = load_harness()
    spec = harness.build_spec_payload()
    ids = {row["spec_id"] for row in spec["ode_certificate_specs"]}
    assert harness.REQUIRED_SPEC_IDS <= ids
    for row in spec["ode_certificate_specs"]:
        assert row["zero_mathlib_dependency"] is True
        assert row["public_ready"] is False
        assert row["upload_allowed"] is False
        assert row["release_ready"] is False
        assert row["mathlib_dependency"] is False


def test_symbolic_fixtures_satisfy_bounded_odes():
    harness = load_harness()
    assert harness.exp_ode_check()["passed"] is True
    assert harness.sin_ode_check()["passed"] is True
    assert harness.cos_ode_check()["passed"] is True
    polynomial = harness.polynomial_derivative_check()
    assert polynomial["passed"] is True
    assert polynomial["derivative_table"]["D4(p)"] == "0"


def test_bessel_stub_is_recognized_without_overclaim():
    harness = load_harness()
    records = {row["record_id"]: row for row in harness.load_dfinite_records(ROOT)}
    result = harness.recognize_bessel_stub(records["dfinite_bessel_style_certificate_stub_v0"])
    assert result["passed"] is True
    assert result["status"] == "PASS_STUB_RECOGNIZED"
    assert result["executed_solution_check"] is False


def test_build_all_generates_artifacts_and_guardrails(tmp_path):
    harness = load_harness()
    execution, roundtrip, spec = harness.build_all(ROOT, tmp_path)
    assert execution["record_count"] == 5
    assert execution["failed"] == 0
    assert execution["zero_mathlib_status"] == "PASS"
    assert all(value is True for value in execution["guardrails"].values())
    assert roundtrip["record_count"] == 5
    assert roundtrip["failed"] == 0
    assert roundtrip["zero_mathlib_status"] == "PASS"
    assert spec["spec_count"] >= 7
    artifacts = sorted((tmp_path / "eml").glob("*.eml"))
    assert len(artifacts) == 5
    for path in artifacts:
        text = path.read_text(encoding="utf-8")
        assert "import " + "Mathlib" not in text
        assert "from " + "Mathlib" not in text
        assert "Mathlib" + "." not in text
    allowed_warnings = {"WARN_STUB_NOT_EXECUTED", "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT", "WARN_NO_DIRECT_FORGE_COMPILE"}
    for row in execution["results"]:
        if row.get("warning"):
            assert row["warning"] in allowed_warnings
    for row in roundtrip["results"]:
        if row["status"] == "WARN":
            assert row["forge_code"] in allowed_warnings or roundtrip["efrog_status"] == "WARN"


def test_no_forbidden_true_booleans():
    harness = load_harness()
    for record in harness.load_dfinite_records(ROOT):
        assert record["public_ready"] is False
        assert record["upload_allowed"] is False
        assert record["release_ready"] is False
        assert record["mathlib_dependency"] is False
        assert record["forge_compiler_change_required"] is False
        assert record["hardware_required"] is False
