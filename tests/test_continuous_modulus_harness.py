import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_function_classes_draft")
TOOL = Path("tools/run_continuous_modulus_harness.py")


def load_harness():
    spec = importlib.util.spec_from_file_location("run_continuous_modulus_harness", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_loads_four_continuous_records():
    harness = load_harness()
    records = harness.load_continuous_records(ROOT)
    assert len(records) == 4
    assert {row["record_id"] for row in records} == harness.EXPECTED_RECORDS


def test_modulus_spec_ids_present():
    harness = load_harness()
    spec = harness.build_spec_payload()
    ids = {row["spec_id"] for row in spec["modulus_specs"]}
    assert harness.REQUIRED_SPEC_IDS <= ids
    for row in spec["modulus_specs"]:
        assert row["zero_mathlib_dependency"] is True
        assert row["public_ready"] is False
        assert row["upload_allowed"] is False
        assert row["release_ready"] is False
        assert row["mathlib_dependency"] is False


def test_bounded_continuity_patterns():
    harness = load_harness()
    linear = harness.linear_epsilon_delta_check()
    assert linear["passed"] is True
    assert all(row["passed"] for row in linear["sample_checks"])
    polynomial = harness.polynomial_local_modulus_check()
    assert polynomial["passed"] is True
    assert all(row["inside_interval"] for row in polynomial["sample_checks"])
    absolute = harness.absolute_value_lipschitz_check()
    assert absolute["passed"] is True
    assert all(row["lhs"] <= row["rhs"] for row in absolute["sample_checks"])
    step = harness.step_function_discontinuity_check()
    assert step["passed"] is True
    assert all(row["gap"] > row["epsilon"] for row in step["witness_checks"])


def test_records_carry_non_overclaim_boundaries():
    harness = load_harness()
    records = harness.load_continuous_records(ROOT)
    for record in records:
        text = str(record).lower()
        assert "topology formalization" in text
        assert "public proof" in text or "theorem" in text
        assert record["status"] == "DRAFT_INTERNAL"


def test_build_all_generates_artifacts_and_guardrails(tmp_path):
    harness = load_harness()
    execution, roundtrip, spec = harness.build_all(ROOT, tmp_path)
    assert execution["record_count"] == 4
    assert execution["passed"] == 4
    assert execution["failed"] == 0
    assert execution["zero_mathlib_status"] == "PASS"
    assert execution["guardrails"]["no_topology_formalization_claim"] is True
    assert all(value is True for value in execution["guardrails"].values())
    assert roundtrip["record_count"] == 4
    assert roundtrip["failed"] == 0
    assert roundtrip["zero_mathlib_status"] == "PASS"
    assert roundtrip["guardrails"]["no_topology_formalization_claim"] is True
    assert spec["spec_count"] >= 7
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
    for record in harness.load_continuous_records(ROOT):
        assert record["public_ready"] is False
        assert record["upload_allowed"] is False
        assert record["release_ready"] is False
        assert record["mathlib_dependency"] is False
        assert record["forge_compiler_change_required"] is False
        assert record["hardware_required"] is False
