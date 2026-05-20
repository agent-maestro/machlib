import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_function_classes_draft")
TOOL = Path("tools/validate_function_class_records.py")


def load_validator():
    spec = importlib.util.spec_from_file_location("validate_function_class_records", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_function_class_validator_passes():
    validator = load_validator()
    result = validator.build_result(ROOT)
    assert result["record_count"] >= 20
    assert result["function_class_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert result["zero_mathlib_status"] == "PASS"
    assert result["guardrail_status"] == "PASS"
    assert result["failures"] == []


def test_category_minimums_and_payloads():
    validator = load_validator()
    records, failures = validator.collect_records(ROOT)
    assert failures == []
    counts = {}
    for row in records:
        counts[row["function_class"]] = counts.get(row["function_class"], 0) + 1
    assert counts["D_FINITE_CERTIFICATE"] >= 5
    assert counts["ANALYTIC_LOCAL_SERIES"] >= 4
    assert counts["SMOOTH_FINITE_JET"] >= 4
    assert counts["CONTINUITY_EPSILON_DELTA"] >= 4
    assert counts["CLASS_BOUNDARY_RELATION"] >= 3
    for row in records:
        payload = row["certificate_payload"]
        if row["function_class"] == "D_FINITE_CERTIFICATE":
            assert "ode" in payload or "polynomial_coefficients" in payload
        if row["function_class"] == "ANALYTIC_LOCAL_SERIES":
            assert "series_kind" in payload
            assert row["limitations"]
        if row["function_class"] == "SMOOTH_FINITE_JET":
            assert "derivative_payload" in payload
            assert row["limitations"]
        if row["function_class"] == "CONTINUITY_EPSILON_DELTA":
            assert "continuity_payload" in payload
            assert row["limitations"]
        if row["function_class"] == "CLASS_BOUNDARY_RELATION":
            assert payload["non_overclaim"] is True


def test_no_forbidden_true_booleans():
    validator = load_validator()
    records, _ = validator.collect_records(ROOT)
    for row in records:
        assert row["public_ready"] is False
        assert row["upload_allowed"] is False
        assert row["release_ready"] is False
        assert row["mathlib_dependency"] is False
        assert row["forge_compiler_change_required"] is False
        assert row["hardware_required"] is False
        assert row["status"] == "DRAFT_INTERNAL"
