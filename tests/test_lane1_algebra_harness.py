from pathlib import Path

import pytest

from tools import run_lane1_algebra_harness as harness


ROOT = Path("corpus/eml_lanes_draft")


@pytest.fixture(scope="module")
def result():
    return harness.execute(ROOT)


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_lane1_seed_count(result):
    assert result["seed_count"] == 4
    assert not result["missing_records"]
    assert not result["unexpected_records"]


def test_cubic_dyadic_passes_and_rejects_non_roots(result):
    cubic = row(result, "cubic_dyadic_equilibrium_v0")
    assert cubic["status"] == "PASS"
    assert cubic["classification"] == "CONSTRAINT"
    checks = {item["sample"]: item["constraint_holds"] for item in cubic["checks"]}
    assert checks["zero"] is True
    assert checks["sqrt2"] is True
    assert checks["negative_sqrt2"] is True
    assert checks["one"] is False
    assert checks["two"] is False


def test_linear_dyadic_identity_samples_pass(result):
    linear = row(result, "linear_dyadic_identity_v0")
    assert linear["status"] == "PASS"
    assert linear["classification"] == "IDENTITY"
    assert all(item["identity_holds"] for item in linear["checks"])


def test_quadratic_zero_product_samples_pass(result):
    quadratic = row(result, "quadratic_zero_product_v0")
    assert quadratic["status"] == "PASS"
    checks = {item["sample"]["x"]: item["constraint_holds"] for item in quadratic["checks"]}
    assert checks[-1] is True
    assert checks[1] is True
    assert checks[0] is False
    assert checks[2] is False


def test_inequality_samples_pass(result):
    inequality = row(result, "inequality_sign_flip_v0")
    assert inequality["status"] == "PASS"
    assert inequality["classification"] == "BOUNDED_SYMBOLIC_RULE"
    positive = [item for item in inequality["checks"] if item.get("rule_applied") is not False]
    assert all(item["premise"] and item["conclusion"] for item in positive)
    negative = [item for item in inequality["checks"] if item.get("rule_applied") is False]
    assert negative and negative[0]["premise"] is False


def test_output_guardrails(result):
    assert result["guardrails"]["no_mathlib_dependency"] is True
    assert result["guardrails"]["no_hf_upload"] is True
    assert result["guardrails"]["no_petal_upload"] is True
    assert result["guardrails"]["no_package_publish"] is True
    assert result["guardrails"]["no_hardware"] is True
    assert result["guardrails"]["no_forge_compiler_change"] is True
    assert result["guardrails"]["no_public_theorem_claim"] is True


def test_no_lane1_seed_has_forbidden_true_flags():
    seeds = harness.load_lane1_seeds(ROOT)
    for seed in seeds.values():
        draft = seed.draft
        assert draft["public_ready"] is False
        assert draft["upload_allowed"] is False
        assert draft["mathlib_dependency"] is False
