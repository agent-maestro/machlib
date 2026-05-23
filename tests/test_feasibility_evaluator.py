import pytest

from tools.feasibility_algebra.evaluator import evaluate_expression
from tools.feasibility_algebra.resources import default_resource_profiles
from tools.feasibility_algebra.stress_families import stress_families


@pytest.mark.parametrize("n", [2, 5, 10, 20, 50, 100])
def test_n1000_absurd_or_infeasible_on_browser(n):
    expr = {item.expression_id: item for item in stress_families()}["polynomial_n1000"]
    profile = {item.profile_id: item for item in default_resource_profiles()}["browser_interactive_budget"]
    result = evaluate_expression(expr, n, profile)
    assert result.feasibility_band.value in {"INFEASIBLE", "ABSURD"}
    assert result.public_claim is False
    assert result.theorem_proof_claim is False


@pytest.mark.parametrize("expr_id", ["linear_n", "n_log_n", "quadratic_n2", "cubic_n3"])
def test_small_n_practical_for_workstation(expr_id):
    expr = {item.expression_id: item for item in stress_families()}[expr_id]
    profile = {item.profile_id: item for item in default_resource_profiles()}["workstation"]
    result = evaluate_expression(expr, 10, profile)
    assert result.operation_estimate > 0
    assert result.memory_estimate > 0


def test_memory_quadratic_can_block_memory_budget():
    expr = {item.expression_id: item for item in stress_families()}["memory_quadratic"]
    profile = {item.profile_id: item for item in default_resource_profiles()}["silicon_toy_budget"]
    result = evaluate_expression(expr, 1000, profile)
    assert result.feasibility_band.value in {"INFEASIBLE", "ABSURD"}


def test_result_to_dict_contains_required_false_claims():
    expr = stress_families()[0]
    profile = default_resource_profiles()[0]
    row = evaluate_expression(expr, 1, profile).to_dict()
    assert row["public_claim"] is False
    assert row["theorem_proof_claim"] is False


@pytest.mark.parametrize("profile", default_resource_profiles(), ids=lambda item: item.profile_id)
def test_n1000_at_n10_not_practical_for_any_profile(profile):
    expr = {item.expression_id: item for item in stress_families()}["polynomial_n1000"]
    result = evaluate_expression(expr, 10, profile)
    assert result.feasibility_band.value == "ABSURD"


@pytest.mark.parametrize("profile", default_resource_profiles(), ids=lambda item: item.profile_id)
def test_linear_n_small_has_reason_for_each_profile(profile):
    expr = {item.expression_id: item for item in stress_families()}["linear_n"]
    result = evaluate_expression(expr, 100, profile)
    assert "n=100" in result.reason
