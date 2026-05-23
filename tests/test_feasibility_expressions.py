import math

import pytest

from tools.feasibility_algebra.expressions import ComplexityExpression, factorial_estimate, safe_power
from tools.feasibility_algebra.stress_families import stress_families


@pytest.mark.parametrize(
    "expr_id,n,expected",
    [
        ("linear_n", 10, 10),
        ("quadratic_n2", 10, 100),
        ("cubic_n3", 10, 1000),
        ("polynomial_n10", 2, 1024),
        ("polynomial_n100", 1, 1),
        ("polynomial_n1000", 1, 1),
        ("exponential_2n", 10, 1024),
        ("subexponential_2sqrt_n", 16, 16),
        ("logspace_style", 16, 4),
    ],
)
def test_expression_evaluates_expected_family(expr_id, n, expected):
    expr = {item.expression_id: item for item in stress_families()}[expr_id]
    assert expr.evaluate(n) == pytest.approx(expected)


def test_factorial_estimate_small_value():
    assert factorial_estimate(5) == 120


def test_factorial_estimate_saturates_large_value():
    assert math.isfinite(factorial_estimate(500))


def test_safe_power_saturates_large_value():
    assert safe_power(10, 1000) == pytest.approx(1e308)


def test_negative_n_rejected():
    expr = ComplexityExpression("x", "polynomial", "n", {"exponent": 1}, "O(n)", "test")
    with pytest.raises(ValueError):
        expr.evaluate(-1)


def test_unknown_kind_rejected():
    expr = ComplexityExpression("x", "unknown", "?", {}, "custom", "test")
    with pytest.raises(ValueError):
        expr.evaluate(1)


@pytest.mark.parametrize("expr", stress_families(), ids=lambda item: item.expression_id)
def test_all_stress_families_evaluate_at_n_two(expr):
    assert expr.evaluate(2) > 0


@pytest.mark.parametrize("expr", stress_families(), ids=lambda item: item.expression_id)
def test_all_stress_families_have_false_safe_serializable_fields(expr):
    row = expr.to_dict()
    assert row["expression_id"]
    assert row["asymptotic_label"]
    assert row["practical_notes"]
