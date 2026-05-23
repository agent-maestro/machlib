from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any


MAX_ESTIMATE = 1e308


@dataclass(frozen=True)
class ComplexityExpression:
    expression_id: str
    kind: str
    expression: str
    params: dict[str, Any]
    asymptotic_label: str
    practical_notes: str
    memory_kind: str = "linear"

    def evaluate(self, n: int | float) -> float:
        if n < 0:
            raise ValueError("n must be non-negative")
        if self.kind == "polynomial":
            exponent = float(self.params.get("exponent", 1))
            factor = float(self.params.get("factor", 1))
            return safe_power(n, exponent, factor)
        if self.kind == "n_log_n":
            factor = float(self.params.get("factor", 1))
            return factor * max(1.0, float(n)) * math.log2(max(2.0, float(n)))
        if self.kind == "exponential":
            base = float(self.params.get("base", 2))
            exponent_factor = float(self.params.get("exponent_factor", 1))
            return safe_power(base, exponent_factor * float(n), 1)
        if self.kind == "subexponential":
            base = float(self.params.get("base", 2))
            return safe_power(base, math.sqrt(float(n)), 1)
        if self.kind == "factorial":
            return factorial_estimate(int(n))
        if self.kind == "logspace":
            return math.log2(max(2.0, float(n)))
        if self.kind == "pseudo_polynomial":
            value_bound = float(self.params.get("value_bound", 10_000))
            return float(n) * value_bound
        if self.kind == "fixed_parameter":
            k = float(self.params.get("k", 4))
            return safe_power(2, k, 1) * float(n)
        if self.kind == "constant_huge":
            return float(self.params.get("constant", 1e18))
        if self.kind == "mixed":
            return safe_power(n, float(self.params.get("exponent", 2)), 1) + safe_power(2, math.sqrt(float(n)), 1)
        raise ValueError(f"unsupported expression kind: {self.kind}")

    def memory_estimate(self, n: int | float) -> float:
        if self.memory_kind == "constant":
            return 1024
        if self.memory_kind == "log":
            return 1024 * math.log2(max(2.0, float(n)))
        if self.memory_kind == "quadratic":
            return safe_power(n, 2, 8)
        if self.memory_kind == "exponential":
            return safe_power(2, float(n), 8)
        return max(1024.0, 8.0 * float(n))

    def to_dict(self) -> dict[str, Any]:
        return {
            "expression_id": self.expression_id,
            "kind": self.kind,
            "expression": self.expression,
            "params": self.params,
            "asymptotic_label": self.asymptotic_label,
            "practical_notes": self.practical_notes,
            "memory_kind": self.memory_kind,
        }


def safe_power(base: float | int, exponent: float, factor: float = 1.0) -> float:
    if base == 0:
        return 0.0
    if factor == 0:
        return 0.0
    try:
        log10_value = math.log10(abs(float(base))) * exponent + math.log10(abs(factor))
    except ValueError:
        return MAX_ESTIMATE
    if log10_value > 308:
        return MAX_ESTIMATE
    return min(MAX_ESTIMATE, factor * (float(base) ** exponent))


def factorial_estimate(n: int) -> float:
    if n <= 1:
        return 1.0
    log10_value = math.lgamma(n + 1) / math.log(10)
    if log10_value > 308:
        return MAX_ESTIMATE
    return float(math.factorial(n))
