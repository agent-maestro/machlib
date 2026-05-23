from __future__ import annotations

from .expressions import ComplexityExpression


def stress_families() -> list[ComplexityExpression]:
    return [
        ComplexityExpression("linear_n", "polynomial", "n", {"exponent": 1}, "O(n)", "Usually feasible until IO dominates."),
        ComplexityExpression("n_log_n", "n_log_n", "n log n", {}, "O(n log n)", "Often practical for sorting/indexing scale."),
        ComplexityExpression("quadratic_n2", "polynomial", "n^2", {"exponent": 2}, "O(n^2)", "Feasible only to moderate n."),
        ComplexityExpression("cubic_n3", "polynomial", "n^3", {"exponent": 3}, "O(n^3)", "Quickly heavy but common in bounded linear algebra."),
        ComplexityExpression("polynomial_n10", "polynomial", "n^10", {"exponent": 10}, "O(n^10)", "Formally polynomial but operationally severe."),
        ComplexityExpression("polynomial_n100", "polynomial", "n^100", {"exponent": 100}, "O(n^100)", "Polynomial label hides extreme infeasibility."),
        ComplexityExpression("polynomial_n1000", "polynomial", "n^1000", {"exponent": 1000}, "O(n^1000)", "Central adversarial polynomial-feasibility gap."),
        ComplexityExpression("exponential_2n", "exponential", "2^n", {"base": 2}, "O(2^n)", "Classic exponential blowup."),
        ComplexityExpression("subexponential_2sqrt_n", "subexponential", "2^sqrt(n)", {"base": 2}, "O(2^sqrt(n))", "Can beat high-degree polynomial for many n."),
        ComplexityExpression("factorial_n", "factorial", "n!", {}, "O(n!)", "Symbolic only beyond small n."),
        ComplexityExpression("logspace_style", "logspace", "log n", {}, "O(log n)", "Tiny operations and memory in this toy model.", "log"),
        ComplexityExpression("pseudo_polynomial", "pseudo_polynomial", "n * V", {"value_bound": 1000000}, "pseudo-polynomial", "Feasible depends on numeric value bound."),
        ComplexityExpression("fixed_parameter_like", "fixed_parameter", "2^k * n", {"k": 20}, "FPT-like", "Can be practical when k is small; huge when k grows."),
        ComplexityExpression("constant_but_huge_hidden_factor", "constant_huge", "10^18", {"constant": 1e18}, "O(1)", "Constant-time label can still be impossible."),
        ComplexityExpression("memory_quadratic", "polynomial", "n^2 memory", {"exponent": 2}, "O(n^2)", "Memory, not operations, becomes the blocker.", "quadratic"),
        ComplexityExpression("io_bound_scan", "polynomial", "n scan", {"exponent": 1, "factor": 100}, "O(n)", "Linear but bounded by bandwidth and latency."),
        ComplexityExpression("verifier_linear_solver_huge", "polynomial", "10^9 * n", {"exponent": 1, "factor": 1e9}, "O(n)", "Linear verifier with a huge hidden factor."),
        ComplexityExpression("proof_search_branching", "exponential", "3^n", {"base": 3}, "O(3^n)", "Branching proof search explodes early."),
    ]


def stress_family_rows() -> list[dict[str, object]]:
    rows = []
    for expr in stress_families():
        rows.append({
            **expr.to_dict(),
            "asymptotic_class": expr.asymptotic_label,
            "why_interesting": expr.practical_notes,
            "expected_feasibility_behavior": "Evaluated against bounded resource profiles, not just asymptotic labels.",
            "examples": ["internal toy workload", "CapCard review budget", "Senses visualization budget"],
            "not_claimed": [
                "not a theorem proof",
                "not a new complexity class",
                "not certified safety",
                "not production controller evidence",
            ],
        })
    return rows
