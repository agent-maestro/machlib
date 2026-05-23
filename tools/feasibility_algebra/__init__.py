"""Internal Monogate feasibility algebra stress lab.

This package is local research tooling. It provides executable cost-model
checks for distinguishing asymptotic labels from practical resource feasibility.
It does not claim a theorem, a proof, or certified completeness.
"""

from .bands import FeasibilityBand, band_for_ratio
from .evaluator import FeasibilityResult, evaluate_expression
from .expressions import ComplexityExpression
from .resources import ResourceProfile, default_resource_profiles

__all__ = [
    "ComplexityExpression",
    "FeasibilityBand",
    "FeasibilityResult",
    "ResourceProfile",
    "band_for_ratio",
    "default_resource_profiles",
    "evaluate_expression",
]
