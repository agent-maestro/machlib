from __future__ import annotations

from dataclasses import dataclass

from .bands import FeasibilityBand, band_for_ratio, worse_band
from .expressions import ComplexityExpression
from .resources import ResourceProfile


@dataclass(frozen=True)
class FeasibilityResult:
    expression_id: str
    n: int
    operation_estimate: float
    memory_estimate: float
    budget_profile: str
    feasibility_band: FeasibilityBand
    reason: str
    public_claim: bool = False
    theorem_proof_claim: bool = False

    def to_dict(self) -> dict[str, object]:
        return {
            "expression_id": self.expression_id,
            "n": self.n,
            "operation_estimate": self.operation_estimate,
            "memory_estimate": self.memory_estimate,
            "budget_profile": self.budget_profile,
            "feasibility_band": self.feasibility_band.value,
            "reason": self.reason,
            "public_claim": self.public_claim,
            "theorem_proof_claim": self.theorem_proof_claim,
        }


def evaluate_expression(
    expression: ComplexityExpression,
    n: int,
    profile: ResourceProfile,
) -> FeasibilityResult:
    operations = expression.evaluate(n)
    memory = expression.memory_estimate(n)
    op_ratio = operations / max(profile.operation_budget, 1)
    memory_ratio = memory / max(profile.memory_budget_bytes, 1)
    band = worse_band(band_for_ratio(op_ratio), band_for_ratio(memory_ratio))
    reason = (
        f"{expression.expression} at n={n} uses about {operations:.3e} operations "
        f"and {memory:.3e} bytes against {profile.profile_id}."
    )
    return FeasibilityResult(
        expression_id=expression.expression_id,
        n=n,
        operation_estimate=operations,
        memory_estimate=memory,
        budget_profile=profile.profile_id,
        feasibility_band=band,
        reason=reason,
    )
