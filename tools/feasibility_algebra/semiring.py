from __future__ import annotations

from dataclasses import dataclass, replace

from .bands import FeasibilityBand, band_for_ratio, worse_band


@dataclass(frozen=True)
class FeasibilityElement:
    cost: float
    memory: float
    evidence_risk: float
    claim_risk: float
    freshness_penalty: float
    human_review_cost: float
    band: FeasibilityBand
    evidence: tuple[str, ...] = ()

    def to_dict(self) -> dict[str, object]:
        return {
            "cost": self.cost,
            "memory": self.memory,
            "evidence_risk": self.evidence_risk,
            "claim_risk": self.claim_risk,
            "freshness_penalty": self.freshness_penalty,
            "human_review_cost": self.human_review_cost,
            "band": self.band.value,
            "evidence": list(self.evidence),
        }


def element(cost: float, memory: float = 0, band: FeasibilityBand | None = None) -> FeasibilityElement:
    return FeasibilityElement(cost, memory, 0, 0, 0, 0, band or band_for_ratio(cost / 1e9))


def combine_sequential(left: FeasibilityElement, right: FeasibilityElement) -> FeasibilityElement:
    return FeasibilityElement(
        cost=left.cost + right.cost,
        memory=max(left.memory, right.memory),
        evidence_risk=max(left.evidence_risk, right.evidence_risk),
        claim_risk=max(left.claim_risk, right.claim_risk),
        freshness_penalty=left.freshness_penalty + right.freshness_penalty,
        human_review_cost=left.human_review_cost + right.human_review_cost,
        band=worse_band(left.band, right.band),
        evidence=left.evidence + right.evidence,
    )


def combine_alternative(left: FeasibilityElement, right: FeasibilityElement) -> FeasibilityElement:
    return left if (left.cost + left.claim_risk) <= (right.cost + right.claim_risk) else right


def combine_parallel(left: FeasibilityElement, right: FeasibilityElement) -> FeasibilityElement:
    return FeasibilityElement(
        cost=max(left.cost, right.cost),
        memory=left.memory + right.memory,
        evidence_risk=max(left.evidence_risk, right.evidence_risk),
        claim_risk=max(left.claim_risk, right.claim_risk),
        freshness_penalty=max(left.freshness_penalty, right.freshness_penalty),
        human_review_cost=left.human_review_cost + right.human_review_cost,
        band=worse_band(left.band, right.band),
        evidence=left.evidence + right.evidence,
    )


def degrade_stale(value: FeasibilityElement, penalty: float = 0.2) -> FeasibilityElement:
    return replace(value, freshness_penalty=value.freshness_penalty + penalty)


def block_forbidden_claim(value: FeasibilityElement) -> FeasibilityElement:
    return replace(value, claim_risk=1.0, band=FeasibilityBand.BLOCKED)
