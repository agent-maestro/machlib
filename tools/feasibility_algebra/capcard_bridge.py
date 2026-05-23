from __future__ import annotations

from .bands import FeasibilityBand


def capcard_readiness_from_band(band: FeasibilityBand) -> str:
    if band in {FeasibilityBand.TRIVIAL, FeasibilityBand.PRACTICAL}:
        return "READY_INTERNAL"
    if band in {FeasibilityBand.HEAVY_BUT_POSSIBLE, FeasibilityBand.BORDERLINE}:
        return "REVIEW_REQUIRED"
    if band in {FeasibilityBand.SYMBOLIC_ONLY, FeasibilityBand.INFEASIBLE, FeasibilityBand.ABSURD}:
        return "INTERNAL_ONLY_BLOCKED"
    return "BLOCKED"


def score_candidate(evidence_count: int, worst_band: str, mutation_resistance: float = 0.85) -> dict[str, object]:
    band_penalty = {
        "TRIVIAL": 0,
        "PRACTICAL": 5,
        "HEAVY_BUT_POSSIBLE": 15,
        "BORDERLINE": 30,
        "INFEASIBLE": 55,
        "ABSURD": 70,
        "SYMBOLIC_ONLY": 45,
        "BLOCKED": 90,
    }.get(worst_band, 50)
    score = max(0, min(100, int(35 + evidence_count * 4 + mutation_resistance * 30 - band_penalty)))
    return {"overall_trust_score_0_to_100": score, "readiness": capcard_readiness_from_band(FeasibilityBand(worst_band))}
