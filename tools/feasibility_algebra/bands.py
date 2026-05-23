from __future__ import annotations

from enum import StrEnum


class FeasibilityBand(StrEnum):
    TRIVIAL = "TRIVIAL"
    PRACTICAL = "PRACTICAL"
    HEAVY_BUT_POSSIBLE = "HEAVY_BUT_POSSIBLE"
    BORDERLINE = "BORDERLINE"
    INFEASIBLE = "INFEASIBLE"
    ABSURD = "ABSURD"
    SYMBOLIC_ONLY = "SYMBOLIC_ONLY"
    BLOCKED = "BLOCKED"


def band_for_ratio(ratio: float, *, symbolic_only: bool = False) -> FeasibilityBand:
    if symbolic_only:
        return FeasibilityBand.SYMBOLIC_ONLY
    if ratio <= 1e-6:
        return FeasibilityBand.TRIVIAL
    if ratio <= 1e-2:
        return FeasibilityBand.PRACTICAL
    if ratio <= 0.35:
        return FeasibilityBand.HEAVY_BUT_POSSIBLE
    if ratio <= 1:
        return FeasibilityBand.BORDERLINE
    if ratio <= 1e12:
        return FeasibilityBand.INFEASIBLE
    return FeasibilityBand.ABSURD


def worse_band(left: FeasibilityBand, right: FeasibilityBand) -> FeasibilityBand:
    order = list(FeasibilityBand)
    return left if order.index(left) >= order.index(right) else right
