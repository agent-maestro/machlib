from tools.feasibility_algebra.bands import FeasibilityBand
from tools.feasibility_algebra.semiring import (
    block_forbidden_claim,
    combine_alternative,
    combine_parallel,
    combine_sequential,
    degrade_stale,
    element,
)


def test_element_default_band_from_cost():
    assert element(1).band == FeasibilityBand.TRIVIAL


def test_sequential_adds_costs():
    result = combine_sequential(element(10), element(20))
    assert result.cost == 30


def test_sequential_keeps_worse_band():
    result = combine_sequential(element(1, band=FeasibilityBand.PRACTICAL), element(1, band=FeasibilityBand.ABSURD))
    assert result.band == FeasibilityBand.ABSURD


def test_alternative_picks_lower_cost():
    assert combine_alternative(element(100), element(1)).cost == 1


def test_parallel_sums_memory():
    result = combine_parallel(element(1, memory=5), element(1, memory=7))
    assert result.memory == 12


def test_degrade_stale_increases_penalty():
    assert degrade_stale(element(1)).freshness_penalty > 0


def test_block_forbidden_claim_sets_blocked_band():
    result = block_forbidden_claim(element(1))
    assert result.band == FeasibilityBand.BLOCKED
    assert result.claim_risk == 1.0
