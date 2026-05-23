import pytest

from tools.feasibility_algebra.bands import FeasibilityBand
from tools.feasibility_algebra.capcard_bridge import capcard_readiness_from_band, score_candidate


@pytest.mark.parametrize(
    "band,expected",
    [
        (FeasibilityBand.TRIVIAL, "READY_INTERNAL"),
        (FeasibilityBand.PRACTICAL, "READY_INTERNAL"),
        (FeasibilityBand.BORDERLINE, "REVIEW_REQUIRED"),
        (FeasibilityBand.ABSURD, "INTERNAL_ONLY_BLOCKED"),
        (FeasibilityBand.BLOCKED, "BLOCKED"),
    ],
)
def test_capcard_readiness_from_band(band, expected):
    assert capcard_readiness_from_band(band) == expected


def test_score_candidate_returns_int_score():
    score = score_candidate(5, "PRACTICAL")
    assert isinstance(score["overall_trust_score_0_to_100"], int)


def test_absurd_score_lower_than_practical():
    practical = score_candidate(5, "PRACTICAL")["overall_trust_score_0_to_100"]
    absurd = score_candidate(5, "ABSURD")["overall_trust_score_0_to_100"]
    assert practical > absurd
