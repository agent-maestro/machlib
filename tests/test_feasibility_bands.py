import pytest

from tools.feasibility_algebra.bands import FeasibilityBand, band_for_ratio, worse_band


@pytest.mark.parametrize(
    "ratio,band",
    [
        (0, FeasibilityBand.TRIVIAL),
        (1e-8, FeasibilityBand.TRIVIAL),
        (1e-3, FeasibilityBand.PRACTICAL),
        (0.1, FeasibilityBand.HEAVY_BUT_POSSIBLE),
        (0.8, FeasibilityBand.BORDERLINE),
        (10, FeasibilityBand.INFEASIBLE),
        (1e20, FeasibilityBand.ABSURD),
    ],
)
def test_band_for_ratio_thresholds(ratio, band):
    assert band_for_ratio(ratio) == band


def test_symbolic_only_override():
    assert band_for_ratio(0, symbolic_only=True) == FeasibilityBand.SYMBOLIC_ONLY


def test_worse_band_picks_more_severe():
    assert worse_band(FeasibilityBand.PRACTICAL, FeasibilityBand.ABSURD) == FeasibilityBand.ABSURD
