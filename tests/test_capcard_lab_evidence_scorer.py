from pathlib import Path

import pytest

from tools.capcard_lab.candidate_factory import generate_candidates, make_card
from tools.capcard_lab.evidence_scorer import score, score_card
from tools.capcard_lab.schema import REQUIRED_CANDIDATES


@pytest.mark.parametrize("cid", REQUIRED_CANDIDATES)
def test_score_card_range(cid):
    row = score_card(make_card(cid))
    assert 0 <= row["overall_trust_score_0_to_100"] <= 100


def test_eml_scores_above_qwen():
    eml = score_card(make_card("eml_puzzle_evidence_kernel"))
    qwen = score_card(make_card("qwen_puzzle_curriculum_pack"))
    assert eml["overall_trust_score_0_to_100"] > qwen["overall_trust_score_0_to_100"]


def test_score_outputs_all_candidates(tmp_path):
    cards = tmp_path / "cards"
    generate_candidates(Path("."), cards)
    out = tmp_path / "scores.json"
    data = score(cards, out, Path("."))
    assert data["candidate_count"] >= 15
    assert out.exists()
