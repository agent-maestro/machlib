from pathlib import Path

from tools.capcard_lab.candidate_factory import generate_candidates
from tools.capcard_lab.evidence_scorer import score
from tools.capcard_lab.marketplace_ranker import SEGMENTS, rank


def test_segments_count():
    assert len(SEGMENTS) >= 8


def test_rank_outputs_top_candidate(tmp_path):
    cards = tmp_path / "cards"
    generate_candidates(Path("."), cards)
    scores = tmp_path / "scores.json"
    ranking = tmp_path / "ranking.json"
    score(cards, scores, Path("."))
    data = rank(scores, ranking, Path("."))
    assert data["ranked_candidates"]
    assert data["top_candidate"]


def test_rank_no_upload_actions(tmp_path):
    cards = tmp_path / "cards"
    generate_candidates(Path("."), cards)
    scores = tmp_path / "scores.json"
    ranking = tmp_path / "ranking.json"
    score(cards, scores, Path("."))
    data = rank(scores, ranking, Path("."))
    assert data["production_marketplace_modified"] is False
    assert data["petal_api_upload_performed"] is False
