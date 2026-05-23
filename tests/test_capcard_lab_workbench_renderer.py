from pathlib import Path

from tools.capcard_lab.candidate_factory import generate_candidates
from tools.capcard_lab.evidence_scorer import score
from tools.capcard_lab.marketplace_ranker import rank
from tools.capcard_lab.workbench_renderer import render


def test_render_workbench(tmp_path):
    cards = tmp_path / "cards"
    generate_candidates(Path("."), cards)
    scores = tmp_path / "scores.json"
    ranking = tmp_path / "ranking.json"
    score(cards, scores, Path("."))
    rank(scores, ranking, Path("."))
    out = tmp_path / "workbench"
    manifest = render(cards, scores, ranking, out)
    assert manifest["candidate_count"] >= 15
    assert manifest["html_generated"] is True
    assert (out / "index.html").exists()


def test_workbench_boundary_fields(tmp_path):
    cards = tmp_path / "cards"
    generate_candidates(Path("."), cards)
    scores = tmp_path / "scores.json"
    ranking = tmp_path / "ranking.json"
    score(cards, scores, Path("."))
    rank(scores, ranking, Path("."))
    manifest = render(cards, scores, ranking, tmp_path / "workbench")
    assert manifest["deploy_performed"] is False
    assert manifest["public_claim"] is False
