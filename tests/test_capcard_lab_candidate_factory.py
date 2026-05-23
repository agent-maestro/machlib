from pathlib import Path

import pytest

from tools.capcard_lab.candidate_factory import generate_candidates, make_card
from tools.capcard_lab.schema import FALSE_ACTION_FIELDS, REQUIRED_CANDIDATES


@pytest.mark.parametrize("cid", REQUIRED_CANDIDATES)
def test_make_required_candidate(cid):
    card = make_card(cid)
    assert card["candidate_id"] == cid
    assert card["visibility"] == "internal"
    for field in FALSE_ACTION_FIELDS:
        assert card[field] is False


def test_generate_candidate_count(tmp_path):
    data = generate_candidates(Path("."), tmp_path)
    assert data["candidate_count"] >= 15
    assert len(list(tmp_path.glob("*.json"))) >= 15


def test_qwen_blocked():
    card = make_card("qwen_puzzle_curriculum_pack")
    assert card["readiness_band"] == "BLOCKED_REPAIR_REQUIRED"
    assert card["blockers"]


def test_eml_strong():
    card = make_card("eml_puzzle_evidence_kernel")
    assert card["readiness_band"] == "STRONG_INTERNAL"
