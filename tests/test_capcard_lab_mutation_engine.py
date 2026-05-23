from pathlib import Path

import pytest

from tools.capcard_lab.candidate_factory import generate_candidates, make_card
from tools.capcard_lab.mutation_engine import MUTATION_FAMILIES, apply_mutation, mutate


@pytest.mark.parametrize("family", MUTATION_FAMILIES)
def test_mutation_has_family(family):
    row = apply_mutation(make_card("eml_puzzle_evidence_kernel"), family, 1)
    assert row["mutation_family"] == family
    assert row["fixture_only"] is True


def test_mutation_generation_count(tmp_path):
    cards = tmp_path / "cards"
    muts = tmp_path / "muts"
    generate_candidates(Path("."), cards)
    data = mutate(cards, muts, 40, Path("."))
    assert data["mutation_count"] == 40
    assert len(list(muts.glob("*.json"))) == 40


def test_negative_boundary_mutation_expected_pass():
    row = apply_mutation(make_card("eml_puzzle_evidence_kernel"), "negative_boundary_only_safe_mutation", 1)
    assert "not theorem proved" in row["marketplace_copy"]


def test_token_fixture_marked_fixture_only():
    row = apply_mutation(make_card("eml_puzzle_evidence_kernel"), "token_like_secret_fixture", 1)
    assert row["fixture_only"] is True
