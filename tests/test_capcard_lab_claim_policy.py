import pytest

from tools.capcard_lab.claim_policy import validate_claims
from tools.capcard_lab.schema import FALSE_ACTION_FIELDS, NOT_CLAIMED, action_false_payload


def base_card():
    card = {
        "candidate_id": "x",
        "readiness_band": "READY_INTERNAL",
        "limitations": NOT_CLAIMED,
        "not_claimed": NOT_CLAIMED,
    }
    card.update(action_false_payload())
    return card


def test_valid_claim_card_passes():
    assert validate_claims(base_card()).status == "PASS"


@pytest.mark.parametrize("field", FALSE_ACTION_FIELDS)
def test_true_action_fields_fail(field):
    card = base_card()
    card[field] = True
    assert validate_claims(card).status == "FAIL"


@pytest.mark.parametrize(
    "phrase",
    ["theorem proved", "open problem solved", "certified safety", "production controller", "PETAL verified", "Hugging Face uploaded"],
)
def test_forbidden_positive_claims_fail(phrase):
    card = base_card()
    card["copy"] = phrase
    assert validate_claims(card).status == "FAIL"


def test_negative_boundary_allowed():
    card = base_card()
    card["copy"] = "not theorem proved and not certified safety"
    assert validate_claims(card).status == "PASS"
