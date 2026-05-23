import pytest

from tools.capcard_lab.reviewer_workflow import ALLOWED_DECISIONS, FORBIDDEN_DECISIONS, validate_decision


def decision(name):
    return {
        "reviewer_id": "r1",
        "reviewer_role": "human_reviewer",
        "review_date": "2026-05-21",
        "decision": name,
        "public_claim": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "production_marketplace_modified": False,
    }


@pytest.mark.parametrize("name", sorted(ALLOWED_DECISIONS))
def test_allowed_decisions(name):
    ok, errors = validate_decision(decision(name))
    assert ok, errors


@pytest.mark.parametrize("name", sorted(FORBIDDEN_DECISIONS))
def test_forbidden_decisions(name):
    ok, _ = validate_decision(decision(name))
    assert not ok


@pytest.mark.parametrize("field", ["reviewer_id", "reviewer_role", "review_date"])
def test_required_reviewer_fields(field):
    row = decision("request_revision")
    row[field] = ""
    ok, _ = validate_decision(row)
    assert not ok
