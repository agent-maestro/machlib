from tools.validate_capcard_reviewer_decision import validate_decision


def decision(**overrides):
    row = {
        "candidate_id": "eml",
        "reviewer_id": "r1",
        "reviewer_role": "internal_reviewer",
        "review_date": "2026-05-21",
        "review_decision": "approve_internal_display",
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }
    row.update(overrides)
    return row


def test_valid_approve_internal():
    assert validate_decision(decision()) == []


def test_valid_request_revision():
    assert validate_decision(decision(review_decision="request_revision")) == []


def test_valid_keep_blocked():
    assert validate_decision(decision(review_decision="keep_blocked")) == []


def test_valid_retire_candidate():
    assert validate_decision(decision(review_decision="retire_candidate")) == []


def test_missing_reviewer_id_fails():
    assert validate_decision(decision(reviewer_id=""))


def test_missing_role_fails():
    assert validate_decision(decision(reviewer_role=""))


def test_missing_date_fails():
    assert validate_decision(decision(review_date=""))


def test_approve_public_forbidden():
    assert validate_decision(decision(review_decision="approve_public_marketplace"))


def test_approve_petal_forbidden():
    assert validate_decision(decision(review_decision="approve_petal_upload"))


def test_approve_hf_forbidden():
    assert validate_decision(decision(review_decision="approve_hf_upload"))


def test_approve_certified_safety_forbidden():
    assert validate_decision(decision(review_decision="approve_certified_safety"))


def test_true_upload_field_fails():
    assert validate_decision(decision(petal_api_upload_performed=True))
