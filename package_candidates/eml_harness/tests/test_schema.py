from eml_harness.schema import validate_result


def test_validate_result_accepts_pass():
    assert validate_result({"record_id": "r1", "status": "PASS"}) == []


def test_validate_result_rejects_unknown_status():
    errors = validate_result({"record_id": "r1", "status": "MAYBE"})
    assert errors == ["invalid status: MAYBE"]
