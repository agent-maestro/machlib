from tools.capcard_lab.schema import FALSE_ACTION_FIELDS, REQUIRED_CANDIDATES, action_false_payload


def test_required_candidate_count():
    assert len(REQUIRED_CANDIDATES) >= 15


def test_false_action_fields_present():
    assert "petal_api_upload_performed" in FALSE_ACTION_FIELDS
    assert "huggingface_upload_performed" in FALSE_ACTION_FIELDS


def test_action_false_payload_is_false():
    payload = action_false_payload()
    for field in FALSE_ACTION_FIELDS:
        assert payload[field] is False


def test_internal_visibility_defaults():
    payload = action_false_payload()
    assert payload["safe_to_display_internally"] is True
    assert payload["safe_to_publish_publicly"] is False
