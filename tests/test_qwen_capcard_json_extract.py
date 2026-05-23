from tools.qwen_capcard_lab.json_extract import REQUIRED_CAPCARD_FIELDS, extract_json_object, has_token_like_secret


SAFE = {
    "candidate_id": "x",
    "status": "BLOCKED_WITH_EXACT_FIX_LIST",
    "evidence_basis": [],
    "limitations": [],
    "not_claimed": [],
    "public_ready": False,
}


def as_json(extra=""):
    import json

    return json.dumps(SAFE | (extra or {}))


def test_extract_exact_json():
    result = extract_json_object(as_json(), REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "EXACT_JSON"


def test_extract_thinking_before_json():
    result = extract_json_object("Thinking...\n" + as_json(), REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "JSON_EXTRACTED_FROM_THINKING_TEXT"


def test_extract_thinking_after_json():
    result = extract_json_object(as_json() + "\nDone.", REQUIRED_CAPCARD_FIELDS)
    assert result.extracted_json["candidate_id"] == "x"


def test_extract_markdown_fence():
    result = extract_json_object("```json\n" + as_json() + "\n```", REQUIRED_CAPCARD_FIELDS)
    assert result.extracted_json["status"] == "BLOCKED_WITH_EXACT_FIX_LIST"


def test_extract_multiple_objects_first_valid():
    result = extract_json_object('{"bad": true}\n' + as_json(), REQUIRED_CAPCARD_FIELDS)
    assert result.extracted_json["candidate_id"] == "x"


def test_invalid_json():
    result = extract_json_object("{bad", REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "JSON_MISSING"


def test_no_json():
    result = extract_json_object("no object here", REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "JSON_MISSING"


def test_forbidden_true_field_rejected():
    result = extract_json_object(as_json({"public_ready": True}), REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "JSON_INVALID"


def test_token_like_secret_rejected():
    fake_secret = "sk-" + "abcdefghijklmnopqrstuvwxyz"
    result = extract_json_object('{"token":"' + fake_secret + '"}', None)
    assert result.extraction_status == "JSON_INVALID"


def test_token_detector():
    assert has_token_like_secret("hf_" + "abcdefghijklmnopqrstuvwxyz")


def test_missing_required_field_rejected():
    result = extract_json_object('{"candidate_id": "x"}', REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "JSON_INVALID"


def test_nested_object_balancing():
    raw = '{"candidate_id":"x","status":"BLOCKED_WITH_EXACT_FIX_LIST","evidence_basis":[{"a":1}],"limitations":[],"not_claimed":[]}'
    result = extract_json_object(raw, REQUIRED_CAPCARD_FIELDS)
    assert result.extraction_status == "EXACT_JSON"


def test_brace_inside_string():
    raw = '{"candidate_id":"x","status":"BLOCKED_WITH_EXACT_FIX_LIST","evidence_basis":["{not brace}"],"limitations":[],"not_claimed":[]}'
    assert extract_json_object(raw, REQUIRED_CAPCARD_FIELDS).extracted_json["candidate_id"] == "x"


def test_escaped_quote_inside_string():
    raw = '{"candidate_id":"x","status":"BLOCKED_WITH_EXACT_FIX_LIST","evidence_basis":["say \\"hi\\""],"limitations":[],"not_claimed":[]}'
    assert extract_json_object(raw, REQUIRED_CAPCARD_FIELDS).extracted_json["candidate_id"] == "x"


def test_empty_output_missing():
    assert extract_json_object("", REQUIRED_CAPCARD_FIELDS).extraction_status == "JSON_MISSING"
