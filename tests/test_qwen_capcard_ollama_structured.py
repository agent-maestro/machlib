import json
from urllib import error

from tools.qwen_capcard_lab.json_extract import (
    REQUIRED_STRUCTURED_RESULT_FIELDS,
    extract_json_object,
    validate_structured_result,
)
from tools.qwen_capcard_lab.local_model import (
    CAPCARD_RESULT_SCHEMA,
    build_structured_prompt,
    call_ollama_json,
    call_ollama_structured_api,
    structured_schema_text,
)


SAFE = {
    "task_id": "task_x",
    "status": "WARN",
    "candidate_status": "BLOCKED_WITH_EXACT_FIX_LIST",
    "evidence_present": False,
    "missing_evidence": ["direct accepted repair evidence"],
    "forbidden_claims_present": False,
    "public_ready": False,
    "petal_api_upload_performed": False,
    "huggingface_upload_performed": False,
    "production_marketplace_modified": False,
    "theorem_proof_claim": False,
    "certified_safety_claim": False,
    "production_controller_claim": False,
    "explanation": "Evidence is missing.",
}


class FakeResponse:
    def __init__(self, payload):
        self.payload = payload

    def __enter__(self):
        return self

    def __exit__(self, *_args):
        return False

    def read(self):
        return self.payload.encode()


def api_payload(response):
    return json.dumps({"response": response, "done": True})


def test_schema_has_required_fields():
    assert CAPCARD_RESULT_SCHEMA["properties"]["task_id"]["type"] == "string"
    assert "candidate_status" in CAPCARD_RESULT_SCHEMA["required"]


def test_schema_text_is_json():
    assert json.loads(structured_schema_text())["type"] == "object"


def test_prompt_includes_schema_text():
    prompt = build_structured_prompt("Do task.", task_id="t1")
    assert '"candidate_status"' in prompt
    assert "Task id: t1" in prompt


def test_structured_json_exact_extracts():
    result = extract_json_object(json.dumps(SAFE), REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.extraction_status == "EXACT_JSON"


def test_structured_json_from_thinking_extracts():
    result = extract_json_object("thinking\n" + json.dumps(SAFE), REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.extracted_json["task_id"] == "task_x"


def test_structured_validation_passes_safe_shape():
    assert validate_structured_result(SAFE) == []


def test_structured_validation_rejects_public_ready_true():
    diagnostics = validate_structured_result(SAFE | {"public_ready": True})
    assert "forbidden_true_field:public_ready" in diagnostics


def test_structured_validation_rejects_bad_status():
    assert "invalid_status" in validate_structured_result(SAFE | {"status": "DONE"})


def test_structured_validation_rejects_bad_candidate_status():
    assert "invalid_candidate_status" in validate_structured_result(SAFE | {"candidate_status": "PUBLIC_READY"})


def test_structured_validation_requires_missing_evidence_list():
    assert "missing_evidence_must_be_list" in validate_structured_result(SAFE | {"missing_evidence": "x"})


def test_structured_validation_rejects_forbidden_claims_present_true():
    diagnostics = validate_structured_result(SAFE | {"forbidden_claims_present": True})
    assert "forbidden_claims_present_must_be_false" in diagnostics


def test_api_request_body_includes_format_schema(monkeypatch):
    seen = {}

    def fake_urlopen(req, timeout):
        seen["body"] = json.loads(req.data.decode())
        return FakeResponse(api_payload(json.dumps(SAFE)))

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.request.urlopen", fake_urlopen)
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert seen["body"]["format"]["type"] == "object"
    assert result.extraction_status == "SCHEMA_JSON"


def test_api_json_format_request(monkeypatch):
    seen = {}

    def fake_urlopen(req, timeout):
        seen["body"] = json.loads(req.data.decode())
        return FakeResponse(api_payload(json.dumps(SAFE)))

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.request.urlopen", fake_urlopen)
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS, use_schema=False)
    assert seen["body"]["format"] == "json"
    assert result.mode == "api_json_format"


def test_api_think_false_recorded(monkeypatch):
    seen = {}

    def fake_urlopen(req, timeout):
        seen["body"] = json.loads(req.data.decode())
        return FakeResponse(api_payload(json.dumps(SAFE)))

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.request.urlopen", fake_urlopen)
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS, think_false=True)
    assert seen["body"]["think"] is False
    assert result.mode == "api_schema_format_think_false"


def test_api_unavailable_handled(monkeypatch):
    def fake_urlopen(req, timeout):
        raise error.URLError("down")

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.request.urlopen", fake_urlopen)
    result = call_ollama_structured_api("qwen3:30b", "prompt")
    assert result.extraction_status == "STRUCTURED_API_UNAVAILABLE"


def test_external_url_blocked():
    result = call_ollama_structured_api("qwen3:30b", "prompt", endpoint="https://example.com/api")
    assert result.extraction_status == "MODEL_ERROR"


def test_api_invalid_envelope(monkeypatch):
    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.request.urlopen", lambda req, timeout: FakeResponse("{bad"))
    result = call_ollama_structured_api("qwen3:30b", "prompt")
    assert result.extraction_status == "JSON_INVALID"


def test_api_timeout_handled(monkeypatch):
    def fake_urlopen(req, timeout):
        raise TimeoutError()

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.request.urlopen", fake_urlopen)
    result = call_ollama_structured_api("qwen3:30b", "prompt", timeout_seconds=1)
    assert result.extraction_status == "MODEL_TIMEOUT"


def test_api_token_like_rejected(monkeypatch):
    fake_secret = "hf_" + "abcdefghijklmnopqrstuvwxyz"
    monkeypatch.setattr(
        "tools.qwen_capcard_lab.local_model.request.urlopen",
        lambda req, timeout: FakeResponse(api_payload(json.dumps(SAFE | {"explanation": fake_secret}))),
    )
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.extraction_status == "JSON_INVALID"


def test_api_forbidden_true_rejected(monkeypatch):
    monkeypatch.setattr(
        "tools.qwen_capcard_lab.local_model.request.urlopen",
        lambda req, timeout: FakeResponse(api_payload(json.dumps(SAFE | {"theorem_proof_claim": True}))),
    )
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.extraction_status == "JSON_INVALID"


def test_cli_think_false_mode_records_prompt(monkeypatch):
    class Proc:
        stdout = json.dumps(SAFE)
        stderr = ""
        returncode = 0

    seen = {}

    def fake_run(command, **_kwargs):
        seen["command"] = command
        return Proc()

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.subprocess.run", fake_run)
    result = call_ollama_json("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS, mode="cli_think_false")
    assert "/set nothink" in seen["command"][-1]
    assert result.mode == "cli_think_false"


def test_cli_hide_thinking_mode_records_prompt(monkeypatch):
    class Proc:
        stdout = json.dumps(SAFE)
        stderr = ""
        returncode = 0

    seen = {}

    def fake_run(command, **_kwargs):
        seen["command"] = command
        return Proc()

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.subprocess.run", fake_run)
    result = call_ollama_json("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS, mode="cli_hide_thinking")
    assert "Do not include thinking text" in seen["command"][-1]
    assert result.mode == "cli_hide_thinking"


def test_raw_cli_output_not_silently_accepted(monkeypatch):
    class Proc:
        stdout = "plain text"
        stderr = ""
        returncode = 0

    monkeypatch.setattr("tools.qwen_capcard_lab.local_model.subprocess.run", lambda *a, **k: Proc())
    result = call_ollama_json("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.extraction_status == "JSON_MISSING"


def test_api_schema_valid_flag(monkeypatch):
    monkeypatch.setattr(
        "tools.qwen_capcard_lab.local_model.request.urlopen",
        lambda req, timeout: FakeResponse(api_payload(json.dumps(SAFE))),
    )
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.schema_valid is True


def test_api_schema_invalid_flag(monkeypatch):
    monkeypatch.setattr(
        "tools.qwen_capcard_lab.local_model.request.urlopen",
        lambda req, timeout: FakeResponse(api_payload('{"task_id":"x"}')),
    )
    result = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.schema_valid is False


def test_response_to_dict_contains_mode(monkeypatch):
    monkeypatch.setattr(
        "tools.qwen_capcard_lab.local_model.request.urlopen",
        lambda req, timeout: FakeResponse(api_payload(json.dumps(SAFE))),
    )
    data = call_ollama_structured_api("qwen3:30b", "prompt", required_fields=REQUIRED_STRUCTURED_RESULT_FIELDS).to_dict()
    assert data["mode"] == "api_schema_format"


def test_schema_forbids_extra_top_level_properties():
    assert CAPCARD_RESULT_SCHEMA["additionalProperties"] is False


def test_schema_false_fields_are_const_false():
    assert CAPCARD_RESULT_SCHEMA["properties"]["public_ready"]["const"] is False


def test_missing_required_fields_are_diagnosed():
    diagnostics = validate_structured_result({"task_id": "x"})
    assert any(item.startswith("missing_required_field:") for item in diagnostics)


def test_markdown_fenced_structured_json_extracts():
    result = extract_json_object("```json\n" + json.dumps(SAFE) + "\n```", REQUIRED_STRUCTURED_RESULT_FIELDS)
    assert result.extracted_json["candidate_status"] == "BLOCKED_WITH_EXACT_FIX_LIST"
