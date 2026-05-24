from tools.qwen_capcard_lab.model_registry import ModelRuntime
from tools.qwen_capcard_lab.supervisor import QwenCapCardSupervisor, score_structured, structured_to_capcard


SAFE = {
    "task_id": "t",
    "status": "WARN",
    "candidate_status": "BLOCKED_WITH_EXACT_FIX_LIST",
    "evidence_present": False,
    "missing_evidence": ["direct evidence"],
    "forbidden_claims_present": False,
    "public_ready": False,
    "petal_api_upload_performed": False,
    "huggingface_upload_performed": False,
    "production_marketplace_modified": False,
    "theorem_proof_claim": False,
    "certified_safety_claim": False,
    "production_controller_claim": False,
    "explanation": "missing evidence",
}


def test_structured_to_capcard_false_fields():
    text = structured_to_capcard({"task_id": "t"}, SAFE)
    assert '"public_ready": false' in text


def test_score_structured_passes_safe():
    score = score_structured({"task_id": "t", "prompt": "x"}, {"extracted_json": SAFE, "extraction_status": "SCHEMA_JSON", "extraction_diagnostics": []})
    assert score["schema_valid"] is True


def test_score_structured_missing_json_fails():
    score = score_structured({"task_id": "t"}, {"extracted_json": None, "extraction_status": "JSON_MISSING", "extraction_diagnostics": []})
    assert score["status"] == "FAIL"


def test_score_structured_bad_field_fails():
    score = score_structured({"task_id": "t"}, {"extracted_json": SAFE | {"public_ready": True}, "extraction_status": "SCHEMA_JSON", "extraction_diagnostics": []})
    assert score["schema_valid"] is False


def test_supervisor_stores_registry():
    sup = QwenCapCardSupervisor([ModelRuntime("qwen3:30b", "api_schema_format_think_false", schema_json_rate=1, average_score=99)])
    assert sup.max_attempts == 3


def test_supervisor_timeout_setting():
    sup = QwenCapCardSupervisor([], timeout_seconds=7)
    assert sup.timeout_seconds == 7


def test_supervisor_selectable_registry():
    sup = QwenCapCardSupervisor([ModelRuntime("qwen3:30b", "api_schema_format_think_false", schema_json_rate=1, average_score=99)])
    assert sup.registry[0].model == "qwen3:30b"
