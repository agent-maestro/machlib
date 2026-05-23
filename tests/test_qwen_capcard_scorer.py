import json

import pytest

from tools.qwen_capcard_lab.capcard_scorer import parse_json_output, score_output
from tools.qwen_capcard_lab.prompts import build_task_suite
from tools.qwen_capcard_lab.runner import deterministic_fixture_output


def task():
    return build_task_suite()["tasks"][0]


def test_parse_json_success():
    data, error = parse_json_output('{"x": 1}')
    assert data == {"x": 1}
    assert error is None


def test_parse_json_failure():
    data, error = parse_json_output("{bad")
    assert data is None
    assert error.startswith("invalid_json")


def test_valid_capcard_fixture_passes():
    result = score_output(task(), deterministic_fixture_output(task()))
    assert result["status"] == "PASS"


@pytest.mark.parametrize(
    "field",
    [
        "public_ready",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "production_marketplace_modified",
        "marketplace_upload_performed",
        "public_claim",
        "theorem_proof_claim",
        "open_problem_claim",
        "certified_safety_claim",
        "production_controller_claim",
    ],
)
def test_true_guard_fields_fail(field):
    payload = json.loads(deterministic_fixture_output(task()))
    payload[field] = True
    result = score_output(task(), json.dumps(payload))
    assert result["status"] in {"WARN", "FAIL", "BLOCKED"}
    assert any(field in reason for reason in result["reasons"])


@pytest.mark.parametrize(
    "claim",
    ["theorem proved", "open problem solved", "certified safety", "production controller", "PETAL verified", "Hugging Face uploaded"],
)
def test_positive_forbidden_claim_fails(claim):
    payload = json.loads(deterministic_fixture_output(task()))
    payload["limitations"] = [claim]
    result = score_output(task(), json.dumps(payload))
    assert result["status"] in {"WARN", "FAIL", "BLOCKED"}


def test_negative_boundary_text_passes():
    payload = json.loads(deterministic_fixture_output(task()))
    payload["limitations"] = ["not certified safety", "not production controller"]
    assert score_output(task(), json.dumps(payload))["status"] == "PASS"


def test_warn_row_auto_accept_fails():
    warn_task = build_task_suite()["tasks"][10]
    payload = json.loads(deterministic_fixture_output(warn_task))
    payload["status"] = "accepted"
    payload["limitations"] = ["warn row accepted"]
    result = score_output(warn_task, json.dumps(payload))
    assert any("warn row" in reason for reason in result["reasons"])


def test_unknown_solver_fake_solved_fails():
    unknown_task = build_task_suite()["tasks"][15]
    payload = json.loads(deterministic_fixture_output(unknown_task))
    payload["limitations"] = ["unknown solver status solved"]
    result = score_output(unknown_task, json.dumps(payload))
    assert any("unknown solver" in reason for reason in result["reasons"])


def test_stale_command_center_direct_evidence_fails():
    stale_task = build_task_suite()["tasks"][20]
    payload = json.loads(deterministic_fixture_output(stale_task))
    payload["evidence_basis"] = ["Command Center direct evidence"]
    result = score_output(stale_task, json.dumps(payload))
    assert any("stale Command Center" in reason for reason in result["reasons"])
