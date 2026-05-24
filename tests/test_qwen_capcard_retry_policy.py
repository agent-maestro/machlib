from tools.qwen_capcard_lab.retry_policy import repair_instruction, should_retry


def test_retry_json_missing():
    assert should_retry({"status": "FAIL", "reasons": ["JSON_MISSING"], "score_0_to_100": 0}, 0)


def test_no_retry_after_pass():
    assert should_retry({"status": "PASS", "reasons": [], "score_0_to_100": 100}, 0) is False


def test_no_retry_after_max_attempts():
    assert should_retry({"status": "FAIL", "reasons": ["JSON_INVALID"], "score_0_to_100": 0}, 2) is False


def test_no_retry_token_secret():
    assert should_retry({"status": "FAIL", "reasons": ["token_like_secret"], "score_0_to_100": 0}, 0) is False


def test_no_retry_forbidden_true():
    assert should_retry({"status": "FAIL", "reasons": ["forbidden_true_field:public_ready"], "score_0_to_100": 0}, 0) is False


def test_retry_unknown_solver():
    assert should_retry({"status": "FAIL", "reasons": ["unknown solver status appears faked as solved"], "score_0_to_100": 60}, 0)


def test_retry_stale_reference():
    assert should_retry({"status": "FAIL", "reasons": ["stale Command Center reference used as direct evidence"], "score_0_to_100": 60}, 0)


def test_repair_instruction_includes_reason():
    text = repair_instruction({"reasons": ["JSON_INVALID"]})
    assert "JSON_INVALID" in text
