from tools.qwen_capcard_lab.capcard_scorer import score_output
from tools.qwen_capcard_lab.failure_memory import build_failure_memory
from tools.qwen_capcard_lab.prompts import build_task_suite
from tools.qwen_capcard_lab.runner import deterministic_fixture_output


def test_failure_memory_records_failed_reason():
    scored = [score_output(build_task_suite()["tasks"][0], "{bad")]
    memory = build_failure_memory(scored)
    assert memory["failure_memory"]


def test_failure_memory_reusable_flag_true():
    scored = [score_output(build_task_suite()["tasks"][0], "{bad")]
    memory = build_failure_memory(scored)
    assert memory["failure_memory"][0]["should_reuse_in_future"] is True


def test_failure_memory_has_default_when_no_failures():
    task = build_task_suite()["tasks"][0]
    scored = [score_output(task, deterministic_fixture_output(task))]
    memory = build_failure_memory(scored)
    assert memory["failure_memory"][0]["failure_pattern"] == "prevent_warn_unknown_overclaim"


def test_failure_memory_corrected_shape_mentions_json():
    scored = [score_output(build_task_suite()["tasks"][0], "{bad")]
    memory = build_failure_memory(scored)
    assert "JSON" in memory["failure_memory"][0]["corrected_shape"]


def test_failure_memory_repair_instruction_present():
    scored = [score_output(build_task_suite()["tasks"][0], "{bad")]
    memory = build_failure_memory(scored)
    assert memory["failure_memory"][0]["repair_instruction"]
