from tools.qwen_capcard_lab.capcard_scorer import score_output
from tools.qwen_capcard_lab.prompts import build_task_suite
from tools.qwen_capcard_lab.repair_loop import repair_failed_outputs


def test_repair_loop_improves_invalid_json():
    tasks = build_task_suite()["tasks"][:3]
    scored = [score_output(task, "{bad") for task in tasks]
    result = repair_failed_outputs(tasks, scored, rounds=3)
    assert result["final_average_score"] > result["initial_average_score"]


def test_repair_loop_records_rounds():
    tasks = build_task_suite()["tasks"][:1]
    scored = [score_output(tasks[0], "{bad")]
    result = repair_failed_outputs(tasks, scored, rounds=3)
    assert result["repaired_outputs"][0]["rounds_used"] == 1


def test_repair_loop_has_no_no_go_after_repair():
    tasks = build_task_suite()["tasks"][:2]
    scored = [score_output(task, "{bad") for task in tasks]
    assert repair_failed_outputs(tasks, scored)["no_go_violations_after_repair"] == 0


def test_repair_loop_prompt_rules_present():
    tasks = build_task_suite()["tasks"][:2]
    scored = [score_output(task, "{bad") for task in tasks]
    result = repair_failed_outputs(tasks, scored)
    assert any("warn/unknown" in rule for rule in result["recommended_prompt_rules"])


def test_repair_loop_keeps_passes():
    tasks = build_task_suite()["tasks"][:1]
    from tools.qwen_capcard_lab.runner import deterministic_fixture_output

    scored = [score_output(tasks[0], deterministic_fixture_output(tasks[0]))]
    result = repair_failed_outputs(tasks, scored)
    assert result["fixed_count"] == 0
