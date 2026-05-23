from tools.qwen_capcard_lab.prompts import build_task_suite
from tools.qwen_capcard_lab.schema import DIFFICULTY_BANDS, TASK_FAMILIES, validate_suite, validate_task


def test_suite_has_50_tasks():
    assert build_task_suite()["task_count"] == 50


def test_suite_has_all_families():
    suite = build_task_suite()
    assert {task["family"] for task in suite["tasks"]} == set(TASK_FAMILIES)


def test_suite_validates_cleanly():
    assert validate_suite(build_task_suite()) == []


def test_each_family_has_five_tasks():
    suite = build_task_suite()
    for family in TASK_FAMILIES:
        assert sum(1 for task in suite["tasks"] if task["family"] == family) == 5


def test_difficulty_bands_present():
    suite = build_task_suite()
    assert set(DIFFICULTY_BANDS).issubset({task["difficulty"] for task in suite["tasks"]})


def test_task_guard_fields_false():
    for task in build_task_suite()["tasks"]:
        assert task["public_ready_allowed"] is False
        assert task["petal_upload_allowed"] is False
        assert task["hf_upload_allowed"] is False
        assert task["production_marketplace_allowed"] is False


def test_invalid_family_detected():
    task = build_task_suite()["tasks"][0] | {"family": "bad"}
    assert "invalid family" in validate_task(task)


def test_invalid_difficulty_detected():
    task = build_task_suite()["tasks"][0] | {"difficulty": "bad"}
    assert "invalid difficulty" in validate_task(task)


def test_missing_field_detected():
    task = dict(build_task_suite()["tasks"][0])
    task.pop("prompt")
    assert any("missing prompt" in err for err in validate_task(task))


def test_forbidden_proof_prompt_detected():
    task = build_task_suite()["tasks"][0] | {"prompt": "Please prove a theorem publicly."}
    assert any("forbidden" in err for err in validate_task(task))
