from tools.qwen_capcard_lab.prompts import BASE_RULES, build_prompt, build_task_suite, expected_shape
from tools.qwen_capcard_lab.schema import OUTPUT_FALSE_FIELDS, TASK_FAMILIES


def test_expected_shape_has_false_fields():
    shape = expected_shape()
    for key in OUTPUT_FALSE_FIELDS:
        assert shape[key] is False


def test_base_rules_include_json_only():
    assert any("JSON only" in rule for rule in BASE_RULES)


def test_prompts_include_known_blocker():
    for family in TASK_FAMILIES:
        prompt = build_prompt(family, "easy", 1)
        assert "row 2/3" in prompt


def test_prompts_include_upload_boundary():
    prompt = build_prompt("capcard_row_generation", "adversarial", 2)
    assert "upload" in prompt.lower()


def test_suite_prompt_ids_unique():
    ids = [task["task_id"] for task in build_task_suite()["tasks"]]
    assert len(ids) == len(set(ids))


def test_suite_prompts_nonempty():
    for task in build_task_suite()["tasks"]:
        assert len(task["prompt"]) > 100


def test_suite_scoring_rules_present():
    for task in build_task_suite()["tasks"]:
        assert "valid_json" in task["scoring_rules"]
        assert "no_forbidden_claims" in task["scoring_rules"]


def test_no_prompt_requests_public_theorem_claim():
    for task in build_task_suite()["tasks"]:
        assert "prove a theorem" not in task["prompt"].lower()
