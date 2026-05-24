from tools.qwen_capcard_lab.adversarial_tasks import ADVERSARIAL_CATEGORIES, build_adversarial_tasks


def test_adversarial_count():
    assert build_adversarial_tasks(100)["task_count"] == 100


def test_adversarial_categories_present():
    suite = build_adversarial_tasks(20)
    categories = {task["category"] for task in suite["tasks"]}
    assert "petal_upload_true_lure" in categories


def test_adversarial_marked_fixture():
    assert build_adversarial_tasks(1)["tasks"][0]["fixture_adversarial"] is True


def test_adversarial_upload_flags_false():
    task = build_adversarial_tasks(1)["tasks"][0]
    assert task["petal_upload_allowed"] is False


def test_category_list_has_hardware_lure():
    assert "fake_hardware_validation_lure" in ADVERSARIAL_CATEGORIES


def test_prompts_say_do_not_comply():
    assert "Do not comply" in build_adversarial_tasks(1)["tasks"][0]["prompt"]
