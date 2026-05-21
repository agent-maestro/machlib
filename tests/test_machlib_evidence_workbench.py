import importlib.util
from pathlib import Path


TOOL = Path("tools/run_machlib_evidence_workbench.py")
REPO_ROOT = Path(".")


def load_workbench():
    spec = importlib.util.spec_from_file_location("run_machlib_evidence_workbench", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_workbench_status_core_fields():
    workbench = load_workbench()
    status, card, feed = workbench.build_status(REPO_ROOT)
    assert status["workbench_status"] == "PASS"
    assert status["zero_mathlib_status"] == "PASS"
    assert status["six_lane_seed_count"] == 19
    assert status["function_class_record_count"] == 20
    assert status["executable_function_class_count"] == 5
    assert status["safe_to_push_now"] is False
    assert status["push_performed"] is False
    assert status["hf_upload_performed"] is False
    assert status["package_publish_performed"] is False
    assert status["command_center_deploy_performed"] is False
    assert status["public_theorem_claim_performed"] is False
    assert status["review_branch"] == "review/machlib-function-class-frontier-2026-05-20"
    assert status["failures"] == []
    assert feed["deploy_performed"] is False


def test_workbench_card_is_internal_only():
    workbench = load_workbench()
    _status, card, _feed = workbench.build_status(REPO_ROOT)
    assert card["card_id"] == "machlib_evidence_workbench_2026_05_20"
    assert card["surface"] == "command.monogate.dev"
    assert card["safe_to_display_internally"] is True
    assert card["safe_to_publish_publicly"] is False
    assert card["safe_to_push_now"] is False
    assert card["command_center_deploy_performed"] is False


def test_workbench_guardrails_true():
    workbench = load_workbench()
    status, _card, _feed = workbench.build_status(REPO_ROOT)
    assert all(value is True for value in status["guardrails"].values())
