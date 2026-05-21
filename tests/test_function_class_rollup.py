import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_function_classes_draft")
TOOL = Path("tools/build_function_class_rollup.py")


def load_builder():
    spec = importlib.util.spec_from_file_location("build_function_class_rollup", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_rollup_core_counts_and_statuses():
    builder = load_builder()
    rollup, push, card, feed = builder.build_all(ROOT)
    assert rollup["record_count"] == 20
    assert rollup["executable_class_count"] == 4
    assert rollup["zero_mathlib_status"] == "PASS"
    assert rollup["function_class_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert rollup["public_ready_count"] == 0
    assert rollup["upload_allowed_count"] == 0
    assert rollup["release_ready_count"] == 0
    assert rollup["failures"] == []
    assert push["safe_to_push_now"] is False
    assert card["command_center_deploy_performed"] is False
    assert card["safe_to_display_internally"] is True
    assert card["safe_to_publish_publicly"] is False
    assert feed["deploy_performed"] is False


def test_class_rows_have_expected_warning_only():
    builder = load_builder()
    rollup = builder.build_rollup(ROOT)
    executable = [row for row in rollup["classes"] if row["class_id"] != "CLASS_BOUNDARY_RELATION"]
    assert len(executable) == 4
    for row in executable:
        assert row["execution_status"] == "PASS"
        assert row["execution_failed"] == 0
        assert row["roundtrip_status"] == "WARN"
        assert row["roundtrip_failed"] == 0
        assert row["expected_warning_only"] is True
        assert row["expected_warning"] == "Forge draft-schema limitation"


def test_boundary_rows_are_records_only():
    builder = load_builder()
    rollup = builder.build_rollup(ROOT)
    boundary = [row for row in rollup["classes"] if row["class_id"] == "CLASS_BOUNDARY_RELATION"][0]
    assert boundary["record_count"] == 3
    assert boundary["executable_status"] == "VALIDATED_AS_RECORDS_ONLY"
    assert boundary["roundtrip_status"] == "NOT_EXECUTED"
    assert boundary["failures"] == []


def test_guardrails_and_command_center_card():
    builder = load_builder()
    rollup, push, card, feed = builder.build_all(ROOT)
    assert all(value is True for value in rollup["guardrails"].values())
    assert rollup["push_performed"] is False
    assert rollup["hf_upload_performed"] is False
    assert rollup["package_publish_performed"] is False
    assert rollup["command_center_deploy_performed"] is False
    assert rollup["public_theorem_claim_performed"] is False
    assert push["push_recommended"] == "HUMAN_DECISION_REQUIRED"
    assert card["card_id"] == "machlib_function_class_status_2026_05_20"
    assert card["surface"] == "command.monogate.dev"
    assert feed["adapter_status"] == "DRAFT_INTERNAL"
