import importlib.util
from pathlib import Path


TOOL = Path("tools/build_machlib_phase_spine.py")
ROOT = Path(".")


def load_tool():
    spec = importlib.util.spec_from_file_location("build_machlib_phase_spine", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_phase_spine_shape_and_guardrails():
    tool = load_tool()
    spine, rollup, card, feed = tool.build_spine(ROOT)
    assert spine["zero_mathlib_status"] == "PASS"
    assert spine["overall_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert spine["push_performed"] is False
    assert spine["hf_upload_performed"] is False
    assert spine["package_publish_performed"] is False
    assert len(spine["phases"]) >= 14
    assert spine["phase_count"] == len(spine["phases"])
    assert rollup["zero_mathlib_status"] == "PASS"
    assert rollup["function_class_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert rollup["dfinite_execution_status"] == "PASS"
    assert rollup["dfinite_roundtrip_status"] in {"PASS", "WARN"}
    assert rollup["stochastic_hybrid_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert rollup["stochastic_hybrid_record_count"] == 12
    assert rollup["stochastic_hybrid_execution_status"] == "PASS"
    assert rollup["stochastic_hybrid_roundtrip_status"] in {"PASS", "WARN"}
    assert all(value is True for value in rollup["guardrails"].values())
    assert card["card_id"] == "machlib_phase_spine_2026_05_20"
    assert card["surface"] == "command.monogate.dev"
    assert card["safe_to_push_now"] is False
    assert card["safe_to_display_internally"] is True
    assert card["safe_to_publish_publicly"] is False
    assert feed["adapter_status"] == "DRAFT_INTERNAL"
    assert feed["deploy_performed"] is False


def test_required_phase_commits_are_mapped_or_external():
    tool = load_tool()
    spine, _, _, _ = tool.build_spine(ROOT)
    phase_by_id = {row["phase_id"]: row for row in spine["phases"]}
    assert phase_by_id["phase_0"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_2"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_3"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_4"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_9"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_10"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_11"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_13"]["validation_status"] == "COMMITTED"
    assert phase_by_id["phase_1"]["validation_status"] in {"COMMITTED", "EXTERNAL_EVIDENCE_REPORTED"}
