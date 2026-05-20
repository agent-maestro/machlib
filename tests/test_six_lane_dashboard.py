from pathlib import Path

from tools import build_six_lane_dashboard as dashboard


ROOT = Path("corpus/eml_lanes_draft")


def lane_by_id(obj, lane_id):
    for lane in obj["lanes"]:
        if lane["lane_id"] == lane_id:
            return lane
    raise AssertionError(f"missing {lane_id}")


def test_dashboard_counts_and_statuses():
    obj = dashboard.build_dashboard(ROOT)
    assert obj["seed_count"] == 19
    assert obj["lane_count"] == 6
    assert obj["zero_mathlib_status"] == "PASS"
    assert obj["overall_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert obj["public_ready_count"] == 0
    assert obj["upload_allowed_count"] == 0
    assert obj["release_ready_count"] == 0


def test_lane_seed_counts():
    obj = dashboard.build_dashboard(ROOT)
    assert lane_by_id(obj, "lane_1")["seed_count"] == 4
    for lane_id in ["lane_2", "lane_3", "lane_4", "lane_5", "lane_6"]:
        assert lane_by_id(obj, lane_id)["seed_count"] == 3


def test_all_lane_hard_failures_zero():
    obj = dashboard.build_dashboard(ROOT)
    assert not obj["failures"]
    for lane in obj["lanes"]:
        assert lane["failures"] == 0
        assert lane["zero_mathlib_status"] == "PASS"


def test_lane2_warnings_are_expected_draft_limitations():
    obj = dashboard.build_dashboard(ROOT)
    lane2 = lane_by_id(obj, "lane_2")
    assert lane2["warnings"] == 6
    assert lane2["status"] == "DRAFT_INTERNAL_LIMITATION"
    assert obj["expected_warnings"]
    for item in obj["expected_warnings"]:
        assert item["classification"] == "DRAFT_INTERNAL_LIMITATION"


def test_guardrails_and_blocked_actions():
    obj = dashboard.build_dashboard(ROOT)
    assert obj["push_performed"] is False
    assert obj["hf_upload_performed"] is False
    assert obj["package_publish_performed"] is False
    assert obj["guardrails"]["no_mathlib_dependency"] is True
    assert obj["guardrails"]["legacy_never_default"] is True
    assert obj["guardrails"]["legacy_never_release_dependency"] is True


def test_push_readiness_requires_human_decision():
    obj = dashboard.build_dashboard(ROOT)
    push = dashboard.build_push_readiness(obj)
    assert push["safe_to_push_now"] is False
    assert push["push_performed"] is False
    assert push["push_recommended"] == "HUMAN_DECISION_REQUIRED"
    assert "huggingface_upload" in push["blocked_actions"]
