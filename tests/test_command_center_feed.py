from pathlib import Path

from tools import build_command_center_feed as builder


DASHBOARD = Path("corpus/eml_lanes_draft/six_lane_dashboard_2026_05_20.json")
PUSH = Path("corpus/eml_lanes_draft/six_lane_push_readiness_2026_05_20.json")


def build_payloads():
    dashboard = builder.load_json(DASHBOARD)
    push = builder.load_json(PUSH)
    card = builder.build_card(dashboard, push)
    feed = builder.build_feed(card, DASHBOARD, PUSH)
    return card, feed


def test_card_identity_and_status():
    card, _feed = build_payloads()
    assert card["card_id"] == "machlib_six_lane_status_2026_05_20"
    assert card["surface"] == "command.monogate.dev"
    assert card["visibility"] == "internal"
    assert card["zero_mathlib_status"] == "PASS"
    assert card["overall_status"] == "DRAFT_INTERNAL_VALIDATED"
    assert card["lane_count"] == 6
    assert card["seed_count"] == 19


def test_card_guardrail_counts_and_actions():
    card, _feed = build_payloads()
    assert card["public_ready_count"] == 0
    assert card["upload_allowed_count"] == 0
    assert card["release_ready_count"] == 0
    assert card["push_performed"] is False
    assert card["safe_to_push_now"] is False
    assert card["requires_human_approval_for_push"] is True
    assert card["command_center_deploy_performed"] is False


def test_lane_rows_remain_internal_only():
    card, _feed = build_payloads()
    assert len(card["lanes"]) == 6
    for row in card["lanes"]:
        assert row["draft_internal"] is True
        assert row["public_ready"] is False
        assert row["upload_allowed"] is False
        assert row["release_ready"] is False


def test_not_claimed_boundaries():
    card, _feed = build_payloads()
    text = " ".join(card["not_claimed"])
    assert "not a theorem/proof/open-problem claim" in text
    assert "not a command center deployment" in text


def test_feed_display_boundaries():
    _card, feed = build_payloads()
    assert feed["command_center_surface"] == "command.monogate.dev"
    assert feed["adapter_status"] == "DRAFT_INTERNAL"
    assert feed["deploy_performed"] is False
    assert feed["push_performed"] is False
    assert feed["safe_to_display_internally"] is True
    assert feed["safe_to_publish_publicly"] is False


def test_card_validation_has_no_failures():
    card, feed = build_payloads()
    assert builder.validate_card(card, feed) == []
