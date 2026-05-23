from pathlib import Path

import pytest

from tools.capcard_lab.source_discovery import classify, discover_sources


@pytest.mark.parametrize(
    "path,family",
    [
        ("capcard_marketplace_drafts/x.json", "capcard_draft"),
        ("capcard_specs/spec.json", "capcard_spec"),
        ("reports/qwen_report.md", "qwen_evidence"),
        ("reports/puzzle_report.md", "puzzle_kernel_evidence"),
        ("command_center_feeds/card.json", "command_center_feed"),
        ("capcard_marketplace_drafts/adversarial/cards/x.json", "capcard_draft"),
    ],
)
def test_classify_paths(path, family):
    assert classify(Path(path)) == family


def test_discover_sources_finds_many():
    data = discover_sources(Path("."))
    assert data["source_count"] >= 40
    assert data["status"] == "PASS"


def test_discovery_has_no_public_actions():
    data = discover_sources(Path("."))
    assert data["production_marketplace_modified"] is False
    assert data["petal_api_upload_performed"] is False
    assert data["public_claim"] is False
