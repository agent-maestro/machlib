import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from review_branch_packet.packet import build_packet_from_parts  # noqa: E402
from review_branch_packet.render import render_json, render_markdown  # noqa: E402


def sample_packet(dirty_files=None):
    return build_packet_from_parts(
        current_branch="feat/ac-instances",
        remote_name="origin",
        remote_url="https://example.invalid/repo.git",
        target_review_branch="review/demo",
        review_branch_present=True,
        review_branch_sha="deadbeef",
        local_head_sha="cafebabe",
        latest_commits=["cafebabe demo commit", "deadbeef older commit"],
        dirty_files=dirty_files or [],
        generated_at="2026-05-20T00:00:00+00:00",
    )


def test_packet_json_shape():
    packet = sample_packet()
    data = packet.to_dict()
    assert data["packet_id"] == "review_branch_packet_review_demo"
    assert data["local_only"] is True
    assert data["read_only"] is True
    assert data["target_review_branch"] == "review/demo"
    assert data["working_tree_clean"] is True


def test_no_go_confirmations_are_false_for_actions():
    packet = sample_packet()
    assert packet.push_performed is False
    assert packet.github_pr_created is False
    assert packet.merge_performed is False
    assert packet.command_center_deploy_performed is False
    assert packet.package_publish_performed is False
    assert packet.pypi_token_handling_performed is False
    assert all(value is False for value in packet.no_go_confirmations.values())


def test_markdown_render_includes_branch_commits_and_no_go():
    text = render_markdown(sample_packet())
    assert "review/demo" in text
    assert "cafebabe demo commit" in text
    assert "No-Go Confirmations" in text
    assert "github_pr_created: False" in text


def test_json_render_is_parseable():
    data = json.loads(render_json(sample_packet()))
    assert data["review_branch_present"] is True
    assert data["review_branch_sha"] == "deadbeef"


def test_dirty_file_status_is_represented():
    packet = sample_packet([" M data/proof-registry.jsonl"])
    assert packet.working_tree_clean is False
    assert packet.dirty_files == [" M data/proof-registry.jsonl"]
