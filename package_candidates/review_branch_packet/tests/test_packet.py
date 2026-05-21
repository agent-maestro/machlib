import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from review_branch_packet.packet import build_packet_from_parts  # noqa: E402
from review_branch_packet.render import render_json_packet, render_markdown_packet  # noqa: E402


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
    assert data["local_head_short"] == "cafebab"


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
    text = render_markdown_packet(sample_packet())
    assert "review/demo" in text
    assert "cafebabe demo commit" in text
    assert "No-Go Confirmations" in text
    assert "github_pr_created: False" in text
    assert "not a PR" in text
    assert "not a merge" in text
    assert "not a deploy" in text
    assert "not a publish" in text


def test_json_render_is_parseable():
    data = json.loads(render_json_packet(sample_packet()))
    assert data["review_branch_present"] is True
    assert data["review_branch_sha"] == "deadbeef"


def test_dirty_file_status_is_represented():
    packet = sample_packet([" M data/proof-registry.jsonl"])
    assert packet.working_tree_clean is False
    assert packet.dirty_files == [" M data/proof-registry.jsonl"]


def test_markdown_render_includes_dirty_files():
    text = render_markdown_packet(sample_packet([" M data/proof-registry.jsonl"]))
    assert "data/proof-registry.jsonl" in text
    assert "Clean: `False`" in text


def test_packet_handles_absent_review_branch():
    packet = build_packet_from_parts(
        current_branch="feat/ac-instances",
        remote_name="origin",
        remote_url="",
        target_review_branch="review/missing",
        review_branch_present=False,
        review_branch_sha="",
        local_head_sha="cafebabe123",
        latest_commits=["cafebabe demo commit"],
        dirty_files=[],
    )
    assert packet.review_branch_present is False
    assert packet.review_branch_sha == ""
    assert packet.local_head_short == "cafebab"
