import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from review_branch_packet.git_inspect import (  # noqa: E402
    inspect_repo,
    parse_log_output,
    parse_ls_remote_output,
    parse_remote_output,
    parse_status_output,
    run_git,
)


def test_parse_git_remote_output_prefers_origin_push():
    output = "\n".join(
        [
            "origin\thttps://example.invalid/repo.git (fetch)",
            "origin\thttps://example.invalid/repo.git (push)",
        ]
    )
    assert parse_remote_output(output) == ("origin", "https://example.invalid/repo.git")


def test_parse_git_status_clean():
    clean, dirty = parse_status_output("")
    assert clean is True
    assert dirty == []


def test_parse_git_status_dirty_file():
    clean, dirty = parse_status_output(" M data/proof-registry.jsonl\n?? scratch.txt\n")
    assert clean is False
    assert dirty == [" M data/proof-registry.jsonl", "?? scratch.txt"]


def test_parse_git_log_output():
    commits = parse_log_output("cafebabe demo commit\ndeadbeef older commit\n", limit=1)
    assert commits == ["cafebabe demo commit"]


def test_parse_ls_remote_branch_present():
    present, sha = parse_ls_remote_output("deadbeef\trefs/heads/review/demo\n")
    assert present is True
    assert sha == "deadbeef"


def test_parse_ls_remote_branch_absent():
    present, sha = parse_ls_remote_output("")
    assert present is False
    assert sha == ""


def test_run_git_rejects_forbidden_command():
    with pytest.raises(ValueError):
        run_git(("push", "origin", "HEAD"))


def test_inspect_repo_uses_only_read_only_commands(monkeypatch):
    calls = []

    def fake_run_git(args, *, cwd="."):
        calls.append(args)
        if args == ("status", "--short"):
            return ""
        if args == ("branch", "--show-current"):
            return "feat/ac-instances\n"
        if args == ("remote", "-v"):
            return "origin\thttps://example.invalid/repo.git (push)\n"
        if args[:2] == ("log", "--oneline"):
            return "cafebabe demo commit\n"
        if args[:2] == ("ls-remote", "--heads"):
            return "deadbeef\trefs/heads/review/demo\n"
        raise AssertionError(args)

    monkeypatch.setattr("review_branch_packet.git_inspect.run_git", fake_run_git)
    result = inspect_repo(target_review_branch="review/demo")
    assert result["current_branch"] == "feat/ac-instances"
    assert result["local_head_sha"] == "cafebabe"
    assert result["review_branch_sha"] == "deadbeef"
    forbidden = {"push", "pull", "fetch", "checkout", "merge"}
    assert all(call[0] not in forbidden for call in calls)
