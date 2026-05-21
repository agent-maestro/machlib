import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from review_branch_packet.git_inspect import (  # noqa: E402
    ensure_allowed_command,
    inspect_repo,
    is_allowed_command,
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
    clean, dirty = parse_status_output(" M data/proof-registry.jsonl\n?? scratch.txt\n D gone.md\nR  old -> new\n")
    assert clean is False
    assert dirty == [" M data/proof-registry.jsonl", "?? scratch.txt", " D gone.md", "R  old -> new"]


def test_parse_remote_output_dedupes_fetch_push():
    output = "\n".join(
        [
            "origin\thttps://example.invalid/repo.git (fetch)",
            "origin\thttps://example.invalid/repo.git (push)",
            "backup\thttps://example.invalid/backup.git (push)",
        ]
    )
    assert parse_remote_output(output, preferred="origin") == ("origin", "https://example.invalid/repo.git")


def test_parse_remote_output_missing_remote_graceful():
    assert parse_remote_output("", preferred="origin") == ("origin", "")


def test_parse_git_log_output():
    commits = parse_log_output("cafebabe demo commit\ndeadbeef older commit\n", limit=1)
    assert commits == ["cafebabe demo commit"]


def test_parse_git_log_keeps_sha_and_message():
    commits = parse_log_output("cafebabe demo commit with spaces\n")
    assert commits[0].split(maxsplit=1) == ["cafebabe", "demo commit with spaces"]


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


@pytest.mark.parametrize(
    "command",
    [
        ("git", "status", "--short"),
        ("git", "branch", "--show-current"),
        ("git", "remote", "-v"),
        ("git", "log", "--oneline", "-20"),
        ("git", "ls-remote", "--heads", "origin", "review/demo"),
    ],
)
def test_allowed_command_guard_accepts_read_only(command):
    assert is_allowed_command(command) is True
    ensure_allowed_command(command)


@pytest.mark.parametrize(
    "command",
    [
        ("git", "push", "origin", "HEAD"),
        ("git", "pull"),
        ("git", "fetch"),
        ("git", "checkout", "main"),
        ("git", "merge", "main"),
        ("git", "rebase", "main"),
        ("git", "reset", "--hard"),
        ("git", "add", "."),
        ("git", "commit", "-m", "x"),
        ("gh", "pr", "create"),
        ("npm", "run", "deploy"),
        ("twine", "upload", "dist/*"),
    ],
)
def test_forbidden_command_guard_blocks_actions(command):
    assert is_allowed_command(command) is False
    with pytest.raises(ValueError):
        ensure_allowed_command(command)


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


def test_inspect_repo_handles_absent_review_branch(monkeypatch):
    def fake_run_git(args, *, cwd="."):
        if args == ("status", "--short"):
            return "?? scratch.txt\n"
        if args == ("branch", "--show-current"):
            return "feat/ac-instances\n"
        if args == ("remote", "-v"):
            return ""
        if args[:2] == ("log", "--oneline"):
            return "cafebabe demo commit\n"
        if args[:2] == ("ls-remote", "--heads"):
            return ""
        raise AssertionError(args)

    monkeypatch.setattr("review_branch_packet.git_inspect.run_git", fake_run_git)
    result = inspect_repo(target_review_branch="review/missing")
    assert result["review_branch_present"] is False
    assert result["review_branch_sha"] == ""
    assert result["working_tree_clean"] is False
    assert result["dirty_files"] == ["?? scratch.txt"]
    assert result["remote_url"] == ""
