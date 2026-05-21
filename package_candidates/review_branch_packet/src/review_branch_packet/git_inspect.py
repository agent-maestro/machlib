"""Read-only git inspection helpers for review branch packets."""

from __future__ import annotations

import subprocess
from pathlib import Path


class GitInspectError(RuntimeError):
    """Raised when a read-only git command fails."""


FORBIDDEN_COMMANDS = (
    ("git", "push"),
    ("git", "pull"),
    ("git", "fetch"),
    ("git", "checkout"),
    ("git", "merge"),
    ("git", "rebase"),
    ("git", "reset"),
    ("git", "add"),
    ("git", "commit"),
    ("gh", "pr", "create"),
    ("npm", "run", "deploy"),
    ("twine", "upload"),
)


def is_allowed_command(command: tuple[str, ...]) -> bool:
    """Return True when command is one of the supported read-only commands."""

    if not command:
        return False
    if any(command[: len(blocked)] == blocked for blocked in FORBIDDEN_COMMANDS):
        return False
    if command == ("git", "status", "--short"):
        return True
    if command == ("git", "branch", "--show-current"):
        return True
    if command == ("git", "remote", "-v"):
        return True
    if len(command) == 4 and command[:3] == ("git", "log", "--oneline"):
        return command[3].startswith("-") and command[3][1:].isdigit()
    if len(command) == 5 and command[:3] == ("git", "ls-remote", "--heads"):
        return bool(command[3]) and bool(command[4])
    return False


def ensure_allowed_command(command: tuple[str, ...]) -> None:
    if not is_allowed_command(command):
        raise ValueError(f"forbidden command: {' '.join(command)}")


def run_git(args: tuple[str, ...], *, cwd: Path | str = ".") -> str:
    """Run an allowed read-only git command and return stdout."""

    command = ("git", *args)
    ensure_allowed_command(command)
    completed = subprocess.run(
        command,
        cwd=cwd,
        check=False,
        text=True,
        capture_output=True,
    )
    if completed.returncode != 0:
        raise GitInspectError(completed.stderr.strip() or f"git {' '.join(args)} failed")
    return completed.stdout


def parse_status_output(output: str) -> tuple[bool, list[str]]:
    dirty_files: list[str] = []
    for line in output.splitlines():
        normalized = line.rstrip()
        if normalized.strip():
            dirty_files.append(normalized)
    return len(dirty_files) == 0, dirty_files


def parse_remote_output(output: str, preferred: str = "origin") -> tuple[str, str]:
    remotes: dict[str, list[str]] = {}
    for line in output.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        name, url = parts[0], parts[1]
        remotes.setdefault(name, [])
        if url not in remotes[name]:
            remotes[name].append(url)
    if preferred in remotes:
        return preferred, remotes[preferred][0]
    if remotes:
        name = sorted(remotes)[0]
        return name, remotes[name][0]
    return preferred, ""


def parse_log_output(output: str, limit: int | None = None) -> list[str]:
    commits = [line.strip() for line in output.splitlines() if line.strip()]
    if limit is not None:
        return commits[:limit]
    return commits


def short_sha(commit_line_or_sha: str) -> str:
    token = commit_line_or_sha.split()[0] if commit_line_or_sha.split() else commit_line_or_sha
    return token[:7]


def parse_ls_remote_output(output: str) -> tuple[bool, str]:
    line = output.strip().splitlines()[0] if output.strip() else ""
    if not line:
        return False, ""
    parts = line.split()
    return True, parts[0]


def inspect_repo(
    *,
    target_review_branch: str,
    cwd: Path | str = ".",
    remote_name: str = "origin",
    log_limit: int = 10,
) -> dict[str, object]:
    status = run_git(("status", "--short"), cwd=cwd)
    branch = run_git(("branch", "--show-current"), cwd=cwd).strip()
    remote_output = run_git(("remote", "-v"), cwd=cwd)
    safe_limit = max(1, int(log_limit))
    log_output = run_git(("log", "--oneline", f"-{safe_limit}"), cwd=cwd)
    ls_remote = run_git(("ls-remote", "--heads", remote_name, target_review_branch), cwd=cwd)

    working_tree_clean, dirty_files = parse_status_output(status)
    parsed_remote_name, remote_url = parse_remote_output(remote_output, preferred=remote_name)
    latest_commits = parse_log_output(log_output, limit=safe_limit)
    review_branch_present, review_branch_sha = parse_ls_remote_output(ls_remote)
    local_head_sha = latest_commits[0].split()[0] if latest_commits else ""

    return {
        "current_branch": branch,
        "remote_name": parsed_remote_name,
        "remote_url": remote_url,
        "target_review_branch": target_review_branch,
        "review_branch_present": review_branch_present,
        "review_branch_sha": review_branch_sha,
        "local_head_sha": local_head_sha,
        "local_head_short": short_sha(local_head_sha),
        "latest_commits": latest_commits,
        "working_tree_clean": working_tree_clean,
        "dirty_files": dirty_files,
    }
