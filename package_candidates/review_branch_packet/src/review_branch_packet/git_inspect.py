"""Read-only git inspection helpers for review branch packets."""

from __future__ import annotations

import subprocess
from pathlib import Path


class GitInspectError(RuntimeError):
    """Raised when a read-only git command fails."""


def run_git(args: tuple[str, ...], *, cwd: Path | str = ".") -> str:
    """Run an allowed read-only git command and return stdout."""

    allowed_prefixes = (
        ("status", "--short"),
        ("branch", "--show-current"),
        ("remote", "-v"),
        ("log", "--oneline"),
        ("ls-remote", "--heads"),
    )
    if not any(args[: len(prefix)] == prefix for prefix in allowed_prefixes):
        raise ValueError(f"forbidden git command: git {' '.join(args)}")
    completed = subprocess.run(
        ("git", *args),
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
        if line.strip():
            dirty_files.append(line)
    return len(dirty_files) == 0, dirty_files


def parse_remote_output(output: str, preferred: str = "origin") -> tuple[str, str]:
    fallback: tuple[str, str] | None = None
    for line in output.splitlines():
        parts = line.split()
        if len(parts) < 2:
            continue
        name, url = parts[0], parts[1]
        if fallback is None:
            fallback = (name, url)
        if name == preferred and "(push)" in line:
            return name, url
    return fallback or (preferred, "")


def parse_log_output(output: str, limit: int | None = None) -> list[str]:
    commits = [line.strip() for line in output.splitlines() if line.strip()]
    if limit is not None:
        return commits[:limit]
    return commits


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
    log_output = run_git(("log", "--oneline", f"-{log_limit}"), cwd=cwd)
    ls_remote = run_git(("ls-remote", "--heads", remote_name, target_review_branch), cwd=cwd)

    working_tree_clean, dirty_files = parse_status_output(status)
    parsed_remote_name, remote_url = parse_remote_output(remote_output, preferred=remote_name)
    latest_commits = parse_log_output(log_output, limit=log_limit)
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
        "latest_commits": latest_commits,
        "working_tree_clean": working_tree_clean,
        "dirty_files": dirty_files,
    }
