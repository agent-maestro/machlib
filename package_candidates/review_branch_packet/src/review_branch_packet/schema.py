"""Schema constants for review-branch-packet."""

from __future__ import annotations

BLOCKED_ACTIONS = (
    "git push",
    "git pull",
    "git fetch",
    "git checkout",
    "git merge",
    "gh pr create",
    "deploy",
    "twine",
    "package publish",
    "PyPI upload",
    "Hugging Face upload",
    "PETAL/API upload",
)

READ_ONLY_GIT_COMMANDS = (
    ("git", "status", "--short"),
    ("git", "branch", "--show-current"),
    ("git", "remote", "-v"),
    ("git", "log", "--oneline"),
    ("git", "ls-remote", "--heads"),
)

DEFAULT_NO_GO_CONFIRMATIONS = {
    "package_publish_performed": False,
    "pypi_token_handling_performed": False,
    "github_pr_created": False,
    "merge_performed": False,
    "push_performed": False,
    "command_center_deploy_performed": False,
    "hugging_face_upload_performed": False,
    "petal_api_call_performed": False,
    "hardware_action_performed": False,
    "forge_compiler_behavior_change_performed": False,
    "public_theorem_claim_performed": False,
    "mathlib_dependency_introduced": False,
    "token_like_secret_introduced": False,
}

DEFAULT_RECOMMENDED_NEXT_ACTIONS = (
    "review packet locally",
    "request explicit approval before any private review branch push",
    "keep PR, merge, deploy, upload, and publish actions blocked",
)
