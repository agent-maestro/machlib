"""Packet model and builders."""

from __future__ import annotations

from dataclasses import asdict, dataclass, field
from datetime import datetime, timezone

from .schema import BLOCKED_ACTIONS, DEFAULT_NO_GO_CONFIRMATIONS, DEFAULT_RECOMMENDED_NEXT_ACTIONS


@dataclass(frozen=True)
class ReviewBranchPacket:
    packet_id: str
    target_review_branch: str
    generated_at: str
    local_only: bool
    read_only: bool
    current_branch: str
    remote_name: str
    remote_url: str
    review_branch_present: bool
    review_branch_sha: str
    local_head_sha: str
    latest_commits: list[str]
    working_tree_clean: bool
    dirty_files: list[str]
    validation_summaries: list[dict[str, str]] = field(default_factory=list)
    blocked_actions: list[str] = field(default_factory=lambda: list(BLOCKED_ACTIONS))
    no_go_confirmations: dict[str, bool] = field(default_factory=lambda: dict(DEFAULT_NO_GO_CONFIRMATIONS))
    recommended_next_actions: list[str] = field(default_factory=lambda: list(DEFAULT_RECOMMENDED_NEXT_ACTIONS))
    package_publish_performed: bool = False
    pypi_token_handling_performed: bool = False
    github_pr_created: bool = False
    merge_performed: bool = False
    push_performed: bool = False
    command_center_deploy_performed: bool = False
    public_theorem_claim_performed: bool = False

    def to_dict(self) -> dict[str, object]:
        return asdict(self)


def build_packet_from_parts(
    *,
    current_branch: str,
    remote_name: str,
    remote_url: str,
    target_review_branch: str,
    review_branch_present: bool,
    review_branch_sha: str,
    local_head_sha: str,
    latest_commits: list[str],
    dirty_files: list[str],
    validation_summaries: list[dict[str, str]] | None = None,
    recommended_next_actions: list[str] | None = None,
    generated_at: str | None = None,
    push_performed: bool = False,
) -> ReviewBranchPacket:
    return ReviewBranchPacket(
        packet_id=f"review_branch_packet_{target_review_branch.replace('/', '_')}",
        target_review_branch=target_review_branch,
        generated_at=generated_at or datetime.now(timezone.utc).replace(microsecond=0).isoformat(),
        local_only=True,
        read_only=True,
        current_branch=current_branch,
        remote_name=remote_name,
        remote_url=remote_url,
        review_branch_present=review_branch_present,
        review_branch_sha=review_branch_sha,
        local_head_sha=local_head_sha,
        latest_commits=latest_commits,
        working_tree_clean=len(dirty_files) == 0,
        dirty_files=dirty_files,
        validation_summaries=validation_summaries or [],
        recommended_next_actions=recommended_next_actions or list(DEFAULT_RECOMMENDED_NEXT_ACTIONS),
        push_performed=push_performed,
    )


def build_packet_from_inspection(
    inspection: dict[str, object],
    *,
    validation_summaries: list[dict[str, str]] | None = None,
    recommended_next_actions: list[str] | None = None,
) -> ReviewBranchPacket:
    return build_packet_from_parts(
        current_branch=str(inspection["current_branch"]),
        remote_name=str(inspection["remote_name"]),
        remote_url=str(inspection["remote_url"]),
        target_review_branch=str(inspection["target_review_branch"]),
        review_branch_present=bool(inspection["review_branch_present"]),
        review_branch_sha=str(inspection["review_branch_sha"]),
        local_head_sha=str(inspection["local_head_sha"]),
        latest_commits=list(inspection["latest_commits"]),
        dirty_files=list(inspection["dirty_files"]),
        validation_summaries=validation_summaries,
        recommended_next_actions=recommended_next_actions,
    )
