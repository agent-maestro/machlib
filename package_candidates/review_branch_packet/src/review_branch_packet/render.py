"""Render review branch packets."""

from __future__ import annotations

import json

from .packet import ReviewBranchPacket


def render_json_packet(packet: ReviewBranchPacket) -> str:
    return json.dumps(packet.to_dict(), indent=2, sort_keys=True) + "\n"


def render_markdown_packet(packet: ReviewBranchPacket) -> str:
    commits = "\n".join(f"- `{line}`" for line in packet.latest_commits) or "- none"
    dirty = "\n".join(f"- `{line}`" for line in packet.dirty_files) or "- clean"
    validations = "\n".join(
        f"- {item.get('name', 'validation')}: {item.get('status', 'UNKNOWN')}"
        for item in packet.validation_summaries
    ) or "- validation placeholders only"
    confirmations = "\n".join(
        f"- {name}: {value}" for name, value in sorted(packet.no_go_confirmations.items())
    )
    actions = "\n".join(f"- {item}" for item in packet.recommended_next_actions)
    blocked = "\n".join(f"- {item}" for item in packet.blocked_actions)

    return f"""# Review Branch Packet

## Branch Summary
- Current branch: `{packet.current_branch}`
- Local HEAD: `{packet.local_head_sha}`
- Local HEAD short: `{packet.local_head_short}`
- Working tree clean: `{packet.working_tree_clean}`

## Remote Review Branch Summary
- Remote: `{packet.remote_name}` `{packet.remote_url}`
- Target review branch: `{packet.target_review_branch}`
- Review branch present: `{packet.review_branch_present}`
- Review branch SHA: `{packet.review_branch_sha}`

## Latest Commits
{commits}

## Working Tree Status
- Clean: `{packet.working_tree_clean}`
{dirty}

## Validation Summary
{validations}

## No-Go Confirmations
{confirmations}

## Package / Publish / PyPI Boundary
- No package publish performed.
- No PyPI upload performed.
- No PyPI token handling performed.
- No release artifact creation performed.
- This packet is not a push, not a PR, not a merge, not a deploy, and not a publish.

## Human Approval Requirements
- Explicit approval is required before any push.
- No push, no GitHub PR, no merge, no deploy, no upload, and no package publish actions are performed.

## Recommended Next Actions
{actions}

## Blocked Actions
{blocked}
"""


def render_json(packet: ReviewBranchPacket) -> str:
    return render_json_packet(packet)


def render_markdown(packet: ReviewBranchPacket) -> str:
    return render_markdown_packet(packet)
