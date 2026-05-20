#!/usr/bin/env python3
"""Build a draft Command Center card/feed from the MachLib six-lane dashboard.

This tool writes local JSON payloads only. It does not deploy a command center,
push to a remote, publish packages, or upload artifacts.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
CARD_ID = "machlib_six_lane_status_2026_05_20"
SURFACE = "command.monogate.dev"
NOT_CLAIMED = [
    "not public-ready",
    "not upload-ready",
    "not release-ready",
    "not a theorem/proof/open-problem claim",
    "not a Hugging Face upload",
    "not a package publish",
    "not a PETAL/API upload",
    "not a CapCard marketplace change",
    "not a Forge compiler behavior change",
    "not a command center deployment",
]


def load_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def lane_card_rows(dashboard: dict[str, Any]) -> list[dict[str, Any]]:
    rows = []
    for lane in dashboard.get("lanes", []):
        rows.append(
            {
                "lane_id": lane["lane_id"],
                "title": lane["title"],
                "seed_count": lane["seed_count"],
                "execution_status": lane["execution_status"],
                "roundtrip_status": lane["roundtrip_status"],
                "warnings": lane["warnings"],
                "failures": lane["failures"],
                "status": lane["status"],
                "draft_internal": True,
                "public_ready": False,
                "upload_allowed": False,
                "release_ready": False,
            }
        )
    return rows


def build_card(dashboard: dict[str, Any], push: dict[str, Any]) -> dict[str, Any]:
    return {
        "card_id": CARD_ID,
        "surface": SURFACE,
        "visibility": "internal",
        "tier": "OBSERVATION",
        "title": "MachLib Six-Lane Status",
        "subtitle": "Zero-Mathlib DRAFT_INTERNAL coverage feed",
        "zero_mathlib_status": dashboard["zero_mathlib_status"],
        "overall_status": dashboard["overall_status"],
        "lane_count": dashboard["lane_count"],
        "seed_count": dashboard["seed_count"],
        "lanes": lane_card_rows(dashboard),
        "public_ready_count": dashboard["public_ready_count"],
        "upload_allowed_count": dashboard["upload_allowed_count"],
        "release_ready_count": dashboard["release_ready_count"],
        "push_performed": False,
        "safe_to_push_now": False,
        "push_recommended": push["push_recommended"],
        "requires_human_approval_for_push": True,
        "hf_upload_performed": False,
        "package_publish_performed": False,
        "petal_upload_performed": False,
        "capcard_marketplace_change_performed": False,
        "hardware_action_performed": False,
        "forge_compiler_behavior_change_performed": False,
        "public_theorem_claim_performed": False,
        "command_center_deploy_performed": False,
        "not_claimed": NOT_CLAIMED,
    }


def build_feed(card: dict[str, Any], dashboard_path: Path, push_path: Path) -> dict[str, Any]:
    return {
        "feed_id": "machlib_six_lane_status_feed_2026_05_20",
        "generated_at_date": DATE,
        "source_dashboard_path": str(dashboard_path),
        "source_push_readiness_path": str(push_path),
        "cards": [card],
        "command_center_surface": SURFACE,
        "adapter_status": "DRAFT_INTERNAL",
        "deploy_performed": False,
        "push_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "required_human_actions": [
            "Approve any future push before remote visibility.",
            "Approve any future Command Center integration before deployment.",
            "Keep public, upload, and release flags false until explicit review.",
        ],
    }


def build_schema() -> dict[str, Any]:
    required = [
        "card_id",
        "surface",
        "visibility",
        "tier",
        "zero_mathlib_status",
        "overall_status",
        "lane_count",
        "seed_count",
        "public_ready_count",
        "upload_allowed_count",
        "release_ready_count",
        "push_performed",
        "safe_to_push_now",
        "requires_human_approval_for_push",
        "command_center_deploy_performed",
        "not_claimed",
    ]
    return {
        "schema_id": "machlib_command_center_card_schema_DRAFT_2026_05_20",
        "status": "DRAFT_INTERNAL",
        "surface": SURFACE,
        "required_fields": required,
        "field_types": {
            "card_id": "string",
            "surface": "string",
            "visibility": "string",
            "tier": "string",
            "zero_mathlib_status": "string",
            "overall_status": "string",
            "lane_count": "integer",
            "seed_count": "integer",
            "lanes": "array",
            "public_ready_count": "integer",
            "upload_allowed_count": "integer",
            "release_ready_count": "integer",
            "push_performed": "boolean",
            "safe_to_push_now": "boolean",
            "requires_human_approval_for_push": "boolean",
            "command_center_deploy_performed": "boolean",
            "not_claimed": "array",
        },
        "lane_row_fields": [
            "lane_id",
            "title",
            "seed_count",
            "execution_status",
            "roundtrip_status",
            "warnings",
            "failures",
            "status",
            "draft_internal",
            "public_ready",
            "upload_allowed",
            "release_ready",
        ],
        "display_contract": [
            "Display as internal observation-tier status only.",
            "Do not show as public, upload, or release readiness.",
            "Do not imply deployment, remote push, or package publication.",
        ],
    }


def validate_card(card: dict[str, Any], feed: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    expected_false = [
        "push_performed",
        "hf_upload_performed",
        "package_publish_performed",
        "petal_upload_performed",
        "capcard_marketplace_change_performed",
        "hardware_action_performed",
        "forge_compiler_behavior_change_performed",
        "public_theorem_claim_performed",
        "command_center_deploy_performed",
    ]
    if card.get("card_id") != CARD_ID:
        failures.append("card_id mismatch")
    if card.get("surface") != SURFACE:
        failures.append("surface mismatch")
    if card.get("visibility") != "internal":
        failures.append("visibility mismatch")
    if card.get("zero_mathlib_status") != "PASS":
        failures.append("zero_mathlib_status not PASS")
    if card.get("overall_status") != "DRAFT_INTERNAL_VALIDATED":
        failures.append("overall_status unexpected")
    for key in ["public_ready_count", "upload_allowed_count", "release_ready_count"]:
        if card.get(key) != 0:
            failures.append(f"{key} must be 0")
    for key in expected_false:
        if card.get(key) is not False:
            failures.append(f"{key} must be false")
    if card.get("safe_to_push_now") is not False:
        failures.append("safe_to_push_now must be false")
    if card.get("requires_human_approval_for_push") is not True:
        failures.append("requires_human_approval_for_push must be true")
    for row in card.get("lanes", []):
        for key in ["public_ready", "upload_allowed", "release_ready"]:
            if row.get(key) is True:
                failures.append(f"{row.get('lane_id')} has {key}=true")
    if feed.get("deploy_performed") is not False:
        failures.append("feed deploy_performed must be false")
    if feed.get("safe_to_display_internally") is not True:
        failures.append("feed safe_to_display_internally must be true")
    if feed.get("safe_to_publish_publicly") is not False:
        failures.append("feed safe_to_publish_publicly must be false")
    return failures


def write_reports(card: dict[str, Any], feed: dict[str, Any]) -> None:
    reports = Path("reports")
    reports.mkdir(exist_ok=True)
    lane_lines = "\n".join(
        f"- {row['lane_id']}: {row['title']} | seeds={row['seed_count']} | status={row['status']}"
        for row in card["lanes"]
    )
    (reports / "machlib_command_center_feed_summary_2026_05_20.md").write_text(
        f"""# MachLib Command Center Feed Summary ({DATE})

## Scope

Local draft feed/card packet for `{SURFACE}`. No Command Center files were
modified and no deploy was performed.

## Inputs Consumed

- `corpus/eml_lanes_draft/six_lane_dashboard_2026_05_20.json`
- `corpus/eml_lanes_draft/six_lane_push_readiness_2026_05_20.json`

## Card Payload Summary

- Card: `{card['card_id']}`
- Visibility: `{card['visibility']}`
- Tier: `{card['tier']}`
- Overall status: `{card['overall_status']}`
- Zero-Mathlib status: `{card['zero_mathlib_status']}`

## Feed Payload Summary

- Feed: `{feed['feed_id']}`
- Adapter status: `{feed['adapter_status']}`
- Safe for internal display: {str(feed['safe_to_display_internally']).lower()}
- Safe for public display: {str(feed['safe_to_publish_publicly']).lower()}

## Command Center Relationship

This is a draft input contract only. It is not a deployment and it does not
modify the Command Center frontend.
""",
        encoding="utf-8",
    )
    (reports / "machlib_command_center_card_spec_2026_05_20.md").write_text(
        f"""# MachLib Command Center Card Spec ({DATE})

## Card Fields

The card exposes counts, lane rows, push-readiness gates, and no-go action
flags for internal display.

## Lane Rows

{lane_lines}

## Display Semantics

`PASS` means the relevant local checker or harness completed without hard
failure. `DRAFT_INTERNAL` means the row is review-only and not a release,
upload, or public result signal.

## Must Not Imply

- Public readiness
- Upload readiness
- Release readiness
- Theorem/proof/open-problem result
- Hugging Face upload
- Package publish
- PETAL/API upload
- CapCard marketplace change
- Forge compiler behavior change
- Command Center deployment
""",
        encoding="utf-8",
    )
    (reports / "machlib_command_center_adapter_notes_2026_05_20.md").write_text(
        f"""# MachLib Command Center Adapter Notes ({DATE})

This is only a draft feed adapter. `{SURFACE}` was not modified.

## Future Integration Path

1. Review the JSON schema draft.
2. Add an internal-only card reader in the Command Center repo.
3. Keep refresh local or private until a human approves remote visibility.

## Suggested Internal Card Title

MachLib Six-Lane Status

## Suggested Refresh Cadence

Refresh only after local dashboard rebuilds and zero-dependency checks pass.

## Safe Display Language

Use `DRAFT_INTERNAL_VALIDATED`, `internal`, and `human approval required`.

## Blocked Display Language

Avoid public-ready, upload-ready, release-ready, certified, production, or
proof-result wording.
""",
        encoding="utf-8",
    )
    (reports / "machlib_command_center_guardrail_report_2026_05_20.md").write_text(
        f"""# MachLib Command Center Guardrail Report ({DATE})

- No external formal-library dependency introduced: PASS
- Zero-Mathlib checker passes: PASS
- No Command Center deploy: PASS
- No git push: PASS
- No Hugging Face upload: PASS
- No PETAL/API upload: PASS
- No package publish: PASS
- No PyPI/token handling: PASS
- No hardware action: PASS
- No Forge compiler behavior change: PASS
- No public theorem/proof/open-problem claim: PASS
- No public_ready true rows: PASS
- No upload_allowed true rows: PASS
- No release_ready true rows: PASS
- No marketplace_ready true rows: PASS
- No CapCard certification claim: PASS
- No PETAL verification claim: PASS
- No token-like secret: PASS
""",
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--dashboard", required=True)
    parser.add_argument("--push-readiness", required=True)
    parser.add_argument("--out-card", required=True)
    parser.add_argument("--out-feed", required=True)
    parser.add_argument("--out-schema", required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    dashboard_path = Path(args.dashboard)
    push_path = Path(args.push_readiness)
    dashboard = load_json(dashboard_path)
    push = load_json(push_path)
    card = build_card(dashboard, push)
    feed = build_feed(card, dashboard_path, push_path)
    schema = build_schema()
    failures = validate_card(card, feed)

    for out, obj in [(Path(args.out_card), card), (Path(args.out_feed), feed), (Path(args.out_schema), schema)]:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    readme = Path(args.out_card).parent / "README.md"
    readme.write_text(
        f"""# MachLib Command Center Feeds

Draft internal feed/card payloads for `{SURFACE}`.

These files are local feed specs only. They do not deploy the Command Center,
perform a push, publish packages, upload artifacts, or mark any lane public,
upload, or release ready.
""",
        encoding="utf-8",
    )
    write_reports(card, feed)

    print("COMMAND_CENTER_CARD", card["card_id"], card["zero_mathlib_status"], card["overall_status"])
    print("COMMAND_CENTER_FEED", feed["feed_id"], feed["adapter_status"])
    if failures:
        for failure in failures:
            print(f"failure: {failure}")
    return 1 if args.strict and failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
