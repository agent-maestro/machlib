"""Build a local MachLib evidence reel storyboard packet.

This tool is intentionally local-only. It reads existing evidence reports and
emits JSON/Markdown planning artifacts for a future audiovisual reel. It does
not render video, upload packages, handle tokens, deploy, or call external APIs.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE_TAG = "2026_05_21"
REEL_ID = f"machlib_package_reel_{DATE_TAG}"
TITLE = "MachLib Evidence Tooling Update"

PUBLISHED_PACKAGES = [
    "zero-mathlib-checker",
    "claim-boundary",
    "eml-records",
    "review-branch-packet",
]

READY_PENDING_PACKAGES = [
    "machlib",
    "machlib-workbench",
    "eml-harness",
    "hybrid-trace-eml",
]

PASSED_CHECKS = [
    "package tests",
    "zero-Mathlib gates",
    "Twine checks",
    "repo artifact checks",
]

PAUSED_ITEMS = [
    "PyPI HTTP 429 for MachLib",
    "no immediate retry",
]

BOUNDARY_CLAIMS = [
    "not a theorem prover",
    "not a Mathlib replacement",
    "not an open-problem solution",
    "not certified safety",
    "not production controller evidence",
]

NEXT_ACTIONS = [
    "cooldown",
    "record retry plan",
    "retry MachLib later",
    "continue AV product tooling",
]

EVIDENCE_INPUTS = [
    Path("product_readiness/all_packages_publish_readiness_2026_05_20.json"),
    Path("product_readiness/all_packages_upload_manifest_DRAFT_2026_05_20.json"),
    Path("product_readiness/package_001_cleanup_upload_result_2026_05_20.json"),
    Path("product_readiness/machlib_publish_readiness_2026_05_21.json"),
    Path("reports/all_packages_publish_readiness_2026_05_20.md"),
    Path("reports/package_001_cleanup_upload_result_2026_05_20.md"),
]


@dataclass(frozen=True)
class ReelOutputs:
    storyboard_json: Path
    reel_script_md: Path
    narration_md: Path
    card_manifest_json: Path
    summary_md: Path
    guardrail_md: Path
    next_steps_md: Path


def load_json(path: Path) -> dict[str, Any]:
    """Load JSON from a path, returning an empty object if it is missing."""
    if not path.exists():
        return {}
    return json.loads(path.read_text())


def load_text(path: Path) -> str:
    """Load text from a path, returning an empty string if it is missing."""
    if not path.exists():
        return ""
    return path.read_text()


def load_evidence(root: Path) -> dict[str, Any]:
    """Collect the evidence inputs used to build the reel."""
    evidence: dict[str, Any] = {
        "json": {},
        "text": {},
        "available_inputs": [],
        "missing_inputs": [],
    }
    for rel_path in EVIDENCE_INPUTS:
        path = root / rel_path
        key = rel_path.as_posix()
        if path.exists():
            evidence["available_inputs"].append(key)
            if path.suffix == ".json":
                evidence["json"][key] = load_json(path)
            else:
                evidence["text"][key] = load_text(path)
        else:
            evidence["missing_inputs"].append(key)
    return evidence


def _card(card_id: str, title: str, bullets: list[str], narration: str) -> dict[str, Any]:
    return {
        "card_id": card_id,
        "title": title,
        "duration_seconds": 8,
        "visual_direction": "clean evidence card with concise package/status text",
        "on_screen_bullets": bullets,
        "narration": narration,
    }


def build_storyboard(evidence: dict[str, Any] | None = None) -> dict[str, Any]:
    """Build the storyboard data model without writing files."""
    evidence = evidence or {"available_inputs": [], "missing_inputs": []}
    cards = [
        _card(
            "01-title",
            TITLE,
            ["pre-alpha tooling update", "local evidence reel storyboard"],
            "This is a short evidence update for MachLib package tooling.",
        ),
        _card(
            "02-published-packages",
            "Published packages",
            PUBLISHED_PACKAGES,
            "Four small pre-alpha packages are published and verified for early testing.",
        ),
        _card(
            "03-ready-pending-packages",
            "Ready / pending packages",
            READY_PENDING_PACKAGES,
            "MachLib and adjacent tools remain in a careful readiness and retry path.",
        ),
        _card(
            "04-what-passed",
            "What passed",
            PASSED_CHECKS,
            "The packet records tests, bounded validation, Twine checks, and repo artifact checks.",
        ),
        _card(
            "05-paused",
            "What failed / paused",
            PAUSED_ITEMS,
            "MachLib hit a PyPI rate limit, so the retry path pauses instead of forcing another upload.",
        ),
        _card(
            "06-not-claimed",
            "What is not claimed",
            BOUNDARY_CLAIMS,
            "This is evidence tooling, not a public proof claim or safety certification.",
        ),
        _card(
            "07-next-actions",
            "Next actions",
            NEXT_ACTIONS,
            "The next steps are cooldown, retry planning, and continued local AV product tooling.",
        ),
    ]
    return {
        "reel_id": REEL_ID,
        "title": TITLE,
        "date": "2026-05-21",
        "status": "LOCAL_STORYBOARD_ONLY_NO_VIDEO_RENDERED",
        "source_evidence": {
            "available_inputs": sorted(evidence.get("available_inputs", [])),
            "missing_inputs": sorted(evidence.get("missing_inputs", [])),
        },
        "cards": cards,
        "guardrails": {
            "video_rendered": False,
            "pypi_upload_performed": False,
            "pypi_token_handling_performed": False,
            "deploy_performed": False,
            "hardware_action_performed": False,
            "public_theorem_proof_open_problem_claim": False,
        },
    }


def build_card_manifest(storyboard: dict[str, Any]) -> dict[str, Any]:
    return {
        "manifest_id": f"{REEL_ID}_cards",
        "asset_status": "PLACEHOLDER_ONLY_NO_VIDEO_RENDERED",
        "cards": [
            {
                "card_id": card["card_id"],
                "title": card["title"],
                "format": "storyboard_card",
                "placeholder_asset": f"{card['card_id']}.svg",
                "placeholder_created": False,
            }
            for card in storyboard["cards"]
        ],
    }


def _markdown_script(storyboard: dict[str, Any]) -> str:
    lines = [
        f"# {storyboard['title']}",
        "",
        "Local storyboard packet for an audiovisual-ready evidence reel.",
        "",
    ]
    for card in storyboard["cards"]:
        lines.extend(
            [
                f"## {card['card_id']} - {card['title']}",
                "",
                f"Visual: {card['visual_direction']}.",
                "",
                "On-screen text:",
            ]
        )
        lines.extend(f"- {bullet}" for bullet in card["on_screen_bullets"])
        lines.extend(["", f"Narration: {card['narration']}", ""])
    return "\n".join(lines).rstrip() + "\n"


def _narration(storyboard: dict[str, Any]) -> str:
    lines = [
        "# MachLib Package Reel Narration",
        "",
        "Tone: plain, bounded, and pre-alpha. Avoid hype and avoid proof language.",
        "",
    ]
    for card in storyboard["cards"]:
        lines.extend([f"## {card['title']}", "", card["narration"], ""])
    return "\n".join(lines).rstrip() + "\n"


def _summary(storyboard: dict[str, Any]) -> str:
    return "\n".join(
        [
            "# MachLib Evidence Reel Summary",
            "",
            f"Reel: {storyboard['title']}",
            "",
            "Outputs created:",
            "- JSON storyboard",
            "- Markdown reel script",
            "- narration script",
            "- card manifest",
            "- local guardrail and next-step reports",
            "",
            "Card sequence:",
            *[f"- {card['title']}" for card in storyboard["cards"]],
            "",
            "This packet is local product tooling only. It does not render video or upload anything.",
            "",
        ]
    )


def _guardrail_report(storyboard: dict[str, Any]) -> str:
    return "\n".join(
        [
            "# MachLib Evidence Reel Guardrail Report",
            "",
            "Guardrail status:",
            "- no video rendered",
            "- no PyPI upload",
            "- no PyPI token handling",
            "- no package publish",
            "- no deploy",
            "- no Hugging Face upload or API call",
            "- no PETAL/API call",
            "- no hardware action",
            "- no Forge compiler behavior change",
            "- no public theorem/proof/open-problem claim",
            "- no Mathlib dependency introduced",
            "",
            "Boundary language included:",
            *[f"- {claim}" for claim in BOUNDARY_CLAIMS],
            "",
        ]
    )


def _next_steps() -> str:
    return "\n".join(
        [
            "# MachLib Evidence Reel Next Steps",
            "",
            "Recommended next local tasks:",
            "- add visual design templates for each card",
            "- add optional local SVG/PNG placeholder rendering",
            "- record a voiceover pass from the narration script",
            "- keep MachLib upload retry separate from this AV tooling",
            "",
            "Upload and deployment gates remain closed for this task.",
            "",
        ]
    )


def write_outputs(
    storyboard: dict[str, Any],
    evidence_reels_dir: Path,
    reports_dir: Path,
) -> ReelOutputs:
    evidence_reels_dir.mkdir(parents=True, exist_ok=True)
    reports_dir.mkdir(parents=True, exist_ok=True)

    outputs = ReelOutputs(
        storyboard_json=evidence_reels_dir / f"{REEL_ID}.json",
        reel_script_md=evidence_reels_dir / f"machlib_package_reel_script_{DATE_TAG}.md",
        narration_md=evidence_reels_dir / f"machlib_package_reel_narration_{DATE_TAG}.md",
        card_manifest_json=evidence_reels_dir / f"machlib_package_reel_cards_{DATE_TAG}.json",
        summary_md=reports_dir / f"machlib_evidence_reel_summary_{DATE_TAG}.md",
        guardrail_md=reports_dir / f"machlib_evidence_reel_guardrail_report_{DATE_TAG}.md",
        next_steps_md=reports_dir / f"machlib_evidence_reel_next_steps_{DATE_TAG}.md",
    )

    outputs.storyboard_json.write_text(json.dumps(storyboard, indent=2, sort_keys=True) + "\n")
    outputs.reel_script_md.write_text(_markdown_script(storyboard))
    outputs.narration_md.write_text(_narration(storyboard))
    outputs.card_manifest_json.write_text(
        json.dumps(build_card_manifest(storyboard), indent=2, sort_keys=True) + "\n"
    )
    outputs.summary_md.write_text(_summary(storyboard))
    outputs.guardrail_md.write_text(_guardrail_report(storyboard))
    outputs.next_steps_md.write_text(_next_steps())
    return outputs


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a local MachLib evidence reel packet.")
    parser.add_argument("--root", default=".", type=Path, help="MachLib repository root")
    parser.add_argument("--evidence-reels-dir", default=Path("evidence_reels"), type=Path)
    parser.add_argument("--reports-dir", default=Path("reports"), type=Path)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    root = args.root.resolve()
    evidence = load_evidence(root)
    storyboard = build_storyboard(evidence)
    outputs = write_outputs(
        storyboard,
        root / args.evidence_reels_dir,
        root / args.reports_dir,
    )
    print("EVIDENCE_REEL_WRITTEN", outputs.storyboard_json)
    print("EVIDENCE_REEL_CARDS", len(storyboard["cards"]))


if __name__ == "__main__":
    main()
