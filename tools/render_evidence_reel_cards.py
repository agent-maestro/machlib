"""Render local SVG card previews for the MachLib evidence reel.

The renderer is pure Python and local-only. It creates SVG storyboard cards,
an HTML index, and a render manifest. It does not render video or audio,
upload packages, handle tokens, deploy, or call external APIs.
"""

from __future__ import annotations

import argparse
import json
import textwrap
from dataclasses import dataclass
from datetime import datetime, timezone
from html import escape
from pathlib import Path
from typing import Any


DATE_TAG = "2026_05_21"
REEL_ID = f"machlib_package_reel_{DATE_TAG}"
BOUNDARY_FOOTER_TEXT = "Pre-alpha evidence tooling - not a theorem/proof/safety claim."
BOUNDARY_FOOTER_VISIBLE = "Pre-alpha evidence tooling &#8212; not a theorem/proof/safety claim."
RENDER_ROOT = Path("evidence_reels/rendered") / REEL_ID
STORYBOARD_PATH = Path("evidence_reels") / f"{REEL_ID}.json"
CARDS_PATH = Path("evidence_reels") / f"machlib_package_reel_cards_{DATE_TAG}.json"
SCRIPT_PATH = Path("evidence_reels") / f"machlib_package_reel_script_{DATE_TAG}.md"
NARRATION_PATH = Path("evidence_reels") / f"machlib_package_reel_narration_{DATE_TAG}.md"

CARD_WIDTH = 1280
CARD_HEIGHT = 720


@dataclass(frozen=True)
class RenderCard:
    card_id: str
    filename: str
    title: str
    subtitle: str
    bullets: tuple[str, ...]
    accent: str


RENDER_CARDS = (
    RenderCard(
        "01-title",
        "card_01_title.svg",
        "MachLib Evidence Tooling Update",
        "Package and validation checkpoint",
        (
            "published: zero-mathlib-checker, claim-boundary, eml-records, review-branch-packet",
            "pending: MachLib retry path and adjacent local candidates",
            "status: local visual cards only",
        ),
        "#2457a6",
    ),
    RenderCard(
        "02-published-packages",
        "card_02_published_packages.svg",
        "Published packages",
        "PyPI 0.0.1 cleanup releases",
        (
            "zero-mathlib-checker 0.0.1",
            "claim-boundary 0.0.1",
            "eml-records 0.0.1",
            "review-branch-packet 0.0.1",
        ),
        "#28705b",
    ),
    RenderCard(
        "03-ready-pending",
        "card_03_ready_pending.svg",
        "Ready / pending packages",
        "Local readiness and paused upload state",
        (
            "MachLib package-ready locally but PyPI 429 paused",
            "machlib-workbench / eml-harness / hybrid-trace-eml not uploaded",
            "machlib not yet published",
        ),
        "#8057a7",
    ),
    RenderCard(
        "04-passed-checks",
        "card_04_passed_checks.svg",
        "Passed checks",
        "Validation packet summary",
        (
            "package tests",
            "zero-Mathlib gates",
            "dry-run/twine checks",
            "no release artifacts in repo",
        ),
        "#a65e24",
    ),
    RenderCard(
        "05-pause-failure",
        "card_05_pause_failure.svg",
        "Pause / failure",
        "MachLib upload retry boundary",
        (
            "PyPI HTTP 429 for MachLib",
            "no immediate retry",
            "retry after cooldown",
        ),
        "#a43845",
    ),
    RenderCard(
        "06-not-claimed",
        "card_06_not_claimed.svg",
        "Not claimed",
        "Public boundary language",
        (
            "not theorem prover",
            "not Mathlib replacement",
            "not open-problem result",
            "not certified safety",
            "not production controller",
        ),
        "#3f6678",
    ),
    RenderCard(
        "07-next-actions",
        "card_07_next_actions.svg",
        "Next actions",
        "Local product tooling path",
        (
            "keep cooldown",
            "render visual cards",
            "review Command Center mount",
            "retry MachLib later with fresh token",
        ),
        "#5c6f2b",
    ),
)


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        return {}
    return json.loads(path.read_text())


def wrap_lines(text: str, width: int) -> list[str]:
    lines = textwrap.wrap(text, width=width, break_long_words=False, break_on_hyphens=False)
    return lines or [text]


def svg_text_lines(
    lines: list[str],
    *,
    x: int,
    y: int,
    size: int,
    fill: str,
    weight: str = "400",
    line_height: int = 42,
) -> str:
    chunks = []
    for index, line in enumerate(lines):
        chunks.append(
            f'<text x="{x}" y="{y + index * line_height}" font-size="{size}" '
            f'font-weight="{weight}" fill="{fill}">{escape(line)}</text>'
        )
    return "\n".join(chunks)


def render_svg(card: RenderCard, position: int) -> str:
    title_lines = wrap_lines(card.title, 34)
    subtitle_lines = wrap_lines(card.subtitle, 58)
    bullet_lines: list[str] = []
    for bullet in card.bullets:
        wrapped = wrap_lines(bullet, 62)
        bullet_lines.append(f"- {wrapped[0]}")
        bullet_lines.extend(f"  {line}" for line in wrapped[1:])

    return f'''<svg xmlns="http://www.w3.org/2000/svg" width="{CARD_WIDTH}" height="{CARD_HEIGHT}" viewBox="0 0 {CARD_WIDTH} {CARD_HEIGHT}" role="img" aria-labelledby="title desc">
  <title id="title">{escape(card.title)}</title>
  <desc id="desc">{escape(card.subtitle)}. {escape(BOUNDARY_FOOTER_TEXT)}</desc>
  <rect width="{CARD_WIDTH}" height="{CARD_HEIGHT}" fill="#f7f4ed"/>
  <rect x="0" y="0" width="{CARD_WIDTH}" height="18" fill="{card.accent}"/>
  <rect x="64" y="72" width="1152" height="552" rx="0" fill="#ffffff" stroke="#d7d1c5" stroke-width="2"/>
  <text x="92" y="124" font-size="22" font-weight="700" fill="{card.accent}">MACHLIB EVIDENCE REEL / CARD {position:02d}</text>
  {svg_text_lines(title_lines, x=92, y=194, size=54, fill="#191919", weight="700", line_height=60)}
  {svg_text_lines(subtitle_lines, x=96, y=292, size=28, fill="#4b4b4b", weight="500", line_height=36)}
  <line x1="96" y1="330" x2="1184" y2="330" stroke="#e3ded3" stroke-width="2"/>
  {svg_text_lines(bullet_lines, x=122, y=390, size=30, fill="#202020", weight="500", line_height=44)}
  <rect x="64" y="650" width="1152" height="42" fill="#252525"/>
  <text x="92" y="678" font-size="21" font-weight="600" fill="#ffffff">{BOUNDARY_FOOTER_VISIBLE}</text>
</svg>
'''


def render_index(cards: list[dict[str, str]]) -> str:
    links = "\n".join(
        f'        <li><a href="{escape(card["svg_path"])}">{escape(card["title"])}</a></li>'
        for card in cards
    )
    frames = "\n".join(
        f'      <iframe title="{escape(card["title"])}" src="{escape(card["svg_path"])}"></iframe>'
        for card in cards
    )
    return f"""<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>MachLib Evidence Reel Cards</title>
    <style>
      body {{ font-family: system-ui, sans-serif; margin: 32px; color: #191919; background: #f7f4ed; }}
      main {{ max-width: 960px; margin: 0 auto; }}
      iframe {{ width: 100%; aspect-ratio: 16 / 9; border: 1px solid #d7d1c5; background: white; margin: 16px 0 32px; }}
      a {{ color: #2457a6; }}
    </style>
  </head>
  <body>
    <main>
      <h1>MachLib Evidence Reel Cards</h1>
      <p>Local SVG preview only. No video, audio, upload, or deploy was generated.</p>
      <ol>
{links}
      </ol>
{frames}
    </main>
  </body>
</html>
"""


def build_manifest(cards: list[dict[str, str]], source_files: list[str]) -> dict[str, Any]:
    return {
        "reel_id": REEL_ID,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "card_count": len(cards),
        "cards": cards,
        "source_files": source_files,
        "no_video_generated": True,
        "no_audio_generated": True,
        "no_deploy_performed": True,
        "no_upload_performed": True,
        "no_public_claim": True,
    }


def write_reports(output_dir: Path, cards: list[dict[str, str]]) -> None:
    reports = Path("reports")
    reports.mkdir(parents=True, exist_ok=True)
    summary = reports / f"machlib_evidence_reel_card_renderer_summary_{DATE_TAG}.md"
    guardrail = reports / f"machlib_evidence_reel_card_renderer_guardrail_report_{DATE_TAG}.md"
    next_steps = reports / f"machlib_evidence_reel_card_renderer_next_steps_{DATE_TAG}.md"

    summary.write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel Card Renderer Summary",
                "",
                f"Rendered card count: {len(cards)}",
                f"Output directory: `{output_dir.as_posix()}`",
                "",
                "Outputs:",
                "- seven SVG cards",
                "- browser index preview",
                "- renderer manifest",
                "",
                "This is local product tooling for storyboard review.",
                "",
            ]
        )
    )
    guardrail.write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel Card Renderer Guardrail Report",
                "",
                "- no video generated",
                "- no audio generated",
                "- no deploy performed",
                "- no PyPI upload",
                "- no PyPI token handling",
                "- no package publish",
                "- no twine upload",
                "- no hardware action",
                "- no Forge compiler behavior change",
                "- no Hugging Face upload",
                "- no PETAL/API call",
                "- no public theorem/proof/open-problem claim",
                "- no Mathlib dependency introduced",
                "",
            ]
        )
    )
    next_steps.write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel Card Renderer Next Steps",
                "",
                "- review the local `index.html` preview",
                "- refine visual style if needed",
                "- keep video/audio rendering as a separate local task",
                "- keep Command Center mounting behind a separate review gate",
                "",
            ]
        )
    )


def render_cards(output_dir: Path = RENDER_ROOT) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)

    source_paths = [STORYBOARD_PATH, CARDS_PATH, SCRIPT_PATH, NARRATION_PATH]
    # Load the source files to fail early if the baseline reel packet is absent.
    for source in source_paths[:2]:
        if not load_json(source):
            raise SystemExit(f"missing or empty source file: {source}")
    for source in source_paths[2:]:
        if not source.exists() or not source.read_text():
            raise SystemExit(f"missing or empty source file: {source}")

    rendered_cards: list[dict[str, str]] = []
    for index, card in enumerate(RENDER_CARDS, start=1):
        path = output_dir / card.filename
        path.write_text(render_svg(card, index))
        rendered_cards.append(
            {
                "id": card.card_id,
                "title": card.title,
                "svg_path": card.filename,
            }
        )

    (output_dir / "index.html").write_text(render_index(rendered_cards))
    manifest = build_manifest(rendered_cards, [path.as_posix() for path in source_paths])
    (output_dir / f"render_manifest_{DATE_TAG}.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    write_reports(output_dir, rendered_cards)
    return manifest


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Render local SVG cards for the evidence reel.")
    parser.add_argument("--output-dir", type=Path, default=RENDER_ROOT)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    manifest = render_cards(args.output_dir)
    print("EVIDENCE_REEL_CARDS_RENDERED", manifest["card_count"])
    print("EVIDENCE_REEL_RENDER_DIR", args.output_dir)


if __name__ == "__main__":
    main()
