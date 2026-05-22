"""Build a local browser-playable MachLib evidence reel.

The player is static HTML/CSS/JS. It references the already-rendered SVG cards,
adds playback controls, and records no-upload/no-deploy guardrails.
"""

from __future__ import annotations

import argparse
import json
from datetime import datetime, timezone
from html import escape
from pathlib import Path
from typing import Any


DATE_TAG = "2026_05_21"
REEL_ID = f"machlib_package_reel_{DATE_TAG}"
PLAYER_DIR = Path("evidence_reels/player") / REEL_ID
RENDER_DIR = Path("evidence_reels/rendered") / REEL_ID
VIDEO_DIR = Path("evidence_reels/video") / REEL_ID
NARRATION_PATH = Path("evidence_reels") / f"machlib_package_reel_narration_{DATE_TAG}.md"
RENDER_MANIFEST_PATH = RENDER_DIR / f"render_manifest_{DATE_TAG}.json"
VIDEO_MANIFEST_PATH = VIDEO_DIR / f"video_manifest_{DATE_TAG}.json"
BOUNDARY_FOOTER = "Pre-alpha evidence tooling — not a theorem/proof/safety claim."


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"missing JSON source: {path}")
    return json.loads(path.read_text())


def read_narration(path: Path = NARRATION_PATH) -> str:
    if not path.exists():
        return ""
    return path.read_text()


def narration_sections(markdown: str) -> list[dict[str, str]]:
    sections: list[dict[str, str]] = []
    current_title = ""
    current_lines: list[str] = []
    for raw_line in markdown.splitlines():
        line = raw_line.strip()
        if line.startswith("## "):
            if current_title:
                sections.append({"title": current_title, "text": " ".join(current_lines).strip()})
            current_title = line.removeprefix("## ").strip()
            current_lines = []
        elif current_title and line and not line.startswith("#"):
            current_lines.append(line)
    if current_title:
        sections.append({"title": current_title, "text": " ".join(current_lines).strip()})
    return sections


def player_cards(render_manifest: dict[str, Any]) -> list[dict[str, str]]:
    cards = []
    for card in render_manifest.get("cards", []):
        cards.append(
            {
                "id": card["id"],
                "title": card["title"],
                "svg_path": f"../../rendered/{REEL_ID}/{card['svg_path']}",
            }
        )
    return cards


def write_css(path: Path) -> None:
    path.write_text(
        """html {
  background: #111;
  color: #f5f1e9;
  font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
}

body {
  margin: 0;
  min-height: 100vh;
  background: #151515;
}

.shell {
  max-width: 1120px;
  margin: 0 auto;
  padding: 24px;
}

.topbar,
.controls,
.footer {
  display: flex;
  align-items: center;
  justify-content: space-between;
  gap: 16px;
  flex-wrap: wrap;
}

.eyebrow {
  color: #d8c38b;
  font-size: 12px;
  font-weight: 700;
  letter-spacing: 0.12em;
  text-transform: uppercase;
}

h1 {
  margin: 6px 0 16px;
  font-size: 32px;
}

.stage {
  background: #050505;
  border: 1px solid #3a3428;
  aspect-ratio: 16 / 9;
  width: 100%;
  overflow: hidden;
}

.stage img {
  display: block;
  width: 100%;
  height: 100%;
  object-fit: contain;
  background: #f7f4ed;
}

.controls {
  margin: 18px 0;
}

button {
  background: #f2efe7;
  border: 1px solid #80745c;
  color: #171717;
  cursor: pointer;
  font-size: 15px;
  font-weight: 700;
  padding: 10px 14px;
}

button:hover,
button:focus {
  background: #fff7df;
}

.progress-wrap {
  flex: 1;
  min-width: 220px;
}

.progress {
  background: #3a3428;
  height: 10px;
  overflow: hidden;
}

.progress span {
  background: #d8c38b;
  display: block;
  height: 100%;
  width: 0%;
}

.meta,
.boundary {
  color: #cfc6b5;
  font-size: 14px;
}

.narration {
  background: #201f1c;
  border: 1px solid #3a3428;
  margin-top: 18px;
  padding: 18px;
}

.narration h2 {
  margin: 0 0 8px;
  font-size: 20px;
}

.narration p {
  color: #e8e1d2;
  line-height: 1.5;
  margin: 0;
}

.footer {
  border-top: 1px solid #3a3428;
  margin-top: 24px;
  padding-top: 16px;
}
"""
    )


def write_js(path: Path, cards: list[dict[str, str]], narration: list[dict[str, str]]) -> None:
    payload = {
        "cards": cards,
        "narration": narration,
        "durationMs": 4000,
    }
    path.write_text(
        "const REEL = "
        + json.dumps(payload, indent=2)
        + """;

let current = 0;
let playing = true;
let timer = null;

const cardImage = document.querySelector("[data-card-image]");
const cardTitle = document.querySelector("[data-card-title]");
const cardCounter = document.querySelector("[data-card-counter]");
const narrationTitle = document.querySelector("[data-narration-title]");
const narrationText = document.querySelector("[data-narration-text]");
const progress = document.querySelector("[data-progress]");
const playPause = document.querySelector("[data-play-pause]");

function sectionFor(index) {
  return REEL.narration[index] || { title: REEL.cards[index].title, text: "" };
}

function render() {
  const card = REEL.cards[current];
  const section = sectionFor(current);
  cardImage.src = card.svg_path;
  cardImage.alt = card.title;
  cardTitle.textContent = card.title;
  cardCounter.textContent = `${current + 1} / ${REEL.cards.length}`;
  narrationTitle.textContent = section.title;
  narrationText.textContent = section.text;
  progress.style.width = `${((current + 1) / REEL.cards.length) * 100}%`;
}

function next() {
  current = (current + 1) % REEL.cards.length;
  render();
}

function previous() {
  current = (current - 1 + REEL.cards.length) % REEL.cards.length;
  render();
}

function stopTimer() {
  if (timer) {
    window.clearInterval(timer);
    timer = null;
  }
}

function startTimer() {
  stopTimer();
  timer = window.setInterval(next, REEL.durationMs);
}

function setPlaying(value) {
  playing = value;
  playPause.textContent = playing ? "Pause" : "Play";
  if (playing) {
    startTimer();
  } else {
    stopTimer();
  }
}

document.querySelector("[data-next]").addEventListener("click", () => {
  next();
  if (playing) startTimer();
});

document.querySelector("[data-prev]").addEventListener("click", () => {
  previous();
  if (playing) startTimer();
});

playPause.addEventListener("click", () => setPlaying(!playing));

render();
setPlaying(true);
"""
    )


def write_index(path: Path, cards: list[dict[str, str]]) -> None:
    first = cards[0]
    path.write_text(
        f"""<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>MachLib Evidence Reel Player</title>
    <link rel="stylesheet" href="reel.css">
  </head>
  <body>
    <main class="shell">
      <header class="topbar">
        <div>
          <div class="eyebrow">Local static reel</div>
          <h1>MachLib Evidence Reel</h1>
        </div>
        <div class="meta">No upload, no deploy, no public proof claim</div>
      </header>

      <section class="stage" aria-label="Evidence reel card">
        <img data-card-image src="{escape(first['svg_path'])}" alt="{escape(first['title'])}">
      </section>

      <section class="controls" aria-label="Reel controls">
        <button type="button" data-prev>Previous</button>
        <button type="button" data-play-pause>Pause</button>
        <button type="button" data-next>Next</button>
        <div class="progress-wrap" aria-label="Progress">
          <div class="progress"><span data-progress></span></div>
        </div>
        <div class="meta"><span data-card-title>{escape(first['title'])}</span> · <span data-card-counter>1 / {len(cards)}</span></div>
      </section>

      <section class="narration" aria-label="Narration text">
        <h2 data-narration-title></h2>
        <p data-narration-text></p>
      </section>

      <footer class="footer">
        <span class="boundary">{BOUNDARY_FOOTER}</span>
        <span class="meta">Static HTML/CSS/JS only</span>
      </footer>
    </main>
    <script src="reel.js"></script>
  </body>
</html>
"""
    )


def write_reports(output_dir: Path, reports_dir: Path, manifest: dict[str, Any]) -> None:
    reports_dir.mkdir(parents=True, exist_ok=True)
    (reports_dir / f"machlib_evidence_reel_html_player_summary_{DATE_TAG}.md").write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel HTML Player Summary",
                "",
                f"Player status: `{manifest['player_status']}`",
                f"Card count: {manifest['card_count']}",
                f"Player path: `{(output_dir / 'index.html').as_posix()}`",
                "",
                "The player is static HTML/CSS/JS and references the rendered SVG cards locally.",
                "",
            ]
        )
    )
    (reports_dir / f"machlib_evidence_reel_html_player_guardrail_report_{DATE_TAG}.md").write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel HTML Player Guardrail Report",
                "",
                "- no PyPI upload",
                "- no PyPI token handling",
                "- no package publish",
                "- no twine upload",
                "- no deploy",
                "- no upload",
                "- no video generated",
                "- no audio generated",
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
    (reports_dir / f"machlib_evidence_reel_html_player_next_steps_{DATE_TAG}.md").write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel HTML Player Next Steps",
                "",
                "- review the local player in a browser",
                "- consider Command Center static snapshot mounting under a separate approval",
                "- keep audio/video generation as separate local tasks",
                "- keep deploy and upload gates closed until explicitly approved",
                "",
            ]
        )
    )


def build_player(output_dir: Path = PLAYER_DIR, reports_dir: Path = Path("reports")) -> dict[str, Any]:
    render_manifest = load_json(RENDER_MANIFEST_PATH)
    video_manifest = load_json(VIDEO_MANIFEST_PATH)
    cards = player_cards(render_manifest)
    if len(cards) != 7:
        raise SystemExit("expected seven rendered cards")

    output_dir.mkdir(parents=True, exist_ok=True)
    narration = narration_sections(read_narration())
    write_css(output_dir / "reel.css")
    write_js(output_dir / "reel.js", cards, narration)
    write_index(output_dir / "index.html", cards)

    manifest = {
        "reel_id": REEL_ID,
        "player_status": "PASS",
        "card_count": len(cards),
        "static_html_generated": True,
        "video_generated": False,
        "audio_generated": False,
        "deploy_performed": False,
        "upload_performed": False,
        "network_required": False,
        "no_public_claim": True,
        "source_render_manifest": RENDER_MANIFEST_PATH.as_posix(),
        "source_video_manifest": VIDEO_MANIFEST_PATH.as_posix(),
        "source_video_status": video_manifest.get("video_status"),
        "cards": cards,
        "generated_at": datetime.now(timezone.utc).isoformat(),
    }
    (output_dir / f"player_manifest_{DATE_TAG}.json").write_text(
        json.dumps(manifest, indent=2, sort_keys=True) + "\n"
    )
    write_reports(output_dir, reports_dir, manifest)
    return manifest


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a static MachLib evidence reel HTML player.")
    parser.add_argument("--output-dir", type=Path, default=PLAYER_DIR)
    parser.add_argument("--reports-dir", type=Path, default=Path("reports"))
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    manifest = build_player(args.output_dir, args.reports_dir)
    print("EVIDENCE_REEL_HTML_PLAYER", manifest["player_status"], manifest["card_count"])
    print("EVIDENCE_REEL_HTML_PLAYER_PATH", args.output_dir / "index.html")


if __name__ == "__main__":
    main()
