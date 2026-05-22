"""Build a local MP4 slideshow prototype for the MachLib evidence reel.

The builder is local-only and resilient: if SVG conversion or ffmpeg is not
available, it writes manifests, a preview page, and exact blocker details
instead of failing the product-readiness task.
"""

from __future__ import annotations

import argparse
import json
import shutil
import subprocess
from datetime import datetime, timezone
from html import escape
from pathlib import Path
from typing import Any


DATE_TAG = "2026_05_21"
REEL_ID = f"machlib_package_reel_{DATE_TAG}"
CARD_DURATION_SECONDS = 4
RENDER_DIR = Path("evidence_reels/rendered") / REEL_ID
VIDEO_DIR = Path("evidence_reels/video") / REEL_ID
FRAMES_DIRNAME = "frames"
MP4_FILENAME = f"{REEL_ID}.mp4"
BOUNDARY_FOOTER = "Pre-alpha evidence tooling - not a theorem/proof/open-problem claim."
NOT_CLAIMED = [
    "not a theorem/proof/open-problem claim",
    "not certified safety",
    "not production controller evidence",
    "not a Mathlib replacement",
]


def load_json(path: Path) -> dict[str, Any]:
    if not path.exists():
        raise SystemExit(f"missing JSON source: {path}")
    return json.loads(path.read_text())


def tool_status() -> dict[str, bool]:
    cairosvg_available = False
    try:
        import cairosvg  # noqa: F401

        cairosvg_available = True
    except Exception:
        cairosvg_available = False
    return {
        "ffmpeg": shutil.which("ffmpeg") is not None,
        "rsvg_convert": shutil.which("rsvg-convert") is not None,
        "cairosvg": cairosvg_available,
    }


def missing_tools(status: dict[str, bool]) -> list[str]:
    missing: list[str] = []
    if not (status["cairosvg"] or status["rsvg_convert"]):
        missing.append("cairosvg_or_rsvg-convert")
    if not status["ffmpeg"]:
        missing.append("ffmpeg")
    return missing


def convert_svg_to_png(svg_path: Path, png_path: Path, status: dict[str, bool]) -> None:
    if status["cairosvg"]:
        import cairosvg

        cairosvg.svg2png(url=str(svg_path), write_to=str(png_path), output_width=1280, output_height=720)
        return
    if status["rsvg_convert"]:
        subprocess.run(
            ["rsvg-convert", "-w", "1280", "-h", "720", "-o", str(png_path), str(svg_path)],
            check=True,
        )
        return
    raise RuntimeError("no SVG-to-PNG converter available")


def build_mp4(frame_paths: list[Path], mp4_path: Path) -> None:
    concat_file = mp4_path.parent / "ffmpeg_concat_2026_05_21.txt"
    lines: list[str] = []
    for frame in frame_paths:
        lines.append(f"file '{frame.resolve().as_posix()}'")
        lines.append(f"duration {CARD_DURATION_SECONDS}")
    # ffmpeg's concat demuxer needs the last frame listed again.
    if frame_paths:
        lines.append(f"file '{frame_paths[-1].resolve().as_posix()}'")
    concat_file.write_text("\n".join(lines) + "\n")
    subprocess.run(
        [
            "ffmpeg",
            "-y",
            "-f",
            "concat",
            "-safe",
            "0",
            "-i",
            str(concat_file),
            "-vf",
            "fps=30,format=yuv420p",
            str(mp4_path),
        ],
        check=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )


def frame_rows(manifest: dict[str, Any], frames_dir: Path, frames_generated: bool) -> list[dict[str, Any]]:
    rows = []
    for index, card in enumerate(manifest.get("cards", []), start=1):
        frame_name = f"frame_{index:02d}.png"
        rows.append(
            {
                "card_id": card["id"],
                "title": card["title"],
                "source_svg": (RENDER_DIR / card["svg_path"]).as_posix(),
                "frame_png": (frames_dir / frame_name).as_posix() if frames_generated else null_path(),
                "duration_seconds": CARD_DURATION_SECONDS,
                "no_upload_performed": True,
            }
        )
    return rows


def null_path() -> None:
    return None


def write_preview(output_dir: Path, video_manifest: dict[str, Any], frame_manifest: dict[str, Any]) -> None:
    mp4_path = video_manifest.get("mp4_path")
    video_block = ""
    if video_manifest.get("mp4_generated") and mp4_path:
        video_block = f'<video controls width="960" src="{escape(Path(mp4_path).name)}"></video>'
    else:
        tools = ", ".join(video_manifest.get("missing_tools", [])) or "none"
        video_block = f"<p><strong>MP4 not generated.</strong> Missing local tooling: {escape(tools)}.</p>"

    cards = "\n".join(
        f'<li><a href="../../rendered/{REEL_ID}/{escape(Path(row["source_svg"]).name)}">{escape(row["title"])}</a></li>'
        for row in frame_manifest["frames"]
    )
    html = f"""<!doctype html>
<html lang="en">
  <head>
    <meta charset="utf-8">
    <meta name="viewport" content="width=device-width, initial-scale=1">
    <title>MachLib Evidence Reel Video Prototype</title>
    <style>
      body {{ font-family: system-ui, sans-serif; margin: 32px; background: #f7f4ed; color: #191919; }}
      main {{ max-width: 960px; margin: 0 auto; }}
      video {{ width: 100%; border: 1px solid #d7d1c5; background: #111; }}
      footer {{ margin-top: 32px; font-size: 14px; color: #555; }}
    </style>
  </head>
  <body>
    <main>
      <h1>MachLib Evidence Reel Video Prototype</h1>
      {video_block}
      <h2>Source cards</h2>
      <ol>
{cards}
      </ol>
      <footer>{escape(BOUNDARY_FOOTER)}</footer>
    </main>
  </body>
</html>
"""
    (output_dir / "preview.html").write_text(html)


def write_reports(output_dir: Path, video_manifest: dict[str, Any]) -> None:
    reports = Path("reports")
    reports.mkdir(parents=True, exist_ok=True)
    summary = reports / f"machlib_evidence_reel_video_summary_{DATE_TAG}.md"
    guardrail = reports / f"machlib_evidence_reel_video_guardrail_report_{DATE_TAG}.md"
    next_steps = reports / f"machlib_evidence_reel_video_next_steps_{DATE_TAG}.md"

    summary.write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel Video Summary",
                "",
                f"Video status: `{video_manifest['video_status']}`",
                f"Card count: {video_manifest['card_count']}",
                f"Frame count: {video_manifest['frame_count']}",
                f"MP4 generated: `{str(video_manifest['mp4_generated']).lower()}`",
                f"Output directory: `{output_dir.as_posix()}`",
                f"Missing tools: `{', '.join(video_manifest['missing_tools']) or 'none'}`",
                "",
                "This is local audiovisual product tooling only.",
                "",
            ]
        )
    )
    guardrail.write_text(
        "\n".join(
            [
                "# MachLib Evidence Reel Video Guardrail Report",
                "",
                "- no audio generated",
                "- no upload performed",
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
                "# MachLib Evidence Reel Video Next Steps",
                "",
                "- install local SVG conversion tooling if MP4 generation is blocked",
                "- install local ffmpeg if MP4 encoding is blocked",
                "- keep audio narration as a separate local task",
                "- keep upload and deploy gates closed unless separately approved",
                "",
            ]
        )
    )


def build_video(output_dir: Path = VIDEO_DIR) -> dict[str, Any]:
    output_dir.mkdir(parents=True, exist_ok=True)
    frames_dir = output_dir / FRAMES_DIRNAME
    frames_dir.mkdir(parents=True, exist_ok=True)

    render_manifest = load_json(RENDER_DIR / f"render_manifest_{DATE_TAG}.json")
    cards = render_manifest.get("cards", [])
    if len(cards) != 7:
        raise SystemExit("expected seven rendered source cards")

    status = tool_status()
    missing = missing_tools(status)
    frame_paths: list[Path] = []
    frames_generated = False
    mp4_generated = False
    mp4_path = output_dir / MP4_FILENAME

    if not missing or (status["cairosvg"] or status["rsvg_convert"]):
        try:
            for index, card in enumerate(cards, start=1):
                svg_path = RENDER_DIR / card["svg_path"]
                png_path = frames_dir / f"frame_{index:02d}.png"
                convert_svg_to_png(svg_path, png_path, status)
                frame_paths.append(png_path)
            frames_generated = len(frame_paths) == len(cards)
        except Exception as exc:
            missing.append(f"svg_conversion_failed:{type(exc).__name__}")
            frame_paths = []
            frames_generated = False

    if frames_generated and status["ffmpeg"]:
        try:
            build_mp4(frame_paths, mp4_path)
            mp4_generated = mp4_path.exists()
        except Exception as exc:
            missing.append(f"ffmpeg_failed:{type(exc).__name__}")
            mp4_generated = False

    video_status = "PASS" if mp4_generated else "BLOCKED_BY_LOCAL_TOOLING"
    frame_manifest = {
        "reel_id": REEL_ID,
        "frame_count": len(frame_paths) if frames_generated else 0,
        "frames": frame_rows(render_manifest, frames_dir, frames_generated),
        "no_upload_performed": True,
    }
    video_manifest = {
        "reel_id": REEL_ID,
        "video_status": video_status,
        "card_count": len(cards),
        "frame_count": len(frame_paths) if frames_generated else 0,
        "mp4_generated": mp4_generated,
        "mp4_path": mp4_path.as_posix() if mp4_generated else None,
        "no_audio_generated": True,
        "no_upload_performed": True,
        "no_deploy_performed": True,
        "no_public_claim": True,
        "missing_tools": sorted(set(missing)),
        "not_claimed": NOT_CLAIMED,
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "tooling": status,
    }

    (output_dir / f"frame_manifest_{DATE_TAG}.json").write_text(
        json.dumps(frame_manifest, indent=2, sort_keys=True) + "\n"
    )
    (output_dir / f"video_manifest_{DATE_TAG}.json").write_text(
        json.dumps(video_manifest, indent=2, sort_keys=True) + "\n"
    )
    write_preview(output_dir, video_manifest, frame_manifest)
    write_reports(output_dir, video_manifest)
    return video_manifest


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Build a local MachLib evidence reel video prototype.")
    parser.add_argument("--output-dir", type=Path, default=VIDEO_DIR)
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    manifest = build_video(args.output_dir)
    print("EVIDENCE_REEL_VIDEO_STATUS", manifest["video_status"])
    print("EVIDENCE_REEL_FRAME_COUNT", manifest["frame_count"])
    print("EVIDENCE_REEL_MP4_GENERATED", manifest["mp4_generated"])


if __name__ == "__main__":
    main()
