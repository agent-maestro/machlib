import json
from pathlib import Path

from tools.render_evidence_reel_cards import BOUNDARY_FOOTER_TEXT, render_cards


def test_renderer_creates_seven_svg_cards(tmp_path: Path) -> None:
    output_dir = tmp_path / "rendered"
    manifest = render_cards(output_dir)

    svg_paths = sorted(output_dir.glob("card_*.svg"))
    assert len(svg_paths) == 7
    assert manifest["card_count"] == 7

    for path in svg_paths:
        text = path.read_text()
        assert "<svg" in text
        assert BOUNDARY_FOOTER_TEXT in text
        assert "role=\"img\"" in text


def test_renderer_index_links_all_cards(tmp_path: Path) -> None:
    output_dir = tmp_path / "rendered"
    render_cards(output_dir)

    index = output_dir / "index.html"
    assert index.exists()
    html = index.read_text()
    for path in sorted(output_dir.glob("card_*.svg")):
        assert path.name in html


def test_renderer_manifest_guardrails(tmp_path: Path) -> None:
    output_dir = tmp_path / "rendered"
    render_cards(output_dir)
    manifest_path = output_dir / "render_manifest_2026_05_21.json"

    manifest = json.loads(manifest_path.read_text())
    assert manifest["card_count"] == 7
    assert manifest["no_video_generated"] is True
    assert manifest["no_audio_generated"] is True
    assert manifest["no_deploy_performed"] is True
    assert manifest["no_upload_performed"] is True
    assert manifest["no_public_claim"] is True


def test_renderer_has_no_forbidden_positive_claims(tmp_path: Path) -> None:
    output_dir = tmp_path / "rendered"
    render_cards(output_dir)
    text = "\n".join(path.read_text() for path in output_dir.glob("*"))

    forbidden = [
        "theorem " + "proved",
        "open problem " + "solved",
        "MachLib replaces " + "mathlib",
    ]
    for phrase in forbidden:
        assert phrase not in text
