import json
from pathlib import Path

from tools.build_evidence_reel_html_player import BOUNDARY_FOOTER, build_player


def test_html_player_outputs_exist(tmp_path: Path) -> None:
    output_dir = tmp_path / "player"
    reports_dir = tmp_path / "reports"
    build_player(output_dir, reports_dir)

    assert (output_dir / "index.html").exists()
    assert (output_dir / "reel.css").exists()
    assert (output_dir / "reel.js").exists()
    assert (output_dir / "player_manifest_2026_05_21.json").exists()


def test_html_player_manifest_guardrails(tmp_path: Path) -> None:
    output_dir = tmp_path / "player"
    build_player(output_dir, tmp_path / "reports")
    manifest = json.loads((output_dir / "player_manifest_2026_05_21.json").read_text())

    assert manifest["card_count"] == 7
    assert manifest["static_html_generated"] is True
    assert manifest["video_generated"] is False
    assert manifest["audio_generated"] is False
    assert manifest["deploy_performed"] is False
    assert manifest["upload_performed"] is False
    assert manifest["network_required"] is False
    assert manifest["no_public_claim"] is True


def test_html_player_references_all_cards_and_controls(tmp_path: Path) -> None:
    output_dir = tmp_path / "player"
    build_player(output_dir, tmp_path / "reports")
    html = (output_dir / "index.html").read_text()

    for index in range(1, 8):
        assert f"card_{index:02d}_" in (output_dir / "reel.js").read_text()
    assert "Previous" in html
    assert "Pause" in html
    assert "Next" in html
    assert BOUNDARY_FOOTER in html
    assert "No upload, no deploy, no public proof claim" in html


def test_html_player_no_forbidden_positive_claims(tmp_path: Path) -> None:
    output_dir = tmp_path / "player"
    build_player(output_dir, tmp_path / "reports")
    text = "\n".join(path.read_text(errors="ignore") for path in output_dir.glob("*") if path.is_file())

    forbidden = [
        "theorem " + "proved",
        "open problem " + "solved",
        "MachLib replaces " + "mathlib",
    ]
    for phrase in forbidden:
        assert phrase not in text
