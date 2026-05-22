import json
from pathlib import Path

from tools.build_evidence_reel_video import build_video


def test_video_builder_writes_manifests(tmp_path: Path) -> None:
    manifest = build_video(tmp_path / "video")

    video_manifest = tmp_path / "video" / "video_manifest_2026_05_21.json"
    frame_manifest = tmp_path / "video" / "frame_manifest_2026_05_21.json"
    preview = tmp_path / "video" / "preview.html"

    assert video_manifest.exists()
    assert frame_manifest.exists()
    assert preview.exists()
    assert manifest["card_count"] == 7


def test_video_manifest_guardrails(tmp_path: Path) -> None:
    build_video(tmp_path / "video")
    manifest = json.loads((tmp_path / "video" / "video_manifest_2026_05_21.json").read_text())

    assert manifest["card_count"] == 7
    assert manifest["no_audio_generated"] is True
    assert manifest["no_upload_performed"] is True
    assert manifest["no_deploy_performed"] is True
    assert manifest["no_public_claim"] is True

    if manifest["video_status"] == "PASS":
        assert manifest["mp4_generated"] is True
        assert Path(manifest["mp4_path"]).exists()
    else:
        assert manifest["video_status"] == "BLOCKED_BY_LOCAL_TOOLING"
        assert manifest["missing_tools"]


def test_frame_manifest_lists_seven_cards(tmp_path: Path) -> None:
    build_video(tmp_path / "video")
    frame_manifest = json.loads((tmp_path / "video" / "frame_manifest_2026_05_21.json").read_text())

    assert len(frame_manifest["frames"]) == 7
    assert frame_manifest["no_upload_performed"] is True
    for row in frame_manifest["frames"]:
        assert row["duration_seconds"] == 4
        assert row["source_svg"].endswith(".svg")


def test_video_outputs_avoid_forbidden_positive_claims(tmp_path: Path) -> None:
    build_video(tmp_path / "video")
    text = "\n".join(
        path.read_text(errors="ignore")
        for path in (tmp_path / "video").glob("*")
        if path.is_file()
    )

    forbidden = [
        "theorem " + "proved",
        "open problem " + "solved",
        "MachLib replaces " + "mathlib",
    ]
    for phrase in forbidden:
        assert phrase not in text
