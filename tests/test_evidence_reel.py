from pathlib import Path

from tools.build_evidence_reel import (
    BOUNDARY_CLAIMS,
    PUBLISHED_PACKAGES,
    READY_PENDING_PACKAGES,
    TITLE,
    build_storyboard,
    write_outputs,
)


def test_storyboard_has_required_cards_and_packages() -> None:
    storyboard = build_storyboard({"available_inputs": [], "missing_inputs": []})

    assert storyboard["title"] == TITLE
    assert len(storyboard["cards"]) == 7

    card_titles = [card["title"] for card in storyboard["cards"]]
    assert card_titles == [
        "MachLib Evidence Tooling Update",
        "Published packages",
        "Ready / pending packages",
        "What passed",
        "What failed / paused",
        "What is not claimed",
        "Next actions",
    ]

    published_card = storyboard["cards"][1]
    pending_card = storyboard["cards"][2]
    assert published_card["on_screen_bullets"] == PUBLISHED_PACKAGES
    assert pending_card["on_screen_bullets"] == READY_PENDING_PACKAGES


def test_storyboard_uses_bounded_public_copy() -> None:
    storyboard = build_storyboard({"available_inputs": [], "missing_inputs": []})
    text = str(storyboard)

    forbidden_positive_phrases = [
        "theorem " + "proved",
        "open problem " + "solved",
        "MachLib replaces " + "mathlib",
        "CapCard certifies",
        "PETAL verifies",
    ]
    for phrase in forbidden_positive_phrases:
        assert phrase not in text

    for claim in BOUNDARY_CLAIMS:
        assert claim in text


def test_write_outputs_creates_reel_packet(tmp_path: Path) -> None:
    storyboard = build_storyboard({"available_inputs": ["sample.json"], "missing_inputs": []})
    outputs = write_outputs(storyboard, tmp_path / "evidence_reels", tmp_path / "reports")

    expected_paths = [
        outputs.storyboard_json,
        outputs.reel_script_md,
        outputs.narration_md,
        outputs.card_manifest_json,
        outputs.summary_md,
        outputs.guardrail_md,
        outputs.next_steps_md,
    ]
    for path in expected_paths:
        assert path.exists()
        assert path.read_text()

    assert "pre-alpha" in outputs.narration_md.read_text()
    assert "no PyPI token handling" in outputs.guardrail_md.read_text()
