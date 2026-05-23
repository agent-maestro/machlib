import json
from pathlib import Path

from tools.operator_senses_factory import run


def ensure_gallery():
    run(Path("corpus/operator_senses_factory_2026_05_21"), 25, Path("."))


def test_manifest_exists():
    ensure_gallery()
    assert Path("senses/operator_senses_factory_2026_05_21/operator_senses_manifest_2026_05_21.json").exists()


def test_manifest_counts():
    ensure_gallery()
    manifest = json.loads(Path("senses/operator_senses_factory_2026_05_21/operator_senses_manifest_2026_05_21.json").read_text())
    assert manifest["kernel_count"] >= 25
    assert manifest["gallery_kernel_count"] >= 10


def test_html_has_controls():
    ensure_gallery()
    html = Path("senses/operator_senses_factory_2026_05_21/index.html").read_text()
    for text in ["Kernel", "Play", "Stop", "Mute", "Step sample"]:
        assert text in html


def test_js_uses_web_audio_no_microphone():
    ensure_gallery()
    js = Path("senses/operator_senses_factory_2026_05_21/operator_senses.js").read_text()
    assert "AudioContext" in js
    assert "getUserMedia" not in js


def test_manifest_boundaries():
    ensure_gallery()
    manifest = json.loads(Path("senses/operator_senses_factory_2026_05_21/operator_senses_manifest_2026_05_21.json").read_text())
    for key in ["audio_file_generated", "microphone_required", "hardware_required", "network_required", "deploy_performed", "upload_performed", "public_claim"]:
        assert manifest[key] is False


def test_boundary_copy_present():
    ensure_gallery()
    html = Path("senses/operator_senses_factory_2026_05_21/index.html").read_text()
    assert "Not theorem/proof/open-problem claims" in html
    assert "No microphone" in html


def test_data_file_has_ten_gallery_kernels():
    ensure_gallery()
    data = json.loads(Path("senses/operator_senses_factory_2026_05_21/operator_senses_data_2026_05_21.json").read_text())
    assert len(data["kernels"]) >= 10


def test_positive_and_negative_a_in_gallery():
    ensure_gallery()
    data = json.loads(Path("senses/operator_senses_factory_2026_05_21/operator_senses_data_2026_05_21.json").read_text())
    assert any(row["a"] > 0 for row in data["kernels"])
    assert any(row["a"] < 0 for row in data["kernels"])


def test_capcard_candidates_generated():
    ensure_gallery()
    data = json.loads(Path("product_readiness/operator_senses_capcard_candidates_2026_05_21.json").read_text())
    assert data["candidate_count"] >= 10


def test_operator_assessment_generated():
    ensure_gallery()
    data = json.loads(Path("product_readiness/operator_senses_product_assessment_2026_05_21.json").read_text())
    assert data["verdict"] in ["BUILD_OPERATOR_SENSES_LAB", "KEEP_AS_TOY_KERNEL", "FOLD_INTO_1OP_SENSES", "PAUSE"]
