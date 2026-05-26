import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_exact_product_degree_normalizer_packet_v8_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_v8_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_EXACT_PRODUCT_DEGREE_NORMALIZER_PACKET_V8_READY"
    assert data["bridge_axiom_count"] == 0
    assert data["targeted_example_class_count"] >= 5
    assert data["targeted_example_count"] >= 25
    assert data["root_packet_example_count"] >= 5
    assert data["general_root_count_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_v8_each_example_class_has_five_examples():
    data = json.loads(PACKET.read_text())
    for examples in data["targeted_examples"].values():
        assert len(examples) >= 5


def test_v8_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for name in data["normalizer_layer"]["checked_results"]:
        assert name in lean_text
    for examples in data["targeted_examples"].values():
        for name in examples:
            assert f"theorem {name}" in lean_text
    for item in data["root_packet_examples"]:
        assert f"theorem {item['lean_name']}" in lean_text


def test_v8_no_new_axioms_or_sorry():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "sorry" not in lean_text


def test_v8_boundaries_false():
    data = json.loads(PACKET.read_text())
    for key in [
        "general_root_count_theorem_proved",
        "analytic_identity_theorem_proved",
        "public_theorem_claim",
        "marketplace_ready",
        "public_ready",
        "production_marketplace_modified",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "package_publish_performed",
        "certified_safety_claim",
        "production_controller_claim",
    ]:
        assert data[key] is False
