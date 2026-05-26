import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_product_induction_bridge_packet_v9_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_v9_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_PRODUCT_INDUCTION_BRIDGE_PACKET_V9_READY"
    assert data["checked_bridge_count"] >= 7
    assert data["target_count"] >= 2
    assert data["bridge_axiom_count"] == 0
    assert data["general_root_count_theorem_proved"] is False
    assert data["arbitrary_normalized_product_degree_growth_proved"] is False
    assert data["normalize_eval_soundness_proved"] is False
    assert data["public_theorem_claim"] is False


def test_v9_checked_bridge_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for item in data["checked_bridges"]:
        assert item["lean_name"] in lean_text
    for item in data["targets_named"]:
        assert item["lean_name"] in lean_text


def test_v9_packet_constructors_are_real_definitions():
    lean_text = LEAN.read_text()
    for name in [
        "linearLinearFiniteRootPacket",
        "repeatedLinearFiniteRootPacket",
        "scaledLinearFiniteRootPacket",
        "stagedTripleLinearFiniteRootPacket",
        "linearQuadraticFiniteRootPacketWithCertificate",
        "mulCoeffFiniteRootPacketWithDegreeGrowthCert",
    ]:
        assert f"def {name}" in lean_text


def test_v9_no_new_axioms_or_sorry():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "sorry" not in lean_text


def test_v9_boundaries_false():
    data = json.loads(PACKET.read_text())
    for key in [
        "general_root_count_theorem_proved",
        "arbitrary_normalized_product_degree_growth_proved",
        "normalize_eval_soundness_proved",
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
