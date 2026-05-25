import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = (
    ROOT
    / "product_readiness"
    / "machlib_polynomial_root_count_packet_v2_2026_05_25.json"
)
LEAN = ROOT / "foundations" / "MachLib" / "PolynomialRootCount.lean"


def test_root_count_packet_v2_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_POLYNOMIAL_ROOT_COUNT_PACKET_V2_READY"
    assert data["primitive_count"] >= 8
    assert data["checked_result_count"] >= 8
    assert data["tiny_root_count_result"] == "LINEAR_FACTOR_FINITE_ROOT_PACKET_CHECKED"
    assert data["general_root_count_theorem_proved"] is False
    assert data["analytic_identity_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_root_count_packet_v2_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for primitive in data["primitives"]:
        assert primitive["lean_name"].split(".")[-1] in lean_text
    for result in data["checked_results"]:
        assert result["lean_name"].split(".")[-1] in lean_text
        assert result["evidence_class"] == "MACHLIB_CHECKED"


def test_root_count_packet_v2_includes_finite_root_packet_layer():
    lean_text = LEAN.read_text()
    for expected in [
        "RootListSound",
        "RootListDistinct",
        "RootListDegreeBound",
        "structure FiniteRootPacket",
        "linearFactorFiniteRootPacket",
    ]:
        assert expected in lean_text


def test_no_new_axiom_or_sorry_in_root_count_module_v2():
    text = LEAN.read_text()
    assert "axiom " not in text
    assert "sorry" not in text
