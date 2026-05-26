import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_product_root_bridge_packet_v4_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_product_root_bridge_packet_v4_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_PRODUCT_ROOT_BRIDGE_PACKET_V4_READY"
    assert data["primitive_count"] >= 3
    assert data["checked_result_count"] >= 7
    assert data["bridge_axiom_count"] == 0
    assert data["general_root_count_theorem_proved"] is False
    assert data["analytic_identity_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_product_root_bridge_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for primitive in data["primitives"]:
        assert primitive["lean_name"].split(".")[-1] in lean_text
    for result in data["checked_results"]:
        assert result["lean_name"].split(".")[-1] in lean_text


def test_product_root_bridge_has_derived_zero_product_theorem():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "theorem mul_eq_zero_or_left_or_right" in lean_text


def test_product_root_bridge_contains_linear_and_product_layers():
    lean_text = LEAN.read_text()
    for expected in [
        "linearCoeff",
        "MulEvalSound",
        "eval_linearCoeff_eq_linearFactor",
        "linearCoeff_root_iff_linearFactor_root",
        "productRoot_split",
        "productRoot_right_of_left_nonroot",
        "productRoot_left_of_right_nonroot",
    ]:
        assert expected in lean_text


def test_product_root_bridge_has_no_sorry():
    assert "sorry" not in LEAN.read_text()
