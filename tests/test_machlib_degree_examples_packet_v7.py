import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_degree_examples_packet_v7_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_degree_examples_packet_v7_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_DEGREE_EXAMPLES_PACKET_V7_READY"
    assert data["bridge_axiom_count"] == 0
    assert data["degree_growth_example_count"] >= 5
    assert data["root_union_example_count"] >= 5
    assert data["zero_product_status"] == "DERIVED_THEOREM_NO_BRIDGE_AXIOM"
    assert data["general_root_count_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_degree_examples_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for result in data["checked_results"]:
        assert result["lean_name"].split(".")[-1] in lean_text
    for name in data["degree_growth_examples"]:
        assert f"theorem {name}" in lean_text
    for name in data["root_union_examples"]:
        assert f"theorem {name}" in lean_text


def test_zero_product_is_derived_not_axiom():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "theorem mul_eq_zero_or_left_or_right" in lean_text
    assert "mul_inv" in lean_text


def test_degree_examples_has_no_sorry():
    assert "sorry" not in LEAN.read_text()
