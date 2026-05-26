import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = (
    ROOT
    / "product_readiness"
    / "machlib_normalized_polynomial_root_count_packet_v3_2026_05_25.json"
)
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"
TOP = ROOT / "foundations" / "MachLib.lean"


def test_normalized_root_count_packet_v3_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_NORMALIZED_POLYNOMIAL_ROOT_COUNT_PACKET_V3_READY"
    assert data["primitive_count"] >= 6
    assert data["checked_result_count"] >= 8
    assert data["base_case_result"] == "NONZERO_CONSTANT_HAS_EMPTY_ROOT_PACKET"
    assert data["induction_target_status"] == "DEFINED_NOT_PROVED"
    assert data["general_root_count_theorem_proved"] is False
    assert data["analytic_identity_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_normalized_root_count_packet_v3_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for primitive in data["primitives"]:
        assert primitive["lean_name"].split(".")[-1] in lean_text
    for result in data["checked_results"]:
        assert result["lean_name"].split(".")[-1] in lean_text
        assert result["evidence_class"] == "MACHLIB_CHECKED"


def test_normalized_root_count_module_is_imported():
    assert "import MachLib.NormalizedPolynomialRootCount" in TOP.read_text()


def test_normalized_root_count_includes_induction_target_but_no_claim():
    lean_text = LEAN.read_text()
    assert "def RootCountInductionTarget" in lean_text
    assert "theorem RootCountInductionTarget" not in lean_text
    assert "general polynomial root-count theorem" in lean_text


def test_no_axiom_or_sorry_in_normalized_root_count_module():
    text = LEAN.read_text()
    axiom_lines = [line.strip() for line in text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "theorem mul_eq_zero_or_left_or_right" in text
    assert "sorry" not in text
