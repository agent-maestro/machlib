import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_convolution_root_union_packet_v5_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_convolution_root_union_packet_v5_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_CONVOLUTION_ROOT_UNION_PACKET_V5_READY"
    assert data["primitive_count"] >= 7
    assert data["checked_result_count"] >= 12
    assert data["bridge_axiom_count"] == 1
    assert data["degree_arithmetic_status"] == "BASE_CASE_CHECKED_GENERAL_TARGET_DEFINED_NOT_PROVED"
    assert data["root_list_union_status"] == "SOUNDNESS_CHECKED_DISTINCTNESS_CARDINALITY_NOT_PROVED"
    assert data["general_root_count_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_convolution_root_union_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for primitive in data["primitives"]:
        assert primitive["lean_name"].split(".")[-1] in lean_text
    for result in data["checked_results"]:
        assert result["lean_name"].split(".")[-1] in lean_text


def test_convolution_root_union_contains_core_layers():
    lean_text = LEAN.read_text()
    for expected in [
        "addCoeff",
        "scalarMulCoeff",
        "shiftCoeff",
        "mulCoeff",
        "eval_mulCoeff",
        "mulCoeff_evalSound",
        "insertUniqueRoot",
        "unionUniqueRoots",
        "productRootListSound_union",
        "mulCoeffRootListSound_union",
        "ProductDegreeBoundTarget",
        "productDegreeBound_nil_left",
    ]:
        assert expected in lean_text


def test_convolution_root_union_keeps_single_explicit_bridge_axiom():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == ["axiom mul_eq_zero_or_left_or_right"]


def test_convolution_root_union_has_no_sorry():
    assert "sorry" not in LEAN.read_text()
