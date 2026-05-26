import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_root_union_degree_packet_v6_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_root_union_degree_packet_v6_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_ROOT_UNION_DEGREE_PACKET_V6_READY"
    assert data["checked_result_count"] >= 8
    assert data["bridge_axiom_count"] == 0
    assert data["root_list_distinctness_status"] == "CHECKED_FOR_UNIQUE_UNION"
    assert data["root_list_cardinality_status"] == "CHECKED_UNION_LENGTH_LE_FACTOR_LENGTH_SUM"
    assert data["product_degree_growth_status"] == "CERTIFICATE_INTERFACE_DEFINED_NOT_CONSTRUCTED"
    assert data["general_root_count_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_root_union_degree_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for primitive in data["primitives"]:
        assert primitive["lean_name"].split(".")[-1] in lean_text
    for result in data["checked_results"]:
        assert result["lean_name"].split(".")[-1] in lean_text


def test_root_union_degree_contains_distinctness_cardinality_and_cert_layers():
    lean_text = LEAN.read_text()
    for expected in [
        "ProductDegreeBoundCert",
        "ProductDegreeGrowthCert",
        "RootListDistinct_insertUniqueRoot",
        "RootListDistinct_unionUniqueRoots",
        "length_insertUniqueRoot_le_succ",
        "length_insertUniqueRoot_eq_of_mem",
        "length_unionUniqueRoots_le_add",
        "productRootListDistinct_union",
        "productRootListLength_union_le_add",
        "productRootListDegreeBound_union_of_cert",
    ]:
        assert expected in lean_text


def test_root_union_degree_uses_derived_zero_product_theorem():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "theorem mul_eq_zero_or_left_or_right" in lean_text


def test_root_union_degree_has_no_sorry():
    assert "sorry" not in LEAN.read_text()
