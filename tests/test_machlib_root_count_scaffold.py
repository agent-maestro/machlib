import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = (
    ROOT
    / "product_readiness"
    / "machlib_polynomial_root_count_scaffold_v1_2026_05_25.json"
)
LEAN = ROOT / "foundations" / "MachLib" / "PolynomialRootCount.lean"
TOP = ROOT / "foundations" / "MachLib.lean"


def test_root_count_scaffold_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_POLYNOMIAL_ROOT_COUNT_SCAFFOLD_V1_READY"
    assert data["primitive_count"] >= 4
    assert data["checked_foothold_count"] >= 3
    assert data["tiny_root_count_result"] == "LINEAR_FACTOR_HAS_NO_DISTINCT_ROOT_PAIR"
    assert data["general_root_count_theorem_proved"] is False
    assert data["analytic_identity_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_root_count_scaffold_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for primitive in data["primitives"]:
        assert primitive["lean_name"].split(".")[-1] in lean_text
    for foothold in data["checked_footholds"]:
        assert foothold["lean_name"].split(".")[-1] in lean_text
        assert foothold["evidence_class"] == "MACHLIB_CHECKED"


def test_root_count_module_is_imported():
    assert "import MachLib.PolynomialRootCount" in TOP.read_text()


def test_no_new_axiom_or_sorry_in_root_count_module():
    text = LEAN.read_text()
    assert "axiom " not in text
    assert "sorry" not in text
