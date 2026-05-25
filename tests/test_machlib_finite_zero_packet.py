import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_finite_zero_packet_v1_2026_05_25.json"
FEASIBILITY = (
    ROOT
    / "product_readiness"
    / "machlib_polynomial_degree_root_count_feasibility_2026_05_25.json"
)
LEAN = ROOT / "foundations" / "MachLib" / "FiniteZeroPacket.lean"


def test_finite_zero_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_FINITE_ZERO_PACKET_V1_READY"
    assert data["sample_count"] >= 5
    assert data["analytic_identity_theorem_status"] == "BLOCKED_NEEDS_ANALYTIC_SUBSTRATE"
    assert data["public_ready"] is False
    assert data["public_theorem_claim"] is False


def test_finite_zero_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for sample in data["samples"]:
        assert sample["lean_name"].split(".")[-1] in lean_text
        assert sample["evidence_class"] == "MACHLIB_CHECKED"


def test_root_count_feasibility_is_blocked():
    data = json.loads(FEASIBILITY.read_text())
    assert data["status"] == "POLYNOMIAL_DEGREE_ROOT_COUNT_FEASIBILITY_BLOCKED"
    assert data["root_count_bound_proved"] is False
    assert data["analytic_identity_theorem_proved"] is False
    assert data["public_theorem_claim"] is False


def test_no_new_axiom_or_sorry_in_finite_zero_module():
    text = LEAN.read_text()
    assert "axiom " not in text
    assert "sorry" not in text
