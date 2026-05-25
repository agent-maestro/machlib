import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAYLOAD = ROOT / "product_readiness" / "machlib_polynomial_evidence_v1_2026_05_25.json"
CARD = ROOT / "product_readiness" / "machlib_polynomial_evidence_explorer_card_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "PolynomialEvidence.lean"


def test_polynomial_evidence_payload_shape():
    data = json.loads(PAYLOAD.read_text())
    assert data["status"] == "MACHLIB_POLYNOMIAL_EVIDENCE_V1_READY"
    assert data["fact_count"] >= 5
    assert data["analytic_identity_theorem_status"] == "BLOCKED_NEEDS_ANALYTIC_SUBSTRATE"
    assert data["public_ready"] is False
    assert data["marketplace_ready"] is False
    assert data["public_theorem_claim"] is False


def test_polynomial_evidence_lean_names_exist():
    data = json.loads(PAYLOAD.read_text())
    lean_text = LEAN.read_text()
    for fact in data["facts"]:
        assert fact["lean_name"].split(".")[-1] in lean_text
        assert fact["evidence_class"] == "MACHLIB_CHECKED"


def test_polynomial_evidence_card_is_internal_only():
    card = json.loads(CARD.read_text())
    assert card["status"] == "INTERNAL_PROTOTYPE"
    assert card["boundaries"]["public_ready"] is False
    assert card["boundaries"]["public_theorem_claim"] is False


def test_no_new_axiom_or_sorry_in_polynomial_module():
    text = LEAN.read_text()
    assert "axiom " not in text
    assert "sorry" not in text
