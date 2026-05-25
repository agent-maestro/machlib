import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAYLOAD = (
    ROOT
    / "product_readiness"
    / "machlib_analytic_identity_feasibility_2026_05_25.json"
)
LEAN = ROOT / "foundations" / "MachLib" / "AnalyticIdentityFeasibility.lean"


def test_feasibility_payload_is_blocked_not_claimed():
    data = json.loads(PAYLOAD.read_text())
    assert data["status"] == "FEASIBILITY_BLOCKED_NEEDS_ANALYTIC_SUBSTRATE"
    assert data["analytic_identity_theorem_proved"] is False
    assert data["public_theorem_claim"] is False
    assert data["public_ready"] is False
    assert data["marketplace_ready"] is False


def test_required_concepts_are_explicitly_missing():
    data = json.loads(PAYLOAD.read_text())
    statuses = {item["name"]: item["status"] for item in data["required_concepts"]}
    assert statuses["zero_set"] == "MISSING_SET_SUBSTRATE"
    assert statuses["accumulation_point"] == "MISSING_TOPOLOGY_LIMIT_SUBSTRATE"
    assert statuses["analytic"] == "MISSING_POWER_SERIES_SUBSTRATE"


def test_checked_footholds_exist_in_lean_file():
    data = json.loads(PAYLOAD.read_text())
    lean_text = LEAN.read_text()
    assert len(data["checked_footholds"]) == 3
    for item in data["checked_footholds"]:
        name = item["lean_name"].split(".")[-1]
        assert name in lean_text
        assert item["evidence_class"] == "MACHLIB_CHECKED"


def test_no_new_axiom_or_sorry_in_feasibility_module():
    text = LEAN.read_text()
    assert "axiom " not in text
    assert "sorry" not in text
