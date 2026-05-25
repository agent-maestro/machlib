import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PAYLOAD = ROOT / "product_readiness" / "machlib_proof_spine_v1_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "ProofSpine.lean"


def test_proof_spine_payload_shape():
    data = json.loads(PAYLOAD.read_text())
    assert data["status"] == "MACHLIB_PROOF_SPINE_V1_READY"
    assert data["obligation_count"] >= 10
    assert data["checked_count"] == data["obligation_count"]
    assert data["blocked_count"] == 0
    assert data["public_ready"] is False
    assert data["marketplace_ready"] is False
    assert data["production_marketplace_modified"] is False


def test_proof_spine_lean_names_exist():
    data = json.loads(PAYLOAD.read_text())
    lean_text = LEAN.read_text()
    for obligation in data["obligations"]:
        assert obligation["id"] in lean_text
        assert obligation["evidence_class"] == "MACHLIB_CHECKED"


def test_proof_spine_surfaces_are_mapped():
    data = json.loads(PAYLOAD.read_text())
    surfaces = {
        surface
        for obligation in data["obligations"]
        for surface in obligation["source_surface"]
    }
    assert "Explorer EML primitive bridge" in surfaces
    assert "Forge guard obligations" in surfaces
    assert "PETAL curriculum" in surfaces
    assert "CapCard evidence cards" in surfaces
