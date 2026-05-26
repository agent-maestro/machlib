import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_factored_root_packet_v14_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_v14_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_FACTORED_ROOT_PACKET_V14_READY"
    assert data["checked_result_count"] >= 15
    assert data["known_packet_target_status"] == "CHECKED"
    assert data["linear_factor_product_target_status"] == "CHECKED"
    assert data["repeated_linear_product_target_status"] == "CHECKED"
    assert data["factored_packet_composition_target_status"] == "CHECKED"
    assert data["arbitrary_coeff_target_status"] == "DEFINED_NOT_PROVED"


def test_v14_checked_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for name in data["checked_results"]:
        assert name in lean_text


def test_v14_target_split_exists():
    lean_text = LEAN.read_text()
    for name in [
        "def RootEnumeratorSound",
        "def RootCountForKnownPacketTarget",
        "def RootCountForLinearFactorProductsTarget",
        "def RootCountForRepeatedLinearProductsTarget",
        "def RootCountForFactoredTarget",
        "def RootCountForArbitraryCoeffTarget",
        "def RootCountInductionTarget",
    ]:
        assert name in lean_text
    assert "theorem rootCountForFactoredTarget_checked" in lean_text


def test_v14_forge_efrog_contract_boundary():
    data = json.loads(PACKET.read_text())
    shape = data["forge_efrog_certificate_shape"]
    assert shape["normalization"]["last_nonzero_required"] is True
    assert "RootListSound" in shape["evidence_obligations"]
    assert shape["boundary"]["forge_compiler_behavior_changed"] is False
    assert shape["boundary"]["efrog_behavior_changed"] is False
    assert shape["boundary"]["arbitrary_root_discovery_claim"] is False


def test_v14_no_new_axioms_or_sorry():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "sorry" not in lean_text


def test_v14_boundaries_false():
    data = json.loads(PACKET.read_text())
    for key in [
        "general_root_count_theorem_proved",
        "root_count_induction_target_proved",
        "arbitrary_root_discovery_claim",
        "analytic_identity_theorem_proved",
        "forge_compiler_behavior_changed",
        "efrog_behavior_changed",
        "public_theorem_claim",
        "marketplace_ready",
        "public_ready",
        "production_marketplace_modified",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "package_publish_performed",
        "certified_safety_claim",
        "production_controller_claim",
    ]:
        assert data[key] is False
