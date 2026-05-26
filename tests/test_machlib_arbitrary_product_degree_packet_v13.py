import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_arbitrary_product_degree_packet_v13_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"


def test_v13_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_ARBITRARY_PRODUCT_DEGREE_PACKET_V13_READY"
    assert data["checked_result_count"] >= 14
    assert data["arbitrary_raw_product_last_nonzero_status"] == "CHECKED"
    assert data["arbitrary_raw_product_degree_growth_status"] == "CHECKED"
    assert data["arbitrary_normalized_product_last_nonzero_status"] == "CHECKED"
    assert data["arbitrary_normalized_product_degree_growth_status"] == "CHECKED"
    assert data["product_packet_assembly_status"] == "CHECKED_FOR_KNOWN_FINITE_ROOT_PACKETS"
    assert data["root_count_induction_target_assembled"] is False


def test_v13_checked_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for name in data["checked_results"]:
        assert name in lean_text


def test_v13_arbitrary_targets_checked():
    lean_text = LEAN.read_text()
    assert "def NormalizedMulCoeffDegreeGrowthTarget" in lean_text
    assert "theorem normalizedMulCoeffDegreeGrowthTarget_checked" in lean_text
    assert "def ProductPacketAssemblyTarget" in lean_text
    assert "theorem productPacketAssemblyTarget_checked" in lean_text
    assert "def RootCountInductionTarget" in lean_text


def test_v13_no_new_axioms_or_sorry():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "sorry" not in lean_text


def test_v13_boundaries_false():
    data = json.loads(PACKET.read_text())
    for key in [
        "root_count_induction_target_assembled",
        "general_root_count_theorem_proved",
        "root_count_induction_target_proved",
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
