import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / "product_readiness" / "machlib_normalized_product_eval_packet_v10_2026_05_25.json"
LEAN = ROOT / "foundations" / "MachLib" / "NormalizedPolynomialRootCount.lean"
REPORT = ROOT / "reports" / "machlib_forge_efrog_polynomial_packet_compatibility_2026_05_25.md"


def test_v10_packet_shape():
    data = json.loads(PACKET.read_text())
    assert data["status"] == "MACHLIB_NORMALIZED_PRODUCT_EVAL_PACKET_V10_READY"
    assert data["checked_result_count"] >= 6
    assert data["normalizer_eval_soundness_status"] == "CHECKED"
    assert data["normalized_product_eval_soundness_status"] == "CHECKED"
    assert data["linear_times_arbitrary_degree_growth_proved"] is False
    assert data["arbitrary_normalized_product_degree_growth_proved"] is False
    assert data["forge_compiler_behavior_changed"] is False
    assert data["efrog_behavior_changed"] is False


def test_v10_lean_names_exist():
    data = json.loads(PACKET.read_text())
    lean_text = LEAN.read_text()
    for name in data["checked_results"]:
        assert name in lean_text
    for name in data["targets_named_not_proved"]:
        assert name in lean_text


def test_v10_compatibility_report_boundaries():
    text = REPORT.read_text()
    assert "No Forge compiler behavior is changed here" in text
    assert "No eFrog behavior is changed here" in text
    assert "does not prove the general root-count theorem" in text
    assert "LinearMulCoeffLastNonzeroTarget" in text
    assert "LinearMulCoeffDegreeGrowthTarget" in text


def test_v10_no_new_axioms_or_sorry():
    lean_text = LEAN.read_text()
    axiom_lines = [line.strip() for line in lean_text.splitlines() if line.strip().startswith("axiom ")]
    assert axiom_lines == []
    assert "sorry" not in lean_text


def test_v10_boundaries_false():
    data = json.loads(PACKET.read_text())
    for key in [
        "general_root_count_theorem_proved",
        "linear_times_arbitrary_degree_growth_proved",
        "arbitrary_normalized_product_degree_growth_proved",
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
