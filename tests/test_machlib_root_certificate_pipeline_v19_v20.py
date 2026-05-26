import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "build_machlib_root_certificate_pipeline_v19_v20.py"
PACKET = ROOT / "product_readiness" / "machlib_root_certificate_pipeline_v19_v20_2026_05_25.json"
CERTS = ROOT / "product_readiness" / "machlib_quadratic_certificate_import_v19_2026_05_25.json"
CARD = ROOT / "product_readiness" / "machlib_degree_root_evidence_card_v20_2026_05_25.json"
COMPAT = (
    ROOT
    / "product_readiness"
    / "machlib_forge_efrog_polynomial_certificate_compatibility_v20_2026_05_25.json"
)


def load_tool():
    spec = importlib.util.spec_from_file_location("build_machlib_root_certificate_pipeline_v19_v20", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_build_payload_imports_rational_square_quadratic_certificate():
    tool = load_tool()
    source = tool.load_pipeline(tool.DEFAULT_V18_PACKET)
    payload = tool.build_payload(source)

    assert payload["status"] == "MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_READY"
    assert payload["v19_imported_certificate_count"] >= 1
    assert payload["v19_validation_failure_count"] == 0

    cert = payload["v19_imported_certificates"][0]
    assert cert["constant"] == 1
    assert cert["linear_roots"] == [7, 8]
    assert cert["expected_product_coeffs"] == [56, -15, 1]


def test_v19_validations_are_v15_compatible():
    data = json.loads(PACKET.read_text())
    certs = json.loads(CERTS.read_text())

    assert data["v19_imported_certificate_count"] == len(certs["certificates"])
    assert certs["validations"]
    for validation in certs["validations"]:
        assert validation["status"] == "PASS"
        assert validation["computed_coeffs"] == [56, -15, 1]


def test_v20_evidence_card_contract():
    card = json.loads(CARD.read_text())
    statuses = {row["status"] for row in card["evidence_rows"]}

    assert card["status"] == "MACHLIB_ROOT_CERTIFICATE_PIPELINE_V19_V20_READY"
    assert card["public_ready"] is False
    assert card["marketplace_ready"] is False
    assert "V16_CERTIFICATE_AVAILABLE" in statuses
    assert "V19_CERTIFICATE_CONVERTIBLE" in statuses
    assert "V18_CLASSIFIED_BLOCKER" in statuses


def test_compatibility_packet_is_report_only():
    compat = json.loads(COMPAT.read_text())

    assert compat["status"] == "REPORT_ONLY_NO_BEHAVIOR_CHANGE"
    assert compat["forge_compiler_behavior_changed"] is False
    assert compat["efrog_behavior_changed"] is False
    assert compat["root_count_induction_target_proved"] is False
    assert compat["public_ready"] is False
    assert compat["marketplace_ready"] is False


def test_v19_v20_boundary_flags():
    data = json.loads(PACKET.read_text())

    assert data["root_count_induction_target_status"] == "DEFINED_NOT_PROVED"
    assert data["forge_efrog_compatibility_status"] == "REPORT_ONLY_NO_BEHAVIOR_CHANGE"
    for value in data["boundary"].values():
        assert value is False
