import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "validate_machlib_factorization_certificates_v15.py"
PACKET = ROOT / "product_readiness" / "machlib_factorization_certificate_import_v15_2026_05_25.json"
EXAMPLES = ROOT / "product_readiness" / "machlib_factorization_certificate_examples_v15_2026_05_25.json"
CARD = ROOT / "product_readiness" / "machlib_factored_root_evidence_card_v15_2026_05_25.json"


def load_tool():
    spec = importlib.util.spec_from_file_location("validate_machlib_factorization_certificates_v15", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_fractional_product_validation_passes():
    tool = load_tool()
    cert = {
        "certificate_id": "unit_fraction_test",
        "coeffs": ["-3/2", "3/2", 3],
        "constant": 3,
        "linear_roots": ["1/2", -1],
        "expected_product_coeffs": ["-3/2", "3/2", 3],
        "expected_dedup_roots": ["1/2", -1],
        "normalized": True,
    }
    result = tool.validate_certificate(cert)
    assert result.status == "PASS"
    assert result.computed_coeffs == ["-3/2", "3/2", 3]
    assert result.computed_roots == ["1/2", -1]


def test_bad_coefficients_fail():
    tool = load_tool()
    cert = {
        "certificate_id": "bad_coeff_test",
        "coeffs": [0, 0, 1],
        "constant": 1,
        "linear_roots": [1, 3],
        "expected_product_coeffs": [0, 0, 1],
        "expected_dedup_roots": [1, 3],
        "normalized": True,
    }
    result = tool.validate_certificate(cert)
    assert result.status == "FAIL"
    assert "expected_product_coeffs mismatch" in result.failures


def test_repeated_roots_warn_and_dedup():
    tool = load_tool()
    cert = next(row for row in tool.default_certificates() if row["certificate_id"] == "repeated_cubic_v15")
    result = tool.validate_certificate(cert)
    assert result.status == "PASS"
    assert result.computed_roots == [2]
    assert "repeated roots deduplicated" in result.warnings


def test_v15_packet_outputs():
    data = json.loads(PACKET.read_text())
    examples = json.loads(EXAMPLES.read_text())
    card = json.loads(CARD.read_text())

    assert data["status"] == "MACHLIB_FACTORIZATION_CERTIFICATE_IMPORT_V15_READY"
    assert data["certificate_count"] >= 7
    assert data["pass_count"] == data["certificate_count"]
    assert data["fail_count"] == 0
    assert len(examples["certificates"]) == data["certificate_count"]
    assert card["status"] == data["status"]
    assert card["public_ready"] is False
    assert card["marketplace_ready"] is False


def test_v15_boundaries_false():
    data = json.loads(PACKET.read_text())
    for key, value in data["boundary"].items():
        assert value is False
