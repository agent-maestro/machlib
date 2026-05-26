import importlib.util
import json
import sys
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "build_machlib_root_pipeline_v17_v18.py"
PACKET = ROOT / "product_readiness" / "machlib_polynomial_root_pipeline_v17_v18_2026_05_25.json"
RESIDUALS = ROOT / "product_readiness" / "machlib_residual_root_packets_v17_2026_05_25.json"
QUADRATICS = ROOT / "product_readiness" / "machlib_quadratic_classifier_v18_2026_05_25.json"
CARD = ROOT / "product_readiness" / "machlib_polynomial_root_pipeline_evidence_card_v18_2026_05_25.json"


def load_tool():
    spec = importlib.util.spec_from_file_location("build_machlib_root_pipeline_v17_v18", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_quadratic_classifier_negative_discriminant():
    tool = load_tool()
    result = tool.classify_quadratic([Fraction(1), Fraction(0), Fraction(1)])
    assert result["classification"] == "NEGATIVE_DISCRIMINANT_NO_REAL_ROOTS_IN_QUADRATIC_STUB"
    assert result["blocker"] == "NEGATIVE_DISCRIMINANT"
    assert result["rational_roots"] == []


def test_quadratic_classifier_irrational_roots():
    tool = load_tool()
    result = tool.classify_quadratic([Fraction(-2), Fraction(0), Fraction(1)])
    assert result["classification"] == "IRRATIONAL_ROOTS_BLOCKED_IN_RATIONAL_LAYER"
    assert result["discriminant"] == 8
    assert result["blocker"] == "DISCRIMINANT_NOT_RATIONAL_SQUARE"


def test_quadratic_classifier_rational_square():
    tool = load_tool()
    result = tool.classify_quadratic([Fraction(56), Fraction(-15), Fraction(1)])
    assert result["classification"] == "RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE"
    assert result["discriminant"] == 1
    assert result["rational_roots"] == [7, 8]
    assert result["blocker"] is None


def test_pipeline_payload_contract():
    tool = load_tool()
    payload = tool.build_payload(root_limit=6, denominator_limit=4)

    assert payload["status"] == "MACHLIB_POLYNOMIAL_ROOT_PIPELINE_V17_V18_READY"
    assert payload["case_count"] >= 10
    assert payload["residual_packet_count"] >= 10
    assert payload["quadratic_classification_count"] >= 3
    assert payload["root_count_induction_target_status"] == "DEFINED_NOT_PROVED"
    assert payload["quadratic_closed_form_theorem_claim"] is False
    assert payload["arbitrary_factorization_discovery"] is False
    for value in payload["boundary"].values():
        assert value is False


def test_pipeline_outputs():
    data = json.loads(PACKET.read_text())
    residuals = json.loads(RESIDUALS.read_text())
    quadratics = json.loads(QUADRATICS.read_text())
    card = json.loads(CARD.read_text())

    assert data["status"] == "MACHLIB_POLYNOMIAL_ROOT_PIPELINE_V17_V18_READY"
    assert len(residuals["residual_packets"]) == data["residual_packet_count"]
    assert len(quadratics["quadratic_classifications"]) == data["quadratic_classification_count"]
    assert card["status"] == data["status"]
    assert card["public_ready"] is False
    assert card["marketplace_ready"] is False


def test_pipeline_includes_three_quadratic_residual_classes():
    data = json.loads(PACKET.read_text())
    classes = {
        row["quadratic_classification"]["classification"]
        for row in data["quadratic_classifications"]
    }
    assert "NEGATIVE_DISCRIMINANT_NO_REAL_ROOTS_IN_QUADRATIC_STUB" in classes
    assert "IRRATIONAL_ROOTS_BLOCKED_IN_RATIONAL_LAYER" in classes
    assert "RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE" in classes
