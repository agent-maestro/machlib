import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "run_machlib_rational_root_search_v16.py"
PACKET = ROOT / "product_readiness" / "machlib_rational_root_search_v16_2026_05_25.json"
CERTS = ROOT / "product_readiness" / "machlib_rational_root_certificates_v16_2026_05_25.json"
CARD = ROOT / "product_readiness" / "machlib_rational_root_search_evidence_card_v16_2026_05_25.json"


def load_tool():
    spec = importlib.util.spec_from_file_location("run_machlib_rational_root_search_v16", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_search_finds_quadratic_roots():
    tool = load_tool()
    result = tool.search_factorization(
        tool.parse_coeffs([6, -5, 1]),
        root_limit=6,
        denominator_limit=4,
    )
    assert result["status"] == "CERTIFICATE_GENERATED"
    assert result["constant"] == 1
    assert result["linear_roots"] == [2, 3]
    assert result["remaining_coeffs"] == [1]


def test_search_blocks_x_squared_plus_one():
    tool = load_tool()
    result = tool.search_factorization(
        tool.parse_coeffs([1, 0, 1]),
        root_limit=6,
        denominator_limit=4,
    )
    assert result["status"] == "BLOCKED"
    assert result["blocker"] == "NO_COMPLETE_LINEAR_FACTORIZATION_FOUND_WITHIN_BOUND"
    assert result["remaining_coeffs"] == [1, 0, 1]


def test_search_handles_repeated_roots():
    tool = load_tool()
    result = tool.search_factorization(
        tool.parse_coeffs([-8, 12, -6, 1]),
        root_limit=6,
        denominator_limit=4,
    )
    assert result["status"] == "CERTIFICATE_GENERATED"
    assert result["linear_roots"] == [2, 2, 2]


def test_v16_packet_outputs():
    data = json.loads(PACKET.read_text())
    certs = json.loads(CERTS.read_text())
    card = json.loads(CARD.read_text())

    assert data["status"] == "MACHLIB_RATIONAL_ROOT_SEARCH_V16_READY"
    assert data["case_count"] >= 7
    assert data["certificate_generated_count"] >= 5
    assert data["blocked_count"] >= 1
    assert data["validation_failure_count"] == 0
    assert len(certs["certificates"]) == data["certificate_generated_count"]
    assert card["status"] == data["status"]


def test_v16_boundary_flags():
    data = json.loads(PACKET.read_text())
    assert data["arbitrary_factorization_discovery"] is False
    assert data["complete_rational_root_search_claim"] is False
    for key, value in data["boundary"].items():
        assert value is False
