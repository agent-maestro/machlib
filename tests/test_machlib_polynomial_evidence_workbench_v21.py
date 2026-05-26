import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
TOOL = ROOT / "tools" / "run_machlib_polynomial_evidence_workbench_v21.py"
PACKET = ROOT / "product_readiness" / "machlib_polynomial_evidence_workbench_v21_2026_05_25.json"
EXPORT = ROOT / "product_readiness" / "machlib_explorer_root_packet_export_v22_2026_05_25.json"
INVENTORY = ROOT / "product_readiness" / "machlib_root_count_target_inventory_v23_2026_05_25.json"
BRIDGE = ROOT / "product_readiness" / "machlib_certificate_validation_bridge_v24_2026_05_25.json"
ADAPTER = ROOT / "product_readiness" / "machlib_efrog_polynomial_adapter_dry_run_v25_2026_05_25.json"


def load_tool():
    spec = importlib.util.spec_from_file_location("run_machlib_polynomial_evidence_workbench_v21", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_expression_parser_emits_low_to_high_coefficients():
    tool = load_tool()
    assert tool.parse_polynomial_expr("x^2 - 15*x + 56") == [56, -15, 1]
    assert tool.parse_polynomial_expr("(x - 2) * (x - 3)") == [6, -5, 1]


def test_workbench_imports_quadratic_residual_certificate():
    tool = load_tool()
    coeffs = tool.parse_polynomial_expr("x^2 - 15*x + 56")
    payload = tool.build_single_pipeline(
        coeffs,
        source_kind="test_expr",
        source_text="x^2 - 15*x + 56",
        root_limit=6,
        denominator_limit=4,
    )

    assert payload["status"] == "MACHLIB_POLYNOMIAL_EVIDENCE_WORKBENCH_V21_READY"
    assert payload["workbench_status"] == "CERTIFICATE_IMPORTED_FROM_QUADRATIC_RESIDUAL"
    assert payload["v18_quadratic_classification"]["classification"] == "RATIONAL_DISCRIMINANT_SQUARE_FACTORABLE"
    assert payload["v19_imported_validation"]["status"] == "PASS"
    assert payload["v19_imported_certificate"]["linear_roots"] == [7, 8]


def test_workbench_outputs_are_internal_and_parseable():
    packet = json.loads(PACKET.read_text())
    export = json.loads(EXPORT.read_text())
    inventory = json.loads(INVENTORY.read_text())
    bridge = json.loads(BRIDGE.read_text())
    adapter = json.loads(ADAPTER.read_text())

    assert packet["status"] == "MACHLIB_POLYNOMIAL_EVIDENCE_WORKBENCH_V21_READY"
    assert export["status"] == "INTERNAL_EXPLORER_EXPORT_READY"
    assert inventory["status"] == "ROOT_COUNT_TARGET_INVENTORY_READY"
    assert bridge["status"] == "DERIVED_EXECUTABLE_CERTIFICATE_VALIDATION_READY"
    assert adapter["status"] == "EFROG_POLYNOMIAL_ADAPTER_DRY_RUN_READY"
    assert export["public_ready"] is False
    assert export["marketplace_ready"] is False
    assert adapter["efrog_behavior_changed"] is False
    assert adapter["forge_compiler_behavior_changed"] is False


def test_root_count_inventory_keeps_arbitrary_target_unproved():
    inventory = json.loads(INVENTORY.read_text())

    assert "rootCountForFactoredTarget_checked" in inventory["checked_targets"]
    assert "RootCountInductionTarget" in inventory["defined_not_proved_targets"]
    assert inventory["root_count_induction_target_proved"] is False
    assert inventory["public_theorem_claim"] is False


def test_workbench_boundary_flags():
    packet = json.loads(PACKET.read_text())

    assert packet["root_count_induction_target_status"] == "DEFINED_NOT_PROVED"
    for value in packet["boundary"].values():
        assert value is False
