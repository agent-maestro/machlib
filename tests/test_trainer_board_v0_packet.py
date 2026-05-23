import json
import subprocess
import sys
from pathlib import Path

from tools.validate_trainer_board_v0_packet import validate_packet


ROOT = Path("hardware_readiness/trainer_board_v0_2026_05_23")


def test_packet_root_exists_after_generation():
    assert ROOT.exists()


def test_expected_packet_files_exist():
    for name in [
        "trainer_board_v0_preflight_2026_05_23.json",
        "trainer_board_v0_serial_schema_2026_05_23.json",
        "trainer_board_v0_expected_trace_2026_05_23.jsonl",
        "trainer_board_v0_expected_summary_2026_05_23.json",
        "trainer_board_v0_capture_folder_template_2026_05_23.json",
        "trainer_board_v0_packet_manifest_template_2026_05_23.json",
        "trainer_board_v0_operator_checklist_2026_05_23.md",
        "trainer_board_v0_findings_template_2026_05_23.md",
        "trainer_board_v0_no_hardware_guardrail_2026_05_23.md",
    ]:
        assert (ROOT / name).exists()


def test_validate_packet_function_accepts_packet():
    validate_packet(ROOT)


def test_validate_packet_cli_accepts_packet():
    result = subprocess.run(
        [
            sys.executable,
            "tools/validate_trainer_board_v0_packet.py",
            "--root",
            str(ROOT),
            "--strict",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "TRAINER_BOARD_V0_PACKET_VALIDATION_OK" in result.stdout


def test_trace_has_62_frames():
    frames = [
        json.loads(line)
        for line in (ROOT / "trainer_board_v0_expected_trace_2026_05_23.jsonl").read_text().splitlines()
    ]
    assert len(frames) == 62


def test_trace_has_required_serial_fields():
    frames = [
        json.loads(line)
        for line in (ROOT / "trainer_board_v0_expected_trace_2026_05_23.jsonl").read_text().splitlines()
    ]
    for frame in frames:
        for key in ["kernel_id", "mode", "input", "request", "guard_state", "guard_reason", "output", "timestamp_ms", "source"]:
            assert key in frame


def test_trace_is_not_hardware_observed():
    frames = [
        json.loads(line)
        for line in (ROOT / "trainer_board_v0_expected_trace_2026_05_23.jsonl").read_text().splitlines()
    ]
    assert all(frame["hardware_observed"] is False for frame in frames)
    assert all(frame["live_serial_capture"] is False for frame in frames)


def test_preflight_forbidden_fields_false():
    preflight = json.loads((ROOT / "trainer_board_v0_preflight_2026_05_23.json").read_text())
    for key in [
        "hardware_action_performed",
        "live_serial_capture_performed",
        "esp32_flash_performed",
        "arduino_flash_performed",
        "fpga_programming_performed",
        "soldering_performed",
        "powering_new_circuit_performed",
        "certified_safety_claim",
        "production_controller_claim",
        "darpa_acceptance_claim",
        "public_claim",
    ]:
        assert preflight[key] is False


def test_summary_guard_telemetry_coverage():
    summary = json.loads((ROOT / "trainer_board_v0_expected_summary_2026_05_23.json").read_text())
    assert summary["full_guard_telemetry_coverage"] is True
    assert summary["valid_frame_count"] == 62
    assert summary["invalid_frame_count"] == 0


def test_capcard_candidate_is_internal():
    candidate = json.loads(Path("product_readiness/trainer_board_v0_capcard_candidate_2026_05_23.json").read_text())
    assert candidate["visibility"] == "internal"
    assert candidate["public_claim"] is False
