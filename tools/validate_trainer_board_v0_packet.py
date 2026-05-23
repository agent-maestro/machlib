"""Validate the Trainer Board v0 Blackwell-side preflight packet."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


REQUIRED_FILES = [
    "trainer_board_v0_preflight_2026_05_23.json",
    "trainer_board_v0_serial_schema_2026_05_23.json",
    "trainer_board_v0_expected_trace_2026_05_23.jsonl",
    "trainer_board_v0_expected_summary_2026_05_23.json",
    "trainer_board_v0_capture_folder_template_2026_05_23.json",
    "trainer_board_v0_packet_manifest_template_2026_05_23.json",
    "trainer_board_v0_operator_checklist_2026_05_23.md",
    "trainer_board_v0_findings_template_2026_05_23.md",
    "trainer_board_v0_no_hardware_guardrail_2026_05_23.md",
]

SERIAL_FIELDS = {
    "kernel_id",
    "mode",
    "input",
    "request",
    "guard_state",
    "guard_reason",
    "output",
    "timestamp_ms",
    "source",
}

TOKEN_PATTERN = re.compile(r"pypi-[A-Za-z0-9]{20,}|hf_[A-Za-z0-9]{20,}|sk-[A-Za-z0-9]{20,}")


def load_json(path: Path) -> dict:
    return json.loads(path.read_text())


def validate_no_tokens(root: Path) -> None:
    for path in root.rglob("*"):
        if path.is_file():
            text = path.read_text(errors="ignore")
            if TOKEN_PATTERN.search(text):
                raise ValueError(f"token-like secret found in {path}")


def validate_trace(path: Path) -> list[dict]:
    frames = [json.loads(line) for line in path.read_text().splitlines() if line.strip()]
    if len(frames) != 62:
        raise ValueError("expected 62 frames")
    for frame in frames:
        missing = sorted(SERIAL_FIELDS - set(frame))
        if missing:
            raise ValueError(f"frame {frame.get('frame_index')} missing {missing}")
        if frame.get("hardware_observed") is not False:
            raise ValueError("hardware_observed must be false")
        if frame.get("live_serial_capture") is not False:
            raise ValueError("live_serial_capture must be false")
    return frames


def validate_packet(root: Path) -> None:
    for rel in REQUIRED_FILES:
        if not (root / rel).exists():
            raise ValueError(f"missing {rel}")
    preflight = load_json(root / "trainer_board_v0_preflight_2026_05_23.json")
    summary = load_json(root / "trainer_board_v0_expected_summary_2026_05_23.json")
    validate_trace(root / "trainer_board_v0_expected_trace_2026_05_23.jsonl")
    false_keys = [
        "hardware_action_performed",
        "certified_safety_claim",
        "production_controller_claim",
        "public_claim",
    ]
    for key in false_keys:
        if preflight.get(key) is not False:
            raise ValueError(f"preflight.{key} must be false")
        if summary.get(key) is not False:
            raise ValueError(f"summary.{key} must be false")
    for key in [
        "live_serial_capture_performed",
        "esp32_flash_performed",
        "arduino_flash_performed",
        "fpga_programming_performed",
        "soldering_performed",
        "powering_new_circuit_performed",
        "darpa_acceptance_claim",
    ]:
        if preflight.get(key) is not False:
            raise ValueError(f"preflight.{key} must be false")
    if summary.get("frame_count") != 62:
        raise ValueError("summary.frame_count must be 62")
    if summary.get("valid_frame_count") != 62:
        raise ValueError("summary.valid_frame_count must be 62")
    if summary.get("invalid_frame_count") != 0:
        raise ValueError("summary.invalid_frame_count must be 0")
    validate_no_tokens(root)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    validate_packet(args.root)
    print("TRAINER_BOARD_V0_PACKET_VALIDATION_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
