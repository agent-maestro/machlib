"""Generate Trainer Board v0 expected serial telemetry.

This is a Blackwell-side simulator only. It never opens serial ports, flashes
firmware, powers circuits, or observes hardware.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


KERNEL_ID = "threshold_reflex_v0"
MODE = "trainer_board_v0_reflex"
SOURCE = "blackwell_expected_simulation_only"
THRESHOLD = 0.55
WIDTH = 0.10
MAX_STEP = 0.20
SAFE_OUTPUT_LIMIT = 0.85


def clamp(value: float, low: float, high: float) -> float:
    return max(low, min(high, value))


def rate_limit(previous: float, target: float, max_step: float = MAX_STEP) -> float:
    delta = clamp(target - previous, -max_step, max_step)
    return previous + delta


def pot_sequence() -> list[float]:
    """Return exactly 62 values with low, threshold, high, and clamp cases."""
    values = [
        0.00,
        0.04,
        0.08,
        0.12,
        0.18,
        0.24,
        0.30,
        0.36,
        0.42,
        0.48,
        0.52,
        0.54,
        0.55,
        0.56,
        0.58,
        0.60,
        0.62,
        0.65,
        0.70,
        0.75,
        0.80,
        0.85,
        0.90,
        0.95,
        1.00,
        0.98,
        0.96,
        0.94,
        0.92,
        0.90,
        0.88,
        0.86,
        0.84,
        0.82,
        0.78,
        0.74,
        0.70,
        0.66,
        0.62,
        0.58,
        0.55,
        0.52,
        0.48,
        0.44,
        0.40,
        0.35,
        0.30,
        0.25,
        0.20,
        0.15,
        0.10,
        0.05,
        0.00,
        0.55,
        0.75,
        0.95,
        0.65,
        0.45,
        0.85,
        0.25,
        1.00,
        0.55,
    ]
    assert len(values) == 62
    return values


@dataclass(frozen=True)
class FrameStats:
    pass_through_count: int
    clamped_count: int


def make_frame(frame_index: int, pot_raw: float, previous_output: float) -> tuple[dict, float]:
    centered = (pot_raw - THRESHOLD) / WIDTH
    target = clamp(centered + 0.5, 0.0, 1.0)
    requested_output = rate_limit(previous_output, target)
    safe_output = clamp(requested_output, 0.0, SAFE_OUTPUT_LIMIT)
    clamped = requested_output > SAFE_OUTPUT_LIMIT
    frame = {
        "frame_index": frame_index,
        "timestamp_ms": frame_index * 50,
        "kernel_id": KERNEL_ID,
        "mode": MODE,
        "input": {"pot_raw": round(pot_raw, 4)},
        "request": {
            "centered": round(centered, 6),
            "target": round(target, 6),
            "requested_output": round(requested_output, 6),
        },
        "guard_state": "clamp_to_safe_output" if clamped else "pass_through",
        "guard_reason": "safe_output_limit_0.85" if clamped else "within_safe_output_limit",
        "output": {"safe_output": round(safe_output, 6)},
        "source": SOURCE,
        "hardware_observed": False,
        "live_serial_capture": False,
    }
    return frame, safe_output


def generate_frames() -> list[dict]:
    previous_output = 0.0
    frames = []
    for frame_index, pot_raw in enumerate(pot_sequence()):
        frame, previous_output = make_frame(frame_index, pot_raw, previous_output)
        frames.append(frame)
    return frames


def validate_frame(frame: dict) -> None:
    required = {
        "frame_index",
        "timestamp_ms",
        "kernel_id",
        "mode",
        "input",
        "request",
        "guard_state",
        "guard_reason",
        "output",
        "source",
        "hardware_observed",
        "live_serial_capture",
    }
    missing = sorted(required - set(frame))
    if missing:
        raise ValueError(f"missing fields: {missing}")
    if frame["kernel_id"] != KERNEL_ID:
        raise ValueError("kernel_id mismatch")
    if frame["mode"] != MODE:
        raise ValueError("mode mismatch")
    if frame["hardware_observed"] is not False:
        raise ValueError("hardware_observed must be false")
    if frame["live_serial_capture"] is not False:
        raise ValueError("live_serial_capture must be false")
    if frame["guard_state"] not in {"pass_through", "clamp_to_safe_output"}:
        raise ValueError("unexpected guard_state")
    if frame["output"]["safe_output"] > SAFE_OUTPUT_LIMIT:
        raise ValueError("safe_output exceeds limit")


def summarize(frames: Iterable[dict]) -> dict:
    rows = list(frames)
    for frame in rows:
        validate_frame(frame)
    pass_count = sum(1 for frame in rows if frame["guard_state"] == "pass_through")
    clamp_count = sum(1 for frame in rows if frame["guard_state"] == "clamp_to_safe_output")
    return {
        "frame_count": len(rows),
        "valid_frame_count": len(rows),
        "invalid_frame_count": 0,
        "kernel_id": KERNEL_ID,
        "mode": MODE,
        "simulated_only": True,
        "hardware_observed": False,
        "live_serial_capture": False,
        "flash_performed": False,
        "hardware_action_performed": False,
        "pass_through_count": pass_count,
        "clamped_count": clamp_count,
        "full_guard_telemetry_coverage": True,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
    }


def write_outputs(out_jsonl: Path, summary_out: Path) -> dict:
    frames = generate_frames()
    if len(frames) != 62:
        raise ValueError("expected exactly 62 frames")
    summary = summarize(frames)
    if summary["clamped_count"] < 1:
        raise ValueError("expected at least one clamp frame")
    if summary["pass_through_count"] < 1:
        raise ValueError("expected pass-through frames")
    out_jsonl.parent.mkdir(parents=True, exist_ok=True)
    summary_out.parent.mkdir(parents=True, exist_ok=True)
    out_jsonl.write_text("\n".join(json.dumps(frame, sort_keys=True) for frame in frames) + "\n")
    summary_out.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    return summary


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-jsonl", required=True, type=Path)
    parser.add_argument("--summary-out", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    summary = write_outputs(args.out_jsonl, args.summary_out)
    if args.strict and summary["frame_count"] != 62:
        raise SystemExit("strict frame count mismatch")
    print("TRAINER_BOARD_V0_SIMULATION_OK", summary["frame_count"], summary["clamped_count"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
