import json
import subprocess
import sys

from tools import trainer_board_v0_simulator as sim


def test_pot_sequence_has_exactly_62_values():
    assert len(sim.pot_sequence()) == 62


def test_generated_frames_have_exactly_62_rows():
    assert len(sim.generate_frames()) == 62


def test_frames_have_required_serial_shape():
    frame = sim.generate_frames()[0]
    for key in [
        "kernel_id",
        "mode",
        "input",
        "request",
        "guard_state",
        "guard_reason",
        "output",
        "timestamp_ms",
        "source",
    ]:
        assert key in frame


def test_frames_are_simulation_only():
    for frame in sim.generate_frames():
        assert frame["hardware_observed"] is False
        assert frame["live_serial_capture"] is False
        assert frame["source"] == "blackwell_expected_simulation_only"


def test_guard_includes_clamp_and_pass_through():
    states = {frame["guard_state"] for frame in sim.generate_frames()}
    assert "pass_through" in states
    assert "clamp_to_safe_output" in states


def test_safe_output_never_exceeds_limit():
    for frame in sim.generate_frames():
        assert frame["output"]["safe_output"] <= sim.SAFE_OUTPUT_LIMIT


def test_rate_limit_never_exceeds_max_step():
    frames = sim.generate_frames()
    previous = 0.0
    for frame in frames:
        current = frame["request"]["requested_output"]
        assert abs(current - previous) <= sim.MAX_STEP + 1e-9
        previous = frame["output"]["safe_output"]


def test_summary_counts_frames_and_guard_states():
    summary = sim.summarize(sim.generate_frames())
    assert summary["frame_count"] == 62
    assert summary["valid_frame_count"] == 62
    assert summary["invalid_frame_count"] == 0
    assert summary["pass_through_count"] > 0
    assert summary["clamped_count"] > 0


def test_summary_forbidden_action_fields_false():
    summary = sim.summarize(sim.generate_frames())
    for key in [
        "hardware_observed",
        "live_serial_capture",
        "flash_performed",
        "hardware_action_performed",
        "public_claim",
        "certified_safety_claim",
        "production_controller_claim",
    ]:
        assert summary[key] is False


def test_cli_writes_jsonl_and_summary(tmp_path):
    out_jsonl = tmp_path / "trace.jsonl"
    summary_out = tmp_path / "summary.json"
    result = subprocess.run(
        [
            sys.executable,
            "tools/trainer_board_v0_simulator.py",
            "--out-jsonl",
            str(out_jsonl),
            "--summary-out",
            str(summary_out),
            "--strict",
        ],
        check=True,
        text=True,
        capture_output=True,
    )
    assert "TRAINER_BOARD_V0_SIMULATION_OK" in result.stdout
    frames = [json.loads(line) for line in out_jsonl.read_text().splitlines()]
    summary = json.loads(summary_out.read_text())
    assert len(frames) == 62
    assert summary["frame_count"] == 62
