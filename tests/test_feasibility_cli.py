import json
from pathlib import Path

from tools.feasibility_algebra.cli import main, run_stress


def test_run_stress_writes_core_outputs(tmp_path):
    out = tmp_path / "lab"
    run_stress(out, strict=True)
    assert (out / "feasibility_results_2026_05_23.json").exists()
    assert (out / "n1000_stress_result_2026_05_23.json").exists()


def test_run_stress_result_pass(tmp_path):
    payload = run_stress(tmp_path / "lab", strict=True)
    assert payload["status"] == "PASS"
    assert payload["result_count"] >= 18 * 9 * 8


def test_cli_main_run_stress(tmp_path):
    out = tmp_path / "cli"
    main(["run-stress", "--out-dir", str(out), "--strict"])
    data = json.loads((out / "n1000_stress_result_2026_05_23.json").read_text())
    assert data["central_case"] == "n^1000"


def test_cli_outputs_no_public_claim(tmp_path):
    out = tmp_path / "cli"
    run_stress(out, strict=True)
    data = json.loads((out / "feasibility_results_2026_05_23.json").read_text())
    assert data["public_claim"] is False
