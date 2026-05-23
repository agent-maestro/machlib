import json
import subprocess
from pathlib import Path


def run_cli(*args, cwd=None):
    return subprocess.run(
        ["python", "-m", "tools.qwen_capcard_lab.cli", *args],
        cwd=cwd or Path(__file__).resolve().parents[1],
        text=True,
        capture_output=True,
        check=False,
    )


def test_cli_help():
    proc = run_cli("--help")
    assert proc.returncode == 0


def test_cli_build_suite(tmp_path):
    out = tmp_path / "suite.json"
    proc = run_cli("build-suite", "--out", str(out), "--strict")
    assert proc.returncode == 0, proc.stderr
    assert json.loads(out.read_text())["task_count"] == 50


def test_cli_run_bakeoff(tmp_path):
    suite = tmp_path / "suite.json"
    out_dir = tmp_path / "bakeoff"
    assert run_cli("build-suite", "--out", str(suite), "--strict").returncode == 0
    proc = run_cli("run-bakeoff", "--models", "qwen3:30b", "--suite", str(suite), "--out-dir", str(out_dir), "--strict")
    assert proc.returncode == 0, proc.stderr
    data = json.loads((out_dir / "bakeoff_result_2026_05_23.json").read_text())
    assert data["task_count"] == 50
    assert data["real_model_outputs"] is False


def test_cli_repair_loop(tmp_path):
    suite = tmp_path / "suite.json"
    bakeoff_dir = tmp_path / "bakeoff"
    repair_dir = tmp_path / "repair"
    run_cli("build-suite", "--out", str(suite), "--strict")
    run_cli("run-bakeoff", "--models", "qwen3:30b", "--suite", str(suite), "--out-dir", str(bakeoff_dir), "--strict")
    proc = run_cli(
        "run-repair-loop",
        "--model",
        "qwen3:30b",
        "--suite",
        str(suite),
        "--bakeoff",
        str(bakeoff_dir / "bakeoff_result_2026_05_23.json"),
        "--out-dir",
        str(repair_dir),
        "--rounds",
        "3",
        "--strict",
    )
    assert proc.returncode == 0, proc.stderr
    assert (repair_dir / "prompt_pack_2026_05_23.json").exists()


def test_cli_validate_results(tmp_path):
    suite = tmp_path / "suite.json"
    bakeoff_dir = tmp_path / "bakeoff"
    repair_dir = tmp_path / "repair"
    update = tmp_path / "update.json"
    run_cli("build-suite", "--out", str(suite), "--strict")
    run_cli("run-bakeoff", "--models", "qwen3:30b", "--suite", str(suite), "--out-dir", str(bakeoff_dir), "--strict")
    run_cli("run-repair-loop", "--model", "qwen3:30b", "--suite", str(suite), "--bakeoff", str(bakeoff_dir / "bakeoff_result_2026_05_23.json"), "--out-dir", str(repair_dir), "--rounds", "3", "--strict")
    update.write_text(json.dumps({
        "public_ready": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "fine_tune_performed": False,
        "cloud_model_used": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }))
    proc = run_cli(
        "validate-results",
        "--bakeoff",
        str(bakeoff_dir / "bakeoff_result_2026_05_23.json"),
        "--repair-loop",
        str(repair_dir / "repair_loop_result_2026_05_23.json"),
        "--update",
        str(update),
        "--strict",
    )
    assert proc.returncode == 0, proc.stderr


def test_cli_build_suite_prints_ok(tmp_path):
    out = tmp_path / "suite.json"
    proc = run_cli("build-suite", "--out", str(out), "--strict")
    assert "QWEN_CAPCARD_TASK_SUITE_OK" in proc.stdout


def test_cli_bakeoff_writes_model_outputs(tmp_path):
    suite = tmp_path / "suite.json"
    out_dir = tmp_path / "bakeoff"
    run_cli("build-suite", "--out", str(suite), "--strict")
    run_cli("run-bakeoff", "--models", "qwen3:30b", "--suite", str(suite), "--out-dir", str(out_dir), "--strict")
    assert any((out_dir / "model_outputs").glob("*.json"))


def test_cli_bakeoff_writes_scored_outputs(tmp_path):
    suite = tmp_path / "suite.json"
    out_dir = tmp_path / "bakeoff"
    run_cli("build-suite", "--out", str(suite), "--strict")
    run_cli("run-bakeoff", "--models", "qwen3:30b", "--suite", str(suite), "--out-dir", str(out_dir), "--strict")
    assert any((out_dir / "scored_outputs").glob("*.json"))


def test_cli_repair_loop_writes_failure_memory(tmp_path):
    suite = tmp_path / "suite.json"
    bakeoff_dir = tmp_path / "bakeoff"
    repair_dir = tmp_path / "repair"
    run_cli("build-suite", "--out", str(suite), "--strict")
    run_cli("run-bakeoff", "--models", "qwen3:30b", "--suite", str(suite), "--out-dir", str(bakeoff_dir), "--strict")
    run_cli("run-repair-loop", "--model", "qwen3:30b", "--suite", str(suite), "--bakeoff", str(bakeoff_dir / "bakeoff_result_2026_05_23.json"), "--out-dir", str(repair_dir), "--rounds", "3", "--strict")
    assert (repair_dir / "failure_memory_2026_05_23.json").exists()
