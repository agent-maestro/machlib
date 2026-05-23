import subprocess
import sys
from pathlib import Path


def run_cli(*args):
    return subprocess.run([sys.executable, "-m", "tools.capcard_lab.cli", *args], check=True, text=True, capture_output=True)


def test_cli_help():
    result = subprocess.run([sys.executable, "-m", "tools.capcard_lab.cli", "--help"], check=True, text=True, capture_output=True)
    assert "discover" in result.stdout


def test_cli_pipeline_minimal(tmp_path):
    discover = tmp_path / "discover.json"
    graph = tmp_path / "graph.json"
    cards = tmp_path / "cards"
    muts = tmp_path / "muts"
    scores = tmp_path / "scores.json"
    ranking = tmp_path / "ranking.json"
    workbench = tmp_path / "workbench"
    run_cli("discover", "--repo-root", ".", "--out", str(discover), "--strict")
    run_cli("build-graph", "--repo-root", ".", "--out", str(graph), "--strict")
    run_cli("generate-candidates", "--repo-root", ".", "--graph", str(graph), "--out-dir", str(cards), "--strict")
    run_cli("mutate", "--cards", str(cards), "--out-dir", str(muts), "--count", "20", "--strict")
    run_cli("score", "--cards", str(cards), "--graph", str(graph), "--mutations", str(muts), "--out", str(scores), "--strict")
    run_cli("rank", "--scores", str(scores), "--out", str(ranking), "--strict")
    run_cli("render-workbench", "--cards", str(cards), "--scores", str(scores), "--ranking", str(ranking), "--out-dir", str(workbench), "--strict")
    assert (workbench / "index.html").exists()
