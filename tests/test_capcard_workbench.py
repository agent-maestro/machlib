import json

from tools.capcard_workbench import main


def test_workbench_generates_static_files(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    drafts = tmp_path / "drafts"
    drafts.mkdir()
    (drafts / "card.json").write_text(json.dumps({
        "candidate_id": "eml_puzzle_evidence_kernel",
        "display_name": "EML Puzzle Evidence Kernel",
        "evidence_basis": ["internal evidence ledger", "no-upload gate"],
        "limitations": ["not certified safety"],
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }))
    out = tmp_path / "out"
    monkeypatch.setattr("sys.argv", ["capcard_workbench.py", "--drafts", str(drafts), "--out-dir", str(out), "--strict"])
    assert main() == 0
    assert (out / "index.html").exists()
    assert (out / "candidate_index.json").exists()
    manifest = json.loads((out / "workbench_manifest_2026_05_21.json").read_text())
    assert manifest["html_generated"] is True
    assert manifest["deploy_performed"] is False
    assert manifest["production_marketplace_modified"] is False
