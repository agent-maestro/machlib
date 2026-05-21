import json
import os
import subprocess
import sys
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from claim_boundary.cli import main  # noqa: E402
from claim_boundary.scanner import scan_path  # noqa: E402


def phrase(*parts: str) -> str:
    return "".join(parts)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")


def test_clean_text_passes(tmp_path):
    write(tmp_path / "safe.md", "local evidence summary only\n")
    result = scan_path(tmp_path)
    assert result.passed is True
    assert result.suspicious_finding_count == 0


@pytest.mark.parametrize(
    ("text", "finding_class"),
    [
        (phrase("theorem ", "proved"), "PUBLIC_THEOREM_CLAIM"),
        (phrase("open problem ", "solved"), "OPEN_PROBLEM_CLAIM"),
        (phrase("certified ", "safety"), "CERTIFIED_SAFETY_CLAIM"),
        (phrase("production ", "controller"), "PRODUCTION_CONTROLLER_CLAIM"),
        (phrase("CapCard ", "certifies"), "CAPCARD_CERTIFICATION_CLAIM"),
        (phrase("PETAL ", "verifies"), "PETAL_VERIFICATION_CLAIM"),
        (phrase("Hugging Face upload ", "performed"), "HUGGINGFACE_UPLOAD_CLAIM"),
        (phrase("package publish ", "performed"), "PACKAGE_PUBLISH_CLAIM"),
        (phrase("PETAL/API upload ", "performed"), "PETAL_API_UPLOAD_CLAIM"),
        (phrase("command-center deploy ", "performed"), "COMMAND_CENTER_DEPLOY_CLAIM"),
        (phrase("Forge compiler behavior change ", "performed"), "FORGE_COMPILER_CHANGE_CLAIM"),
        (phrase("hardware action ", "performed"), "HARDWARE_ACTION_CLAIM"),
    ],
)
def test_positive_claims_fail(tmp_path, text, finding_class):
    write(tmp_path / "bad.md", text + "\n")
    result = scan_path(tmp_path)
    assert result.passed is False
    assert result.findings[0].finding_class == finding_class


@pytest.mark.parametrize(
    ("text", "finding_class"),
    [
        ("public_ready: true", "PUBLIC_READY_TRUE"),
        ("upload_allowed: true", "UPLOAD_ALLOWED_TRUE"),
        ("release_ready: true", "RELEASE_READY_TRUE"),
        ("marketplace_ready: true", "MARKETPLACE_READY_TRUE"),
    ],
)
def test_true_readiness_booleans_fail(tmp_path, text, finding_class):
    write(tmp_path / "bad.json", text + "\n")
    result = scan_path(tmp_path)
    assert result.passed is False
    assert result.findings[0].finding_class == finding_class


@pytest.mark.parametrize(
    "text",
    [
        "no public theorem/proof/open-problem claim",
        phrase("not certified ", "safety"),
        phrase("no package publish ", "performed"),
        phrase("Hugging Face upload was not ", "performed"),
        "PETAL/API upload remains blocked",
        phrase("not production ", "controller evidence"),
        "release-ready: false",
        "public_ready: false",
        "upload_allowed: false",
    ],
)
def test_negative_boundary_text_passes(tmp_path, text):
    write(tmp_path / "safe.md", text + "\n")
    result = scan_path(tmp_path)
    assert result.passed is True
    assert result.boundary_text_count == 1
    assert result.findings[0].finding_class == "NEGATED_NO_GO_TEXT"


def test_policy_text_passes(tmp_path):
    write(tmp_path / "policy.md", "POLICY_TEXT " + phrase("theorem ", "proved") + " is a blocked phrase\n")
    result = scan_path(tmp_path)
    assert result.passed is True
    assert result.policy_text_count == 1


@pytest.mark.parametrize("token", ["hf_" + "a" * 24, "pypi-" + "b" * 24, "sk-" + "c" * 24])
def test_token_like_secret_fails(tmp_path, token):
    write(tmp_path / "bad.txt", token + "\n")
    result = scan_path(tmp_path)
    assert result.passed is False
    assert result.token_like_secret_count == 1
    assert result.findings[0].finding_class == "TOKEN_LIKE_SECRET"


def test_json_output_shape(tmp_path):
    write(tmp_path / "safe.md", "public_ready: false\n")
    result = scan_path(tmp_path).to_dict()
    assert result["scanned_file_count"] == 1
    assert result["suspicious_finding_count"] == 0
    assert result["boundary_text_count"] == 1
    assert result["findings"]


def test_include_filtering(tmp_path):
    write(tmp_path / "bad.md", phrase("theorem ", "proved") + "\n")
    write(tmp_path / "safe.txt", "ordinary text\n")
    result = scan_path(tmp_path, include=("*.txt",))
    assert result.passed is True
    assert result.scanned_file_count == 1


def test_excluded_directory_ignored(tmp_path):
    write(tmp_path / "node_modules" / "bad.md", phrase("theorem ", "proved") + "\n")
    result = scan_path(tmp_path)
    assert result.passed is True
    assert result.scanned_file_count == 0


def test_cli_exit_code_behavior(tmp_path, capsys):
    write(tmp_path / "safe.md", "public_ready: false\n")
    assert main(["scan", str(tmp_path)]) == 0
    assert "CLAIM_BOUNDARY PASS" in capsys.readouterr().out

    write(tmp_path / "bad.md", phrase("theorem ", "proved") + "\n")
    assert main(["scan", str(tmp_path)]) == 1
    assert "CLAIM_BOUNDARY FAIL" in capsys.readouterr().out
    assert main(["scan", str(tmp_path), "--fail-on", "never"]) == 0


def test_cli_json_module_invocation(tmp_path):
    write(tmp_path / "safe.md", "upload_allowed: false\n")
    proc = subprocess.run(
        [sys.executable, "-m", "claim_boundary.cli", "scan", str(tmp_path), "--json"],
        cwd=ROOT,
        env={**os.environ, "PYTHONPATH": str(SRC)},
        text=True,
        capture_output=True,
        check=True,
    )
    data = json.loads(proc.stdout)
    assert data["suspicious_finding_count"] == 0
    assert data["boundary_text_count"] == 1
