from pathlib import Path

from tools.capcard_lab.qwen_repair import build_qwen_repair


def test_qwen_repair_keeps_blocked():
    data = build_qwen_repair(Path("."))
    assert data["status"] == "QWEN_KEEP_BLOCKED"


def test_qwen_rows_have_exact_actions():
    data = build_qwen_repair(Path("."))
    assert len(data["rows"]) == 2
    assert data["exact_next_actions"]


def test_qwen_no_uploads():
    data = build_qwen_repair(Path("."))
    assert data["petal_api_upload_performed"] is False
    assert data["huggingface_upload_performed"] is False
