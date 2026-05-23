import subprocess

from tools.qwen_capcard_lab.local_model import call_ollama_json


class FakeProc:
    def __init__(self, stdout="", stderr="", returncode=0):
        self.stdout = stdout
        self.stderr = stderr
        self.returncode = returncode


def test_local_model_success(monkeypatch):
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda *a, **k: FakeProc('{"candidate_id":"x","status":"BLOCKED_WITH_EXACT_FIX_LIST","evidence_basis":[],"limitations":[],"not_claimed":[]}'),
    )
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.extraction_status == "EXACT_JSON"
    assert result.real_model_output is True


def test_local_model_thinking_text(monkeypatch):
    monkeypatch.setattr(
        subprocess,
        "run",
        lambda *a, **k: FakeProc('Thinking... {"candidate_id":"x","status":"BLOCKED_WITH_EXACT_FIX_LIST","evidence_basis":[],"limitations":[],"not_claimed":[]}'),
    )
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.extraction_status == "JSON_EXTRACTED_FROM_THINKING_TEXT"


def test_local_model_timeout(monkeypatch):
    def boom(*args, **kwargs):
        raise subprocess.TimeoutExpired(args[0], timeout=1, output="", stderr="")

    monkeypatch.setattr(subprocess, "run", boom)
    result = call_ollama_json("qwen3:30b", "prompt", timeout_seconds=1)
    assert result.extraction_status == "MODEL_TIMEOUT"


def test_local_model_error(monkeypatch):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc("", "bad", 2))
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.extraction_status == "MODEL_ERROR"


def test_command_recorded(monkeypatch):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc("{}"))
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.command[:3] == ["ollama", "run", "qwen3:30b"]


def test_raw_output_recorded(monkeypatch):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc("hello"))
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.raw_output == "hello"


def test_forbidden_true_rejected(monkeypatch):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc('{"public_ready": true}'))
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.extraction_status == "JSON_INVALID"


def test_token_like_rejected(monkeypatch):
    fake_secret = "pypi-" + "abcdefghijklmnopqrstuvwxyz"
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc('{"x":"' + fake_secret + '"}'))
    result = call_ollama_json("qwen3:30b", "prompt")
    assert result.extraction_status == "JSON_INVALID"


def test_runtime_seconds_present(monkeypatch):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc("{}"))
    assert call_ollama_json("qwen3:30b", "prompt").runtime_seconds >= 0


def test_to_dict(monkeypatch):
    monkeypatch.setattr(subprocess, "run", lambda *a, **k: FakeProc("{}"))
    data = call_ollama_json("qwen3:30b", "prompt").to_dict()
    assert data["model"] == "qwen3:30b"
