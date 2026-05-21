import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from review_branch_packet.cli import main  # noqa: E402


def fake_completed(stdout: str, returncode: int = 0):
    class Completed:
        def __init__(self):
            self.stdout = stdout
            self.stderr = ""
            self.returncode = returncode

    return Completed()


def install_fake_subprocess(monkeypatch, calls):
    def fake_run(cmd, cwd=".", check=False, text=True, capture_output=True):
        calls.append(tuple(cmd))
        assert cmd[0] == "git"
        forbidden = {"push", "pull", "fetch", "checkout", "merge"}
        assert cmd[1] not in forbidden
        assert tuple(cmd[:3]) != ("gh", "pr", "create")
        if tuple(cmd[1:]) == ("status", "--short"):
            return fake_completed("")
        if tuple(cmd[1:]) == ("branch", "--show-current"):
            return fake_completed("feat/ac-instances\n")
        if tuple(cmd[1:]) == ("remote", "-v"):
            return fake_completed("origin\thttps://example.invalid/repo.git (push)\n")
        if tuple(cmd[1:4]) == ("log", "--oneline", "-10"):
            return fake_completed("cafebabe demo commit\n")
        if tuple(cmd[1:3]) == ("ls-remote", "--heads"):
            return fake_completed("deadbeef\trefs/heads/review/demo\n")
        raise AssertionError(cmd)

    monkeypatch.setattr("review_branch_packet.git_inspect.subprocess.run", fake_run)


def test_cli_json_output_shape(monkeypatch, capsys):
    calls = []
    install_fake_subprocess(monkeypatch, calls)
    rc = main(["inspect", "--target", "review/demo", "--json"])
    assert rc == 0
    data = json.loads(capsys.readouterr().out)
    assert data["target_review_branch"] == "review/demo"
    assert data["review_branch_present"] is True
    assert data["push_performed"] is False
    assert data["github_pr_created"] is False


def test_cli_writes_json_and_markdown(monkeypatch, tmp_path, capsys):
    calls = []
    install_fake_subprocess(monkeypatch, calls)
    out = tmp_path / "packet.json"
    md = tmp_path / "packet.md"
    rc = main(["inspect", "--target", "review/demo", "--out", str(out), "--markdown-out", str(md)])
    assert rc == 0
    assert json.loads(out.read_text())["local_head_sha"] == "cafebabe"
    assert "Review Branch Packet" in md.read_text()
    assert capsys.readouterr().out == ""


def test_cli_never_invokes_forbidden_commands(monkeypatch, capsys):
    calls = []
    install_fake_subprocess(monkeypatch, calls)
    main(["inspect", "--target", "review/demo", "--json"])
    rendered = [" ".join(call) for call in calls]
    assert not any("git push" in item for item in rendered)
    assert not any("git merge" in item for item in rendered)
    assert not any("gh pr create" in item for item in rendered)
