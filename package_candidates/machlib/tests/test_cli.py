from machlib.cli import main


def test_info_json(capsys) -> None:
    assert main(["info", "--json"]) == 0
    out = capsys.readouterr().out
    assert '"package_name": "machlib"' in out
    assert '"version": "0.0.1"' in out


def test_boundaries(capsys) -> None:
    assert main(["boundaries"]) == 0
    out = capsys.readouterr().out
    assert "not a theorem prover" in out
    assert "not a replacement for Mathlib" in out


def test_toolchain(capsys) -> None:
    assert main(["toolchain"]) == 0
    out = capsys.readouterr().out
    assert "zero-mathlib-checker" in out
    assert "review-branch-packet" in out
