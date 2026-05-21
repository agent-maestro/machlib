from machlib_workbench.cli import main


def test_cli_summarize_json(tmp_path, capsys):
    (tmp_path / "report.md").write_text("# Report\n")

    assert main(["summarize", str(tmp_path), "--json"]) == 0

    output = capsys.readouterr().out
    assert '"file_count": 1' in output
    assert '"markdown_count": 1' in output
