from machlib_workbench.summary import summarize_path


def test_summarize_path_counts_files(tmp_path):
    (tmp_path / "a.md").write_text("# A\n")
    (tmp_path / "b.json").write_text("{}\n")
    (tmp_path / "c.txt").write_text("x\n")

    summary = summarize_path(tmp_path)

    assert summary.file_count == 3
    assert summary.markdown_count == 1
    assert summary.json_count == 1
    assert summary.other_count == 1
