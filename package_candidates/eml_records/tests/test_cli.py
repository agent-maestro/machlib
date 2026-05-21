from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from eml_records.cli import main

from test_validators import base_record, function_record


def test_cli_json_output_shape(tmp_path, capsys) -> None:
    path = tmp_path / "records.json"
    path.write_text(json.dumps({"records": [base_record(), function_record()]}), encoding="utf-8")
    code = main(["validate", str(path), "--json", "--strict"])
    captured = capsys.readouterr()
    payload = json.loads(captured.out)
    assert code == 0
    assert payload["scanned_file_count"] == 1
    assert payload["record_count"] == 2
    assert payload["valid_count"] == 2
    assert payload["failure_count"] == 0
    assert payload["family_counts"]["FUNCTION_CLASS"] == 1


def test_cli_strict_exits_nonzero_on_failure(tmp_path) -> None:
    path = tmp_path / "bad.json"
    record = base_record()
    record["release_ready"] = True
    path.write_text(json.dumps(record), encoding="utf-8")
    code = main(["validate", str(path), "--strict"])
    assert code == 1


def test_cli_non_strict_returns_zero_on_failure(tmp_path) -> None:
    path = tmp_path / "bad.json"
    record = base_record()
    record["upload_allowed"] = True
    path.write_text(json.dumps(record), encoding="utf-8")
    code = main(["validate", str(path)])
    assert code == 0


def test_cli_family_filter_passes_when_present(tmp_path) -> None:
    path = tmp_path / "function.json"
    path.write_text(json.dumps(function_record()), encoding="utf-8")
    code = main(["validate", str(path), "--family", "function-class", "--strict"])
    assert code == 0


def test_cli_family_filter_fails_when_missing(tmp_path) -> None:
    path = tmp_path / "generic.json"
    path.write_text(json.dumps(base_record()), encoding="utf-8")
    code = main(["validate", str(path), "--family", "function-class", "--strict"])
    assert code == 1


def test_cli_stochastic_family_filter(tmp_path) -> None:
    from test_validators import stochastic_record

    path = tmp_path / "stochastic.json"
    path.write_text(json.dumps(stochastic_record()), encoding="utf-8")
    code = main(["validate", str(path), "--family", "stochastic-hybrid", "--strict"])
    assert code == 0


def test_cli_include_filter(tmp_path, capsys) -> None:
    (tmp_path / "skip.json").write_text(json.dumps(base_record()), encoding="utf-8")
    (tmp_path / "keep.eml").write_text(json.dumps(function_record()), encoding="utf-8")
    code = main(["validate", str(tmp_path), "--include", "*.eml", "--json", "--strict"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 0
    assert payload["scanned_file_count"] == 1
    assert payload["family_counts"]["FUNCTION_CLASS"] == 1


def test_cli_exclude_dir(tmp_path, capsys) -> None:
    (tmp_path / "node_modules").mkdir()
    (tmp_path / "node_modules" / "bad.json").write_text(json.dumps({**base_record(), "public_ready": True}), encoding="utf-8")
    (tmp_path / "good.json").write_text(json.dumps(base_record()), encoding="utf-8")
    code = main(["validate", str(tmp_path), "--exclude-dir", "node_modules", "--json", "--strict"])
    payload = json.loads(capsys.readouterr().out)
    assert code == 0
    assert payload["scanned_file_count"] == 1
