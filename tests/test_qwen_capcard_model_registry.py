from tools.qwen_capcard_lab.model_registry import ModelRuntime, RUNTIME_MODES, registry_from_matrix


def test_runtime_modes_include_api_schema_think_false():
    assert "api_schema_format_think_false" in RUNTIME_MODES


def test_model_runtime_to_dict():
    row = ModelRuntime("qwen3:30b", "api_schema_format", schema_json_rate=1.0)
    assert row.to_dict()["schema_json_rate"] == 1.0


def test_registry_from_matrix():
    rows = registry_from_matrix({"rows": [{"model": "m", "runtime_mode": "api_schema_format", "schema_json_rate": 1}]})
    assert rows[0].model == "m"


def test_unavailable_runtime_dict():
    row = ModelRuntime("m", "x", available=False)
    assert row.to_dict()["available"] is False


def test_runtime_notes_preserved():
    row = ModelRuntime("m", "x", notes="hello")
    assert row.notes == "hello"
