import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_stochastic_hybrid_draft")
TOOL = Path("tools/validate_stochastic_hybrid_records.py")


def load_validator():
    spec = importlib.util.spec_from_file_location("validate_stochastic_hybrid_records", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_stochastic_hybrid_records_validate():
    validator = load_validator()
    result = validator.validate(ROOT)
    assert result["record_count"] >= 12
    assert result["status"] == "DRAFT_INTERNAL_VALIDATED"
    assert result["zero_mathlib_status"] == "PASS"
    assert result["failures"] == []


def test_required_process_classes_present():
    validator = load_validator()
    result = validator.validate(ROOT)
    present = set(result["present_process_classes"])
    assert validator.REQUIRED_CLASSES <= present


def test_records_are_internal_and_guarded():
    import json

    records = json.loads((ROOT / "records_2026_05_20.json").read_text())["records"]
    for record in records:
        assert record["status"] == "DRAFT_INTERNAL"
        assert record["public_ready"] is False
        assert record["upload_allowed"] is False
        assert record["release_ready"] is False
        assert record["mathlib_dependency"] is False
        text = " ".join(record["not_claimed"]).lower()
        assert "not stochastic calculus" in text
        assert "not an sde theorem" in text
        assert "not a markov theorem" in text
