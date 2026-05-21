from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from eml_records.loaders import iter_json_files, load_records_from_path, records_from_json_object
from eml_records.schema import FAMILY_FUNCTION_CLASS, REQUIRED_FALSE_BOOLEANS
from eml_records.validators import (
    classify_family,
    validate_file,
    validate_path,
    validate_record,
    validate_records,
)


def base_record() -> dict:
    return {
        "record_id": "demo_record_v0",
        "status": "DRAFT_INTERNAL",
        "public_ready": False,
        "upload_allowed": False,
        "release_ready": False,
        "mathlib_dependency": False,
        "forge_compiler_change_required": False,
        "hardware_required": False,
        "limitations": ["demo only"],
        "not_claimed": [
            "not public-ready",
            "not upload-ready",
            "not release-ready",
            "not a public theorem/proof/open-problem claim",
        ],
    }


def function_record() -> dict:
    record = base_record()
    record.update(
        {
            "function_class": "D_FINITE_CERTIFICATE",
            "certificate_type": "bounded_demo",
            "certificate_payload": {"ode": "demo"},
        }
    )
    return record


def stochastic_record() -> dict:
    record = base_record()
    record.update(
        {
            "process_class": "HYBRID_TRACE",
            "certificate_type": "bounded_trace",
            "certificate_payload": {"trace": [1, 2, 3]},
            "not_claimed": [
                *record["not_claimed"],
                "not stochastic calculus formalization",
                "not an SDE theorem",
                "not a Markov theorem",
                "not production controller evidence",
                "not certified safety",
            ],
        }
    )
    return record


def test_valid_generic_record_passes() -> None:
    result = validate_record(base_record())
    assert result.valid
    assert result.failure_count == 0
    assert result.record_id == "demo_record_v0"
    assert result.family == "UNKNOWN"


def test_missing_required_field_fails() -> None:
    record = base_record()
    del record["not_claimed"]
    result = validate_record(record)
    assert not result.valid
    assert any("missing required fields" in failure for failure in result.failures)


def test_forbidden_boolean_true_fails() -> None:
    record = base_record()
    record["public_ready"] = True
    result = validate_record(record)
    assert not result.valid
    assert any("public_ready must be false" in failure for failure in result.failures)


def test_required_false_boolean_schema_constant() -> None:
    assert "release_ready" in REQUIRED_FALSE_BOOLEANS


def test_invalid_status_fails_in_strict_mode() -> None:
    record = base_record()
    record["status"] = "PUBLIC_READY"
    result = validate_record(record, strict=True)
    assert not result.valid
    assert any("status" in failure for failure in result.failures)


def test_invalid_status_warns_in_non_strict_mode() -> None:
    record = base_record()
    record["status"] = "PUBLIC_READY"
    result = validate_record(record, strict=False)
    assert result.valid
    assert any("status" in warning for warning in result.warnings)


def test_missing_not_claimed_concept_fails_in_strict_mode() -> None:
    record = base_record()
    record["not_claimed"] = ["not public-ready", "not upload-ready", "not release-ready"]
    result = validate_record(record, strict=True)
    assert not result.valid
    assert any("public theorem" in failure for failure in result.failures)


def test_missing_not_claimed_concept_warns_in_non_strict_mode() -> None:
    record = base_record()
    record["not_claimed"] = ["not public-ready", "not upload-ready", "not release-ready"]
    result = validate_record(record, strict=False)
    assert result.valid
    assert any("public theorem" in warning for warning in result.warnings)


def test_function_class_record_passes() -> None:
    result = validate_record(function_record(), strict=True)
    assert result.valid
    assert result.family_counts == {FAMILY_FUNCTION_CLASS: 1}


def test_stochastic_hybrid_record_passes() -> None:
    result = validate_record(stochastic_record(), strict=True)
    assert result.valid
    assert result.family_counts == {"STOCHASTIC_HYBRID": 1}


def test_missing_stochastic_boundary_fails() -> None:
    record = stochastic_record()
    record["not_claimed"] = base_record()["not_claimed"]
    result = validate_record(record)
    assert not result.valid
    assert any("missing stochastic boundary concept" in failure for failure in result.failures)


def test_list_of_records_validates() -> None:
    result = validate_records([base_record(), function_record(), stochastic_record()])
    assert result.valid
    assert result.record_count == 3
    assert result.family_counts["FUNCTION_CLASS"] == 1


def test_records_from_json_object_handles_records_wrapper() -> None:
    records = records_from_json_object({"records": [base_record(), "skip"]})
    assert records == [base_record()]


def test_family_classifier() -> None:
    assert classify_family({"draft_eml_seed": base_record()}) == "LANE_SEED"
    assert classify_family(function_record()) == "FUNCTION_CLASS"
    assert classify_family(stochastic_record()) == "STOCHASTIC_HYBRID"
    assert classify_family({**base_record(), "evidence_type": "demo"}) == "EVIDENCE_RECORD"
    assert classify_family({"record_id": "x"}) == "UNKNOWN"


def test_lane_seed_wrapper_validates() -> None:
    wrapper = {"theorem": {"id": "lane_demo", "lane": 1}, "draft_eml_seed": {**base_record(), "lane": 1}}
    result = validate_record(wrapper)
    assert result.valid
    assert result.family_counts == {"LANE_SEED": 1}


def test_evidence_record_validates() -> None:
    record = {**base_record(), "evidence_type": "bounded_demo"}
    result = validate_record(record, strict=True)
    assert result.valid
    assert result.family_counts == {"EVIDENCE_RECORD": 1}


def test_nested_list_records_validate() -> None:
    result = validate_records([[base_record()], [function_record(), [stochastic_record()]]], strict=True)
    assert result.valid
    assert result.record_count == 3


def test_invalid_json_file_surfaces_failure(tmp_path) -> None:
    path = tmp_path / "bad.json"
    path.write_text("{not-json", encoding="utf-8")
    result = validate_file(path, strict=True)
    assert not result.valid
    assert any("JSON parse failed" in failure for failure in result.failures)


def test_load_records_from_path_and_include_filtering(tmp_path) -> None:
    (tmp_path / "record.json").write_text(__import__("json").dumps(base_record()), encoding="utf-8")
    (tmp_path / "skip.txt").write_text(__import__("json").dumps(function_record()), encoding="utf-8")
    assert len(load_records_from_path(tmp_path)) == 1
    assert len(load_records_from_path(tmp_path, include=("*.txt",))) == 1
    assert [path.name for path in iter_json_files(tmp_path, include=("*.txt",))] == ["skip.txt"]


def test_excluded_directory_ignored(tmp_path) -> None:
    (tmp_path / "node_modules").mkdir()
    (tmp_path / "node_modules" / "record.json").write_text(__import__("json").dumps(base_record()), encoding="utf-8")
    (tmp_path / "record.json").write_text(__import__("json").dumps(base_record()), encoding="utf-8")
    result = validate_path(tmp_path, strict=True)
    assert result.valid
    assert result.record_count == 1


def test_validate_path_family_filter() -> None:
    result = validate_path(ROOT / "tests", family=FAMILY_FUNCTION_CLASS, strict=True)
    assert not result.valid
    assert any("expected family" in failure for failure in result.failures)


def test_package_does_not_require_mathlib() -> None:
    record = base_record()
    record["limitations"] = ["demo only, no external formal dependency"]
    result = validate_record(record)
    assert result.valid
