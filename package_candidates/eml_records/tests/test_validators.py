from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
sys.path.insert(0, str(SRC))

from eml_records.loaders import records_from_json_object
from eml_records.validators import classify_family, validate_record, validate_records


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


def test_function_class_record_passes() -> None:
    result = validate_record(function_record(), strict=True)
    assert result.valid
    assert result.family_counts == {"FUNCTION_CLASS": 1}


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


def test_package_does_not_require_mathlib() -> None:
    record = base_record()
    record["limitations"] = ["demo only, no external formal dependency"]
    result = validate_record(record)
    assert result.valid
