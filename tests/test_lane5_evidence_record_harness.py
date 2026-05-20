from pathlib import Path

from tools import run_lane5_evidence_record_harness as harness


ROOT = Path("corpus/eml_lanes_draft")
TMP_ROOT = Path("/tmp/machlib_lane5_evidence_roundtrip_pytest_2026_05_20")
SPEC_OUT = Path("/tmp/machlib_lane5_evidence_schema_pytest_2026_05_20.json")


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_loads_three_lane5_seeds():
    seeds = harness.load_lane5_seeds(ROOT)
    assert set(seeds) == harness.EXPECTED_RECORDS
    assert len(seeds) == 3


def test_evidence_schema_specs_include_required_ids():
    specs = harness.write_evidence_schema_spec(SPEC_OUT)
    assert {item["schema_id"] for item in specs} == harness.REQUIRED_SCHEMA_IDS
    for item in specs:
        assert item["zero_mathlib_dependency"] is True
        assert item["public_ready"] is False
        assert item["upload_allowed"] is False
        assert item["mathlib_dependency"] is False
        assert "PUBLIC_READY" in item["forbidden_statuses"]


def test_lean_checkable_artifact_record_is_scoped():
    result = harness.run_execution(ROOT)
    artifact = row(result, "lean_checkable_artifact_record_v0")
    assert artifact["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in artifact["checks"]}
    assert checks["artifact_status_field_mapped"] is True
    assert checks["lean_check_status_scoped"] is True
    assert checks["blanket_proof_claim_absent"] is True
    assert artifact["artifact_status"] == "NEEDS_REVIEW"


def test_evidence_row_has_limitations_and_not_claimed():
    result = harness.run_execution(ROOT)
    evidence = row(result, "evidence_row_with_limitations_v0")
    assert evidence["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in evidence["checks"]}
    assert checks["limitations_non_empty"] is True
    assert checks["not_claimed_present"] is True
    assert checks["no_public_proof_boundary"] is True


def test_failed_attempt_is_not_accepted_or_public_ready():
    result = harness.run_execution(ROOT)
    failed = row(result, "failed_attempt_record_v0")
    assert failed["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in failed["checks"]}
    assert checks["failed_attempt_recorded"] is True
    assert checks["failure_reason_or_blocker_present"] is True
    assert checks["next_safe_local_action_present"] is True
    assert checks["not_treated_as_accepted"] is True
    assert failed["artifact_status"] == "FAILED_ATTEMPT_RECORDED"


def test_eml_artifacts_are_generated_and_zero_dependency():
    seeds = harness.load_lane5_seeds(ROOT)
    execution = harness.run_execution(ROOT)
    paths = harness.write_eml_artifacts(seeds, execution, TMP_ROOT)
    assert set(paths) == harness.EXPECTED_RECORDS
    for path in paths.values():
        text = path.read_text()
        assert path.exists()
        assert not harness.contains_raw_dependency(text)
        assert "public_ready false" in text
        assert "upload_allowed false" in text
        assert "mathlib_dependency false" in text


def test_execution_and_roundtrip_guardrails():
    execution = harness.run_execution(ROOT)
    roundtrip = harness.run_roundtrip(ROOT, TMP_ROOT, execution)
    assert execution["seed_count"] == 3
    assert execution["failed"] == 0
    assert roundtrip["seed_count"] == 3
    assert roundtrip["failed"] == 0
    assert roundtrip["roundtrip_status"] in {"PASS", "WARN"}
    for result in [execution, roundtrip]:
        assert result["guardrails"]["no_mathlib_dependency"] is True
        assert result["guardrails"]["no_hf_upload"] is True
        assert result["guardrails"]["no_petal_upload"] is True
        assert result["guardrails"]["no_package_publish"] is True
        assert result["guardrails"]["no_hardware"] is True
        assert result["guardrails"]["no_forge_compiler_change"] is True
        assert result["guardrails"]["no_public_theorem_claim"] is True


def test_no_seed_has_forbidden_true_flags():
    seeds = harness.load_lane5_seeds(ROOT)
    for seed in seeds.values():
        draft = seed.draft
        assert draft["public_ready"] is False
        assert draft["upload_allowed"] is False
        assert draft["mathlib_dependency"] is False


def test_warnings_are_allowed_only_for_tool_surface_limits():
    execution = harness.run_execution(ROOT)
    roundtrip = harness.run_roundtrip(ROOT, TMP_ROOT, execution)
    allowed = {
        "PASS",
        "WARN_EXPECTED_DRAFT_SCHEMA_LIMIT",
        "WARN_NO_DIRECT_FORGE_COMPILE",
        "WARN_EFROG_API_LIMIT",
    }
    for item in roundtrip["results"]:
        assert item["roundtrip_status"] in allowed
        assert not item["failures"]
        text = " ".join(item["warnings"]).lower()
        assert "upload" not in text
        assert "hardware" not in text
        assert "compiler mutation" not in text
