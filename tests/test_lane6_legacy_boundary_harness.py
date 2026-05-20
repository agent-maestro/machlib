from pathlib import Path

from tools import run_lane6_legacy_boundary_harness as harness


ROOT = Path("corpus/eml_lanes_draft")
TMP_ROOT = Path("/tmp/machlib_lane6_legacy_boundary_roundtrip_pytest_2026_05_20")
SPEC_OUT = Path("/tmp/machlib_lane6_legacy_boundary_spec_pytest_2026_05_20.json")


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_loads_three_lane6_seeds():
    seeds = harness.load_lane6_seeds(ROOT)
    assert set(seeds) == harness.EXPECTED_RECORDS
    assert len(seeds) == 3


def test_legacy_boundary_specs_include_required_ids_and_flags():
    specs = harness.write_legacy_boundary_spec(SPEC_OUT)
    assert {item["boundary_id"] for item in specs} == harness.REQUIRED_BOUNDARY_IDS
    for item in specs:
        assert item["default_enabled"] is False
        assert item["opt_in_only"] is True
        assert item["release_dependency_allowed"] is False
        assert item["current_release_dependency"] is False
        assert item["zero_mathlib_dependency"] is True
        assert item["public_ready"] is False
        assert item["upload_allowed"] is False
        assert item["mathlib_dependency"] is False


def test_efrog_default_is_zero_dependency_and_legacy_is_opt_in():
    probe = harness.efrog_default_and_legacy_probe()
    assert probe["status"] == "PASS"
    assert probe["default_zero_dependency"] is True
    assert probe["legacy_parameter_detected"] or probe["cli_flag_detected"]
    assert probe["legacy_parameter_default_false"] or probe["cli_flag_detected"]


def test_legacy_header_opt_in_boundary():
    result = harness.run_execution(ROOT)
    header = row(result, "legacy_mathlib_header_opt_in_note_v0")
    assert header["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in header["checks"]}
    assert checks["legacy_mode_opt_in_only"] is True
    assert checks["default_behavior_zero_dependency"] is True
    assert checks["efrog_default_zero_dependency"] is True
    assert checks["efrog_legacy_opt_in_detected"] is True


def test_legacy_adapter_boundary():
    result = harness.run_execution(ROOT)
    adapter = row(result, "legacy_adapter_boundary_record_v0")
    assert adapter["status"] == "PASS"
    assert adapter["default_enabled"] is False
    assert adapter["opt_in_only"] is True
    assert adapter["release_dependency_allowed"] is False
    assert adapter["current_release_dependency"] is False


def test_legacy_to_machlib_migration_stub():
    result = harness.run_execution(ROOT)
    migration = row(result, "legacy_to_machlib_migration_stub_v0")
    assert migration["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in migration["checks"]}
    assert checks["machlib_owned_target"] is True
    assert checks["does_not_import_source_dependency"] is True
    assert checks["does_not_auto_accept_legacy_artifacts"] is True
    assert checks["requires_review_or_validation"] is True


def test_eml_artifacts_are_generated_and_zero_dependency():
    seeds = harness.load_lane6_seeds(ROOT)
    execution = harness.run_execution(ROOT)
    paths = harness.write_eml_artifacts(seeds, execution, TMP_ROOT)
    assert set(paths) == harness.EXPECTED_RECORDS
    for path in paths.values():
        text = path.read_text()
        assert path.exists()
        assert not harness.contains_raw_dependency(text)
        assert "default_enabled false" in text
        assert "opt_in_only true" in text
        assert "release_dependency_allowed false" in text
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
        assert result["guardrails"]["legacy_never_default"] is True
        assert result["guardrails"]["legacy_never_release_dependency"] is True


def test_no_seed_has_forbidden_true_flags():
    seeds = harness.load_lane6_seeds(ROOT)
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
