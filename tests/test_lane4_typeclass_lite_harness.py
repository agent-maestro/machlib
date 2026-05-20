from pathlib import Path

from tools import run_lane4_typeclass_lite_harness as harness


ROOT = Path("corpus/eml_lanes_draft")
TMP_ROOT = Path("/tmp/machlib_lane4_typeclass_lite_roundtrip_pytest_2026_05_20")
SPEC_OUT = Path("/tmp/machlib_lane4_typeclass_lite_spec_pytest_2026_05_20.json")


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_loads_three_lane4_seeds():
    seeds = harness.load_lane4_seeds(ROOT)
    assert set(seeds) == harness.EXPECTED_RECORDS
    assert len(seeds) == 3


def test_structure_specs_include_required_ids():
    specs = harness.write_structure_spec(SPEC_OUT)
    assert {item["structure_id"] for item in specs} == harness.REQUIRED_STRUCTURE_IDS
    for item in specs:
        assert item["zero_mathlib_dependency"] is True
        assert item["public_ready"] is False
        assert item["upload_allowed"] is False
        assert item["mathlib_dependency"] is False


def test_magma_closure_over_add_mod_3():
    result = harness.run_execution(ROOT)
    magma = row(result, "typeclass_lite_magma_record_v0")
    assert magma["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in magma["checks"]}
    assert checks["closure"] is True
    assert checks["operation_table_exists"] is True
    assert checks["associativity_claimed"] is False
    assert checks["identity_claimed"] is False


def test_monoid_law_records_over_add_mod_3():
    result = harness.run_execution(ROOT)
    monoid = row(result, "typeclass_lite_monoid_record_v0")
    assert monoid["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in monoid["checks"]}
    assert checks["closure"] is True
    assert checks["associativity"] is True
    assert checks["identity_left_right"] is True
    assert checks["imported_hierarchy_claimed"] is False


def test_ordered_carrier_finite_relation():
    result = harness.run_execution(ROOT)
    ordered = row(result, "typeclass_lite_ordered_carrier_v0")
    assert ordered["status"] == "PASS"
    checks = {item["name"]: item["actual"] for item in ordered["checks"]}
    assert checks["reflexive"] is True
    assert checks["antisymmetric"] is True
    assert checks["transitive"] is True
    assert checks["total"] is True
    assert checks["imported_hierarchy_claimed"] is False


def test_eml_artifacts_are_generated_and_zero_dependency():
    seeds = harness.load_lane4_seeds(ROOT)
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
    seeds = harness.load_lane4_seeds(ROOT)
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
