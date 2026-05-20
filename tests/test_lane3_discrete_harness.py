from pathlib import Path

from tools import run_lane3_discrete_harness as harness


ROOT = Path("corpus/eml_lanes_draft")
TMP_ROOT = Path("/tmp/machlib_lane3_discrete_roundtrip_pytest_2026_05_20")


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_loads_three_lane3_seeds():
    seeds = harness.load_lane3_seeds(ROOT)
    assert set(seeds) == harness.EXPECTED_RECORDS
    assert len(seeds) == 3


def test_finite_graph_path_checks():
    result = harness.run_execution(ROOT)
    graph = row(result, "finite_graph_path_check_v0")
    assert graph["status"] == "PASS"
    checks = {item["query"]: item["actual"] for item in graph["checks"]}
    assert checks["A->D"] is True
    assert checks["D->A"] is False
    assert checks["A->A"] is True


def test_tiny_sat_clause_eval_checks():
    result = harness.run_execution(ROOT)
    sat = row(result, "tiny_sat_clause_eval_v0")
    assert sat["status"] == "PASS"
    checks = {item["assignment"]: item for item in sat["checks"]}
    assert checks["assignment1"]["satisfied"] is True
    assert checks["assignment2"]["satisfied"] is False
    assert checks["assignment1"]["clause_values"] == [True, True, True]
    assert checks["assignment2"]["clause_values"] == [True, True, False]


def test_recurrence_outputs_and_negative_index_block():
    result = harness.run_execution(ROOT)
    recurrence = row(result, "recurrence_fib_step_v0")
    assert recurrence["status"] == "PASS"
    checks = {item["n"]: item["actual"] for item in recurrence["checks"]}
    assert checks[2] == 1
    assert checks[3] == 2
    assert checks[4] == 3
    assert checks[5] == 5
    assert recurrence["negative_index"]["blocked"] is True


def test_eml_artifacts_are_generated_and_zero_dependency():
    seeds = harness.load_lane3_seeds(ROOT)
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
    seeds = harness.load_lane3_seeds(ROOT)
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
