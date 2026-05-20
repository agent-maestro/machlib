from pathlib import Path

from tools import run_lane2_roundtrip_probe as probe


ROOT = Path("corpus/eml_lanes_draft")
TMP_ROOT = Path("/tmp/machlib_lane2_roundtrip_probe_pytest_2026_05_20")


def test_loads_three_lane2_seeds():
    seeds = probe.load_lane2_seeds(ROOT)
    assert set(seeds) == probe.EXPECTED_RECORDS
    assert len(seeds) == 3


def test_primitive_specs_include_all_required_ids():
    specs = probe.load_primitive_specs(ROOT)
    ids = {item["primitive_id"] for item in specs}
    assert ids == probe.REQUIRED_PRIMITIVES


def test_symbolic_rewrite_result_is_ready_for_probe():
    result = probe.load_symbolic_rewrite_result(ROOT)
    assert result["seed_count"] == 3
    assert result["failed"] == 0
    assert result["rewrite_status"] == "PASS"
    assert result["lane_status"] == "DRAFT_INTERNAL_SYMBOLIC_REWRITE_ONLY"


def test_eml_artifacts_are_generated_under_tmp_and_zero_dependency():
    seeds = probe.load_lane2_seeds(ROOT)
    rewrite_result = probe.load_symbolic_rewrite_result(ROOT)
    paths = probe.write_eml_artifacts(seeds, rewrite_result, TMP_ROOT)
    assert set(paths) == probe.EXPECTED_RECORDS
    for path in paths.values():
        text = path.read_text()
        assert path.exists()
        assert not probe.contains_raw_dependency(text)
        assert "public_ready false" in text
        assert "upload_allowed false" in text
        assert "mathlib_dependency false" in text
        assert "symbolic_relation" in text


def test_roundtrip_probe_result_guardrails_and_rows():
    result = probe.execute(ROOT, TMP_ROOT)
    assert result["seed_count"] == 3
    assert result["failed"] == 0
    assert result["roundtrip_status"] in {"PASS", "WARN"}
    assert result["guardrails"]["no_mathlib_dependency"] is True
    assert result["guardrails"]["no_hf_upload"] is True
    assert result["guardrails"]["no_petal_upload"] is True
    assert result["guardrails"]["no_package_publish"] is True
    assert result["guardrails"]["no_hardware"] is True
    assert result["guardrails"]["no_forge_compiler_change"] is True
    assert result["guardrails"]["no_public_theorem_claim"] is True
    assert {row["record_id"] for row in result["results"]} == probe.EXPECTED_RECORDS
    for row in result["results"]:
        assert row["eml_artifact_generated"] is True
        assert not row["failures"]


def test_seed_guardrails_are_false():
    seeds = probe.load_lane2_seeds(ROOT)
    for seed in seeds.values():
        draft = seed.draft
        assert draft["public_ready"] is False
        assert draft["upload_allowed"] is False
        assert draft["mathlib_dependency"] is False


def test_allowed_warnings_are_not_boundary_violations():
    result = probe.execute(ROOT, TMP_ROOT)
    allowed = {
        "PASS",
        "WARN_EXPECTED_SYMBOLIC_LIMIT",
        "WARN_NO_DIRECT_FORGE_COMPILE",
        "WARN_EFROG_API_LIMIT",
    }
    for row in result["results"]:
        assert row["roundtrip_status"] in allowed
        text = " ".join(row["warnings"])
        assert "upload" not in text.lower()
        assert "hardware" not in text.lower()
        assert "compiler mutation" not in text.lower()
