from pathlib import Path

from tools import run_lane1_roundtrip_harness as harness


ROOT = Path("corpus/eml_lanes_draft")
TMP_ROOT = Path("/tmp/machlib_lane1_roundtrip_pytest_2026_05_20")


def test_loads_four_lane1_seeds():
    seeds = harness.load_lane1_seeds(ROOT)
    assert set(seeds) == harness.EXPECTED_RECORDS
    assert len(seeds) == 4


def test_eml_artifacts_are_generated_and_zero_dependency():
    seeds = harness.load_lane1_seeds(ROOT)
    paths = harness.write_eml_artifacts(seeds, TMP_ROOT)
    assert set(paths) == harness.EXPECTED_RECORDS
    for path in paths.values():
        text = path.read_text()
        assert path.exists()
        assert not harness.contains_raw_dependency(text)
        assert "public_ready false" in text
        assert "upload_allowed false" in text
        assert "mathlib_dependency false" in text


def test_roundtrip_result_guardrails_and_cubic_presence():
    result = harness.execute(ROOT, TMP_ROOT)
    assert result["seed_count"] == 4
    assert result["failed"] == 0
    assert result["guardrails"]["no_mathlib_dependency"] is True
    assert result["guardrails"]["no_hf_upload"] is True
    assert result["guardrails"]["no_petal_upload"] is True
    assert result["guardrails"]["no_package_publish"] is True
    assert result["guardrails"]["no_hardware"] is True
    assert result["guardrails"]["no_forge_compiler_change"] is True
    assert result["guardrails"]["no_public_theorem_claim"] is True
    ids = {row["record_id"] for row in result["results"]}
    assert "cubic_dyadic_equilibrium_v0" in ids


def test_no_seed_has_forbidden_true_flags():
    seeds = harness.load_lane1_seeds(ROOT)
    for seed in seeds.values():
        draft = seed.draft
        assert draft["public_ready"] is False
        assert draft["upload_allowed"] is False
        assert draft["mathlib_dependency"] is False


def test_warnings_are_allowed_only_for_tool_surface_limits():
    result = harness.execute(ROOT, TMP_ROOT)
    allowed = {
        "WARN_NO_DIRECT_FORGE_COMPILE",
        "WARN_EFROG_API_LIMIT",
        "PASS",
    }
    for row in result["results"]:
        assert row["roundtrip_status"] in allowed
        assert not row["failures"]
