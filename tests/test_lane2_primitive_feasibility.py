from pathlib import Path

import pytest

from tools import analyze_lane2_primitive_feasibility as lane2


ROOT = Path("corpus/eml_lanes_draft")
OUT = ROOT / "lane_2_calculus_special_functions" / "primitive_feasibility_result_2026_05_20.json"
SPEC_OUT = ROOT / "lane_2_calculus_special_functions" / "primitive_spec_draft_2026_05_20.json"


@pytest.fixture(scope="module")
def result():
    return lane2.run_analysis(ROOT, OUT, SPEC_OUT)


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_lane2_seed_count_and_status(result):
    assert result["seed_count"] == 3
    assert result["lane_status"] == "DRAFT_INTERNAL_FEASIBILITY_ONLY"
    assert result["failed"] == 0


def test_all_lane2_seeds_are_draft_internal_with_false_guardrails():
    seeds = lane2.load_lane2_seeds(ROOT)
    assert set(seeds) == lane2.EXPECTED_RECORDS
    for seed in seeds.values():
        draft = seed.draft
        assert draft["status"] == "DRAFT_INTERNAL"
        assert draft["public_ready"] is False
        assert draft["upload_allowed"] is False
        assert draft["mathlib_dependency"] is False
        assert draft["forge_compiler_change_required"] is False
        assert draft["hardware_required"] is False


def test_exp_log_seed_requires_domain_guards(result):
    exp_log = row(result, "exp_log_formal_inverse_draft_v0")
    assert exp_log["status"] == "WARN"
    assert exp_log["feasibility"] == "FEASIBLE_WITH_DOMAIN_GUARD"
    assert "mach_exp_symbolic_v0" in exp_log["required_primitives"]
    assert "mach_log_symbolic_v0" in exp_log["required_primitives"]
    assert any("positive-domain" in guard for guard in exp_log["domain_guards"])


def test_trig_seed_requires_owned_primitive_semantics(result):
    trig = row(result, "trig_pythagorean_symbolic_draft_v0")
    assert trig["status"] == "WARN"
    assert trig["feasibility"] == "NEEDS_MACHLIB_PRIMITIVE"
    assert "mach_sin_symbolic_v0" in trig["required_primitives"]
    assert "mach_cos_symbolic_v0" in trig["required_primitives"]
    assert any("owned" in relation for relation in trig["accepted_symbolic_relations"])


def test_pow_sqrt_boundary_is_not_directly_accepted(result):
    pow_sqrt = row(result, "pow_square_root_symbolic_draft_v0")
    assert pow_sqrt["status"] == "WARN"
    assert pow_sqrt["feasibility"] == "FEASIBLE_WITH_DOMAIN_GUARD"
    assert "mach_sqrt_symbolic_v0" in pow_sqrt["required_primitives"]
    assert any("sqrt(x^2)" in relation for relation in pow_sqrt["blocked_relations"])
    assert any("structure/proof layer" in relation for relation in pow_sqrt["blocked_relations"])


def test_primitive_specs_include_required_ids(result):
    primitive_ids = {item["primitive_id"] for item in result["primitive_specs"]}
    assert primitive_ids == set(lane2.REQUIRED_PRIMITIVES)
    for spec in result["primitive_specs"]:
        assert spec["status"] == "DRAFT_INTERNAL"
        assert spec["public_ready"] is False
        assert spec["upload_allowed"] is False
        assert spec["mathlib_dependency"] is False


def test_guardrails_and_zero_dependency_status(result):
    assert result["zero_mathlib_status"] == "PASS"
    assert result["guardrails"]["no_mathlib_dependency"] is True
    assert result["guardrails"]["no_hf_upload"] is True
    assert result["guardrails"]["no_petal_upload"] is True
    assert result["guardrails"]["no_package_publish"] is True
    assert result["guardrails"]["no_hardware"] is True
    assert result["guardrails"]["no_forge_compiler_change"] is True
    assert result["guardrails"]["no_public_theorem_claim"] is True
    assert result["failures"] == []
