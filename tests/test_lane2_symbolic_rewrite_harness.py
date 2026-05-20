from pathlib import Path

import pytest

from tools import run_lane2_symbolic_rewrite_harness as harness


ROOT = Path("corpus/eml_lanes_draft")
OUT = ROOT / "lane_2_calculus_special_functions" / "symbolic_rewrite_result_2026_05_20.json"


@pytest.fixture(scope="module")
def result():
    return harness.execute(ROOT, OUT)


def row(result, record_id):
    for item in result["results"]:
        if item["record_id"] == record_id:
            return item
    raise AssertionError(f"missing {record_id}")


def test_lane2_seed_count(result):
    assert result["seed_count"] == 3
    assert result["passed"] == 3
    assert result["failed"] == 0


def test_primitive_specs_include_all_required_ids():
    specs = harness.load_primitive_specs(ROOT)
    ids = {item["primitive_id"] for item in specs}
    assert ids == harness.REQUIRED_PRIMITIVES


def test_guarded_log_exp_rewrite_succeeds_and_unguarded_is_blocked(result):
    exp_log = row(result, "exp_log_formal_inverse_draft_v0")
    guarded = {(item["input"], item["guard"]): item for item in exp_log["guarded_rewrites"]}
    assert guarded[("log(exp(x))", "FORMAL_SYMBOLIC_INVERSE_GUARD")]["output"] == "x"
    assert guarded[("log(exp(x))", "FORMAL_SYMBOLIC_INVERSE_GUARD")]["status"] == "PASS"
    blocked = [item for item in exp_log["blocked_rewrites"] if item["input"] == "log(exp(x)"]
    assert blocked == []
    blocked = [item for item in exp_log["blocked_rewrites"] if item["input"] == "log(exp(x))"]
    assert blocked and blocked[0]["status"] == "WARN_BLOCKED_BY_MISSING_GUARD"


def test_exp_log_positive_domain_guard(result):
    exp_log = row(result, "exp_log_formal_inverse_draft_v0")
    guarded = {(item["input"], item["guard"]): item for item in exp_log["guarded_rewrites"]}
    assert guarded[("exp(log(x))", "POSITIVE_DOMAIN_GUARD")]["output"] == "x"
    blocked = [item for item in exp_log["blocked_rewrites"] if item["input"] == "exp(log(x))"]
    assert blocked and blocked[0]["status"] == "WARN_BLOCKED_BY_MISSING_GUARD"


def test_guarded_trig_rewrite_succeeds_and_unguarded_is_blocked(result):
    trig = row(result, "trig_pythagorean_symbolic_draft_v0")
    guarded = trig["guarded_rewrites"][0]
    assert guarded["input"] == "sin(x)^2 + cos(x)^2"
    assert guarded["guard"] == "TRIG_SYMBOLIC_IDENTITY_GUARD"
    assert guarded["output"] == "1"
    assert guarded["status"] == "PASS"
    blocked = trig["blocked_rewrites"][0]
    assert blocked["status"] == "WARN_BLOCKED_BY_MISSING_GUARD"


def test_guarded_sqrt_square_rewrite_and_unsafe_rewrites(result):
    pow_sqrt = row(result, "pow_square_root_symbolic_draft_v0")
    guarded = pow_sqrt["guarded_rewrites"][0]
    assert guarded["input"] == "sqrt(x)^2"
    assert guarded["guard"] == "NONNEGATIVE_DOMAIN_GUARD"
    assert guarded["output"] == "x"
    assert guarded["status"] == "PASS"
    blocked = {(item["input"], item.get("proposed_output")): item for item in pow_sqrt["blocked_rewrites"]}
    assert blocked[("sqrt(x^2)", "x")]["status"] == "BLOCKED"
    assert "sign information" in blocked[("sqrt(x^2)", "x")]["reason"]
    assert blocked[("sqrt(x^2)", "abs(x)")]["status"] == "BLOCKED"
    assert "NEEDS_STRUCTURE_LAYER" in blocked[("sqrt(x^2)", "abs(x)")]["reason"]


def test_public_and_dependency_guardrails_remain_false():
    seeds = harness.load_lane2_seeds(ROOT)
    specs = harness.load_primitive_specs(ROOT)
    for seed in seeds.values():
        draft = seed.draft
        assert draft["public_ready"] is False
        assert draft["upload_allowed"] is False
        assert draft["mathlib_dependency"] is False
    for spec in specs:
        assert spec["public_ready"] is False
        assert spec["upload_allowed"] is False
        assert spec["mathlib_dependency"] is False


def test_result_guardrails(result):
    assert result["zero_mathlib_status"] == "PASS"
    assert result["rewrite_status"] == "PASS"
    assert result["guardrails"]["no_mathlib_dependency"] is True
    assert result["guardrails"]["no_hf_upload"] is True
    assert result["guardrails"]["no_petal_upload"] is True
    assert result["guardrails"]["no_package_publish"] is True
    assert result["guardrails"]["no_hardware"] is True
    assert result["guardrails"]["no_forge_compiler_change"] is True
    assert result["guardrails"]["no_public_theorem_claim"] is True
