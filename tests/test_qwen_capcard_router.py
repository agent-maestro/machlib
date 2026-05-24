from tools.qwen_capcard_lab.model_registry import ModelRuntime
from tools.qwen_capcard_lab.router import runtime_allowed, select_runtime, should_block_runtime


def rt(model="qwen3:30b", mode="api_schema_format_think_false", score=95, schema=1.0, no_go=0):
    return ModelRuntime(model, mode, schema_json_rate=schema, average_score=score, no_go_violation_count=no_go)


def test_runtime_allowed_good():
    assert runtime_allowed(rt()) is True


def test_runtime_blocks_no_go():
    assert runtime_allowed(rt(no_go=1)) is False


def test_runtime_blocks_low_schema():
    assert runtime_allowed(rt(schema=0.2)) is False


def test_select_prefers_qwen3_schema_default():
    selected = select_runtime({"family": "evidence_summary"}, [rt(), rt("qwen3-coder:30b", "api_schema_format", 99, 1)])
    assert selected.model == "qwen3:30b"


def test_select_coder_for_coder_family_if_good():
    selected = select_runtime({"family": "model_self_correction"}, [rt(), rt("qwen3-coder:30b", "api_schema_format", 99, 1)])
    assert selected.model == "qwen3-coder:30b"


def test_select_fallback_when_no_allowed():
    selected = select_runtime({"family": "x"}, [rt(schema=0.1)])
    assert selected.model == "qwen3:30b"


def test_block_runtime_after_forbidden_history():
    history = [{"score": {"reasons": ["forbidden_true_field"]}}, {"score": {"reasons": ["public_ready_must_be_false"]}}]
    assert should_block_runtime(history) is True


def test_do_not_block_runtime_with_clean_history():
    assert should_block_runtime([{"score": {"reasons": []}}]) is False
