from tools.qwen_capcard_lab.teacher_memory import build_teacher_memory, failure_pattern, memory_entry


def test_failure_pattern_json():
    assert failure_pattern({"reasons": ["JSON_INVALID"]}) == "json_or_schema_failure"


def test_failure_pattern_unknown_solver():
    assert failure_pattern({"reasons": ["unknown solver status appears faked as solved"]}) == "unknown_solver_fake_solved"


def test_failure_pattern_stale():
    assert failure_pattern({"reasons": ["stale Command Center reference used as direct evidence"]}) == "stale_reference_misuse"


def test_memory_entry_shape():
    entry = memory_entry({"family": "x"}, "m", "mode", {"reasons": ["JSON_INVALID"]})
    assert entry["task_family"] == "x"


def test_build_teacher_memory_counts_failures():
    memory = build_teacher_memory([{"task": {"family": "x"}, "model": "m", "runtime_mode": "r", "final_score": {"status": "FAIL", "reasons": ["JSON_INVALID"]}}])
    assert memory["entry_count"] == 1


def test_build_teacher_memory_skips_passes():
    memory = build_teacher_memory([{"final_score": {"status": "PASS", "reasons": []}}])
    assert memory["entry_count"] == 0
