import importlib.util
from pathlib import Path


ROOT = Path("corpus/eml_stochastic_hybrid_draft")
TOOL = Path("tools/run_stochastic_hybrid_trace_harness.py")


def load_harness():
    spec = importlib.util.spec_from_file_location("run_stochastic_hybrid_trace_harness", TOOL)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_transition_counts_fixture():
    harness = load_harness()
    assert harness.transition_counts([1, 2, 3, 1, 2]) == {
        "1->2": 2,
        "2->3": 1,
        "3->1": 1,
        "3->2": 0,
    }


def test_one_hot_events_fixture():
    harness = load_harness()
    rows = harness.one_hot_events(["1->2", "2->3", "1->2"])
    assert rows[0]["1->2"] == 1
    assert rows[0]["2->3"] == 0
    assert rows[1]["2->3"] == 1


def test_harness_build_passes(tmp_path):
    harness = load_harness()
    execution, roundtrip, spec = harness.build(ROOT, tmp_path)
    assert execution["record_count"] == 12
    assert execution["execution_status"] == "PASS"
    assert execution["failed"] == 0
    assert roundtrip["failed"] == 0
    assert roundtrip["roundtrip_status"] in {"PASS", "WARN"}
    assert spec["trace_specs"]
    for artifact in execution["eml_artifacts"]:
        text = Path(artifact).read_text()
        assert ("import " + "Mathlib") not in text
        assert ("from " + "Mathlib") not in text
