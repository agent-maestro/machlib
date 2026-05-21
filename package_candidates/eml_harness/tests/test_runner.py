from eml_harness.runner import summarize_results


def test_summarize_results_counts_statuses():
    summary = summarize_results([
        {"record_id": "a", "status": "PASS"},
        {"record_id": "b", "status": "FAIL"},
        {"record_id": "c", "status": "SKIP"},
        {"record_id": "d", "status": "NOPE"},
    ])

    assert summary == {"total": 4, "pass": 1, "fail": 1, "skip": 1, "invalid": 1}
