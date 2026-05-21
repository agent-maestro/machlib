from hybrid_trace_eml.trace import increments, transition_counts, transitions


def test_increments():
    assert increments([1.0, 1.5, 3.0]) == [0.5, 1.5]


def test_transitions():
    assert transitions(["a", "b", "a"]) == [("a", "b"), ("b", "a")]


def test_transition_counts():
    assert transition_counts(["a", "b", "a", "b"]) == {"a->b": 2, "b->a": 1}
