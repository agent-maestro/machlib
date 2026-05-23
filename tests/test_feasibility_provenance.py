from tools.feasibility_algebra.provenance import ProvenanceRecord, combine_provenance


def test_direct_provenance_scores_higher_than_indirect():
    direct = ProvenanceRecord("a", "source", 0, True, 0.1)
    indirect = ProvenanceRecord("b", "source", 0, False, 0.1)
    assert direct.score() > indirect.score()


def test_stale_provenance_scores_lower():
    fresh = ProvenanceRecord("a", "source", 0, True, 0.1)
    stale = ProvenanceRecord("b", "source", 2000, True, 0.1)
    assert fresh.score() > stale.score()


def test_combine_empty_provenance_zero_score():
    assert combine_provenance([])["score"] == 0


def test_combine_provenance_counts_direct_records():
    result = combine_provenance([
        ProvenanceRecord("a", "source", 0, True, 0.1),
        ProvenanceRecord("b", "source", 0, False, 0.1),
    ])
    assert result["direct_count"] == 1
    assert result["record_count"] == 2
