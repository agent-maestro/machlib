"""Unit tests for the multi-proof BFS engine."""
from __future__ import annotations

import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from gym.multi_proof import MultiProofSearch, classify_style
from gym.verifiers import HeuristicVerifier


# ─── style classifier ─────────────────────────────────────────────


def test_classify_style_direct():
    assert classify_style(["rfl"]) == "direct"
    assert classify_style(["exact h"]) == "direct"


def test_classify_style_automation_wins_over_simp_when_first():
    # First-match-wins, automation comes after direct in the table
    assert classify_style(["decide"]) == "automation"
    assert classify_style(["norm_num"]) == "automation"
    assert classify_style(["ring"]) == "automation"


def test_classify_style_simp():
    assert classify_style(["simp"]) == "simplification"
    assert classify_style(["simp [foo]"]) == "simplification"


def test_classify_style_rewriting():
    assert classify_style(["unfold foo"]) == "rewriting"
    assert classify_style(["rw [foo]"]) == "rewriting"


def test_classify_style_eml_specific():
    assert classify_style(["eml_auto"]) == "eml_specific"
    assert classify_style(["exact exp_isEMLElementary"]) == "eml_specific"


def test_classify_style_mixed_fallback():
    assert classify_style(["intro h", "use 0"]) == "mixed"


# ─── heuristic verifier ───────────────────────────────────────────


def test_heuristic_rfl_closes_x_eq_x():
    v = HeuristicVerifier()
    assert v.verify("theorem t : x = x := by sorry", ["rfl"]) is True


def test_heuristic_rfl_does_not_close_x_eq_y():
    v = HeuristicVerifier()
    assert v.verify("theorem t : x = y := by sorry", ["rfl"]) is False


def test_heuristic_decide_on_literal_equality():
    v = HeuristicVerifier()
    assert v.verify("theorem t : 1 = 1 := by sorry", ["decide"]) is True


def test_heuristic_trivial_on_x_eq_x():
    v = HeuristicVerifier()
    assert v.verify("theorem t : 5 = 5 := by sorry", ["trivial"]) is True


def test_heuristic_rejects_unknown_tactic():
    v = HeuristicVerifier()
    assert v.verify("theorem t : x = x := by sorry", ["nlinarith"]) is False


# ─── BFS engine end-to-end (with heuristic verifier) ──────────────


def test_engine_finds_rfl_proof():
    search = MultiProofSearch(max_depth=1, max_proofs=5)
    proofs, stats = search.find_all_proofs("theorem t : x = x := by sorry")
    assert stats.proofs_found > 0
    sequences = [p.tactic_sequence for p in proofs]
    assert ("rfl",) in sequences


def test_engine_marks_shortest_optimal():
    search = MultiProofSearch(max_depth=1, max_proofs=5)
    proofs, _ = search.find_all_proofs("theorem t : 1 = 1 := by sorry")
    optimals = [p for p in proofs if p.is_optimal]
    assert optimals
    shortest_count = min(p.tactic_count for p in proofs)
    for p in optimals:
        assert p.tactic_count == shortest_count


def test_engine_respects_max_proofs():
    search = MultiProofSearch(max_depth=1, max_proofs=2)
    proofs, _ = search.find_all_proofs("theorem t : 1 = 1 := by sorry")
    assert len(proofs) <= 2


def test_engine_finds_no_proof_for_open_goal():
    # Heuristic verifier can't close anything that isn't trivial; an
    # arbitrary equality should yield zero proofs in shallow depth.
    search = MultiProofSearch(max_depth=1, max_proofs=5, timeout_seconds=2.0)
    proofs, _ = search.find_all_proofs(
        "theorem hard : foo bar = baz qux := by sorry",
    )
    assert proofs == []


def test_proof_record_to_machlib_proof_shape():
    search = MultiProofSearch(max_depth=1, max_proofs=1)
    proofs, _ = search.find_all_proofs("theorem t : 7 = 7 := by sorry")
    assert proofs
    rec = proofs[0].to_machlib_proof("p1", eml_node_cost=2)
    assert rec["id"] == "p1"
    assert rec["tactic_count"] == len(rec["tactics"])
    assert rec["eml_node_cost"] == 2
    assert "discovered_by" in rec
    assert "discovery_date" in rec


def test_engine_emits_stats():
    search = MultiProofSearch(max_depth=2, max_proofs=3, timeout_seconds=2.0)
    _, stats = search.find_all_proofs("theorem t : x = x := by sorry")
    assert stats.candidates_tried > 0
    assert stats.elapsed_seconds > 0
    # At least one of the budget exits should fire on a non-trivial run.
    assert (stats.hit_proof_limit or stats.hit_depth_limit
            or stats.hit_timeout or stats.proofs_found > 0)
