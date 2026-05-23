import pytest

from tools import computation_curriculum_kernels as kernels


def test_truth_table_and_rows():
    result = kernels.logic_truth_table_kernel(("and", "p", "q"), ["p", "q"])
    assert len(result["rows"]) == 4
    assert [row["value"] for row in result["rows"]] == [False, False, False, True]


def test_truth_table_or_not():
    result = kernels.logic_truth_table_kernel(("or", "p", ("not", "q")), ["p", "q"])
    assert [row["value"] for row in result["rows"]] == [True, False, True, True]


def test_truth_table_implication():
    result = kernels.logic_truth_table_kernel(("implies", "p", "q"), ["p", "q"])
    assert [row["value"] for row in result["rows"]] == [True, True, False, True]


def test_eval_expr_unknown_op():
    with pytest.raises(ValueError):
        kernels.eval_expr(("xor", "p", "q"), {"p": True, "q": False})


def test_relation_reflexive_symmetric_transitive():
    result = kernels.set_relation_kernel({1, 2}, {(1, 1), (2, 2), (1, 2), (2, 1)})
    assert result["reflexive"] is True
    assert result["symmetric"] is True
    assert result["transitive"] is True


def test_relation_not_reflexive():
    result = kernels.set_relation_kernel({1, 2}, {(1, 1)})
    assert result["reflexive"] is False


def test_relation_not_symmetric():
    result = kernels.set_relation_kernel({1, 2}, {(1, 1), (2, 2), (1, 2)})
    assert result["symmetric"] is False


def test_relation_not_transitive():
    result = kernels.set_relation_kernel({1, 2, 3}, {(1, 2), (2, 3)})
    assert result["transitive"] is False


def test_dfa_accept_trace():
    result = kernels.dfa_trace_kernel({"even", "odd"}, {"a"}, {("even", "a"): "odd", ("odd", "a"): "even"}, "even", {"even"}, "aa")
    assert result["accepted"] is True
    assert [row["state"] for row in result["trace"]] == ["even", "odd", "even"]


def test_dfa_reject_trace():
    result = kernels.dfa_trace_kernel({"even", "odd"}, {"a"}, {("even", "a"): "odd", ("odd", "a"): "even"}, "even", {"even"}, "a")
    assert result["accepted"] is False


def test_dfa_missing_start():
    with pytest.raises(ValueError):
        kernels.dfa_trace_kernel({"q"}, {"a"}, {}, "missing", {"q"}, "")


def test_dfa_bad_symbol():
    with pytest.raises(ValueError):
        kernels.dfa_trace_kernel({"q"}, {"a"}, {}, "q", {"q"}, "b")


def test_dfa_missing_transition():
    with pytest.raises(ValueError):
        kernels.dfa_trace_kernel({"q"}, {"a"}, {}, "q", {"q"}, "a")


def test_regex_matches():
    result = kernels.regex_string_kernel(r"a*b", ["b", "ab", "aaab", "aba"])
    assert result["matches"] == {"b": True, "ab": True, "aaab": True, "aba": False}


def test_regex_empty_string():
    result = kernels.regex_string_kernel(r"a*", ["", "a", "b"])
    assert result["matches"][""] is True
    assert result["matches"]["b"] is False


def test_grammar_generates_base():
    result = kernels.grammar_derivation_kernel({"S": [[""]]}, "S", 1)
    assert "" in result["generated"]


def test_grammar_generates_bounded_language():
    result = kernels.grammar_derivation_kernel({"S": [["a", "S", "b"], [""]]}, "S", 4)
    assert "" in result["generated"]
    assert "ab" in result["generated"]


def test_grammar_marks_bounded_only():
    assert kernels.grammar_derivation_kernel({"S": [["x"]]}, "S", 2)["bounded_only"] is True


def test_pda_stack_trace():
    result = kernels.pda_stack_trace_placeholder([("push", "A"), ("push", "B"), ("pop", None)])
    assert result["trace"][-1]["stack"] == ["A"]


def test_pda_pop_empty_errors():
    with pytest.raises(ValueError):
        kernels.pda_stack_trace_placeholder([("pop", None)])


def test_pda_invalid_action_errors():
    with pytest.raises(ValueError):
        kernels.pda_stack_trace_placeholder([("peek", None)])


def test_turing_trace_reaches_halt():
    result = kernels.turing_machine_trace_kernel({("q0", "1"): ("q0", "1", 1), ("q0", "_"): ("halt", "_", 0)}, "11", "q0", {"halt"}, 10)
    assert result["final_state"] == "halt"


def test_turing_trace_stops_by_max_steps():
    result = kernels.turing_machine_trace_kernel({("q0", "1"): ("q0", "1", 0)}, "1", "q0", {"halt"}, 3)
    assert len(result["trace"]) == 3


def test_turing_trace_missing_transition_stops():
    result = kernels.turing_machine_trace_kernel({}, "1", "q0", {"halt"}, 3)
    assert len(result["trace"]) == 1


@pytest.mark.parametrize(
    "result",
    [
        kernels.logic_truth_table_kernel(("and", "p", "q"), ["p", "q"]),
        kernels.set_relation_kernel({1}, {(1, 1)}),
        kernels.dfa_trace_kernel({"q"}, {"a"}, {("q", "a"): "q"}, "q", {"q"}, "a"),
        kernels.regex_string_kernel("a", ["a"]),
        kernels.grammar_derivation_kernel({"S": [["a"]]}, "S", 1),
        kernels.pda_stack_trace_placeholder([("push", "A")]),
        kernels.turing_machine_trace_kernel({}, "", "q0", {"halt"}, 1),
    ],
)
def test_all_kernels_mark_bounded_only(result):
    assert result["bounded_only"] is True


def test_run_all_summary(tmp_path):
    summary = kernels.run_all(tmp_path)
    assert summary["kernel_count"] == 7
    assert summary["passed_count"] == 7
    assert summary["failed_count"] == 0


def test_run_all_writes_summary(tmp_path):
    kernels.run_all(tmp_path)
    assert (tmp_path / "computation_kernel_execution_summary_2026_05_23.json").exists()


def test_summary_has_no_public_claims(tmp_path):
    summary = kernels.run_all(tmp_path)
    assert summary["theorem_proof_claim"] is False
    assert summary["open_problem_claim"] is False
    assert summary["public_ready"] is False


def test_logic_output_file_written(tmp_path):
    kernels.run_all(tmp_path)
    assert (tmp_path / "logic_truth_table_result_2026_05_23.json").exists()


def test_turing_output_file_written(tmp_path):
    kernels.run_all(tmp_path)
    assert (tmp_path / "turing_trace_result_2026_05_23.json").exists()


def test_pda_placeholder_not_full_theorem():
    result = kernels.pda_stack_trace_placeholder([("push", "A")])
    assert result["not_full_pda_theorem"] is True


def test_regex_result_is_finite_evidence():
    result = kernels.regex_string_kernel(r"(ab)*", ["", "ab", "aba"])
    assert len(result["matches"]) == 3


def test_grammar_respects_depth():
    shallow = kernels.grammar_derivation_kernel({"S": [["a", "S"], ["b"]]}, "S", 1)
    deep = kernels.grammar_derivation_kernel({"S": [["a", "S"], ["b"]]}, "S", 3)
    assert len(deep["generated"]) >= len(shallow["generated"])


def test_relation_kernel_name():
    assert kernels.set_relation_kernel({1}, {(1, 1)})["kernel"] == "set_relation_kernel"


def test_dfa_kernel_name():
    result = kernels.dfa_trace_kernel({"q"}, {"a"}, {("q", "a"): "q"}, "q", {"q"}, "")
    assert result["kernel"] == "dfa_trace_kernel"


def test_logic_kernel_name():
    assert kernels.logic_truth_table_kernel("p", ["p"])["kernel"] == "logic_truth_table_kernel"


def test_invalid_not_expression_missing_variable_errors():
    with pytest.raises(KeyError):
        kernels.logic_truth_table_kernel(("not", "missing"), ["p"])
