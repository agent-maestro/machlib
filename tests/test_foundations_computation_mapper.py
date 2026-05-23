import json
from pathlib import Path

from tools import build_foundations_computation_mapper as mapper


def test_topic_spine_has_five_chapter_families():
    rows = mapper.topic_rows()
    assert len(mapper.family_rows(rows)) == 5


def test_logic_topics_present():
    labels = {row["topic_label"] for row in mapper.topic_rows()}
    assert {"propositional logic", "induction", "recursive definitions"} <= labels


def test_sets_topics_present():
    labels = {row["topic_label"] for row in mapper.topic_rows()}
    assert {"basic sets", "functions", "relational databases"} <= labels


def test_automata_topics_present():
    labels = {row["topic_label"] for row in mapper.topic_rows()}
    assert {"regular expressions", "finite-state automata", "non-regular languages"} <= labels


def test_grammar_topics_present():
    labels = {row["topic_label"] for row in mapper.topic_rows()}
    assert {"context-free grammars", "BNF", "pushdown automata"} <= labels


def test_turing_topics_present():
    labels = {row["topic_label"] for row in mapper.topic_rows()}
    assert {"Turing machines", "computability", "limits of computation"} <= labels


def test_all_topic_rows_are_original_internal_summaries():
    assert all(row["internal_summary_original"] is True for row in mapper.topic_rows())


def test_copied_text_false_everywhere():
    assert all(row["copied_text"] is False for row in mapper.topic_rows())


def test_public_ready_false_everywhere():
    assert all(row["public_ready"] is False for row in mapper.topic_rows())


def test_license_review_required_true_everywhere():
    assert all(row["license_review_required"] is True for row in mapper.topic_rows())


def test_no_theorem_open_problem_claims_in_not_claimed():
    for row in mapper.topic_rows():
        text = " ".join(row["not_claimed"])
        assert "not public theorem/proof/open-problem claim" in text


def test_capcard_candidates_generated():
    assert len(mapper.CAPCARD_CANDIDATES) >= 5


def test_eml_plan_generated_count_matches_topics():
    rows = mapper.topic_rows()
    assert len(mapper.eml_records(rows)) == len(rows)


def test_senses_plan_generated_for_each_family():
    demos = {row["candidate_senses_demo"] for row in mapper.topic_rows()}
    assert {"logic_senses", "relation_senses", "automata_senses", "grammar_senses", "turing_trace_senses"} <= demos


def test_qwen_tasks_generated_for_each_topic():
    assert all(row["candidate_qwen_tasks"] for row in mapper.topic_rows())


def test_guardrail_source_metadata():
    assert mapper.SOURCE["copied_text_included"] is False
    assert mapper.SOURCE["exercises_copied"] is False
    assert mapper.SOURCE["commercial_use_allowed_now"] is False


def test_candidate_card_has_false_action_fields():
    card = mapper.capcard_card("logic_truth_table_kernel", "Logic Truth Table Kernel")
    for key in [
        "marketplace_upload_performed",
        "production_marketplace_modified",
        "petal_api_upload_performed",
        "huggingface_upload_performed",
        "public_claim",
        "certified_safety_claim",
        "production_controller_claim",
        "theorem_proof_claim",
    ]:
        assert card[key] is False


def test_candidate_card_is_internal_only():
    card = mapper.capcard_card("logic_truth_table_kernel", "Logic Truth Table Kernel")
    assert card["visibility"] == "internal"
    assert card["safe_to_display_internally"] is True
    assert card["safe_to_publish_publicly"] is False


def test_qwen_plan_keeps_qwen_blocked():
    plan = mapper.qwen_plan()
    assert plan["existing_qwen_puzzle_curriculum_remains_blocked"] is True
    assert "row 2 validation_status=warn / solver_status=unknown" in plan["current_blockers"]


def test_qwen_plan_has_internal_lanes():
    plan = mapper.qwen_plan()
    assert "dfa_trace_puzzles" in plan["optional_internal_lanes"]
    assert plan["petal_api_upload_performed"] is False


def test_product_assessment_verdict_allowed():
    assert mapper.product_assessment()["verdict"] == "BUILD_COMPUTATION_SENSES_INTERNAL"


def test_command_card_internal_only():
    card = mapper.command_card()
    assert card["visibility"] == "internal"
    assert card["safe_to_publish_publicly"] is False
    assert card["deploy_performed"] is False


def test_mapper_cli_outputs_guardrail(tmp_path):
    out = tmp_path / "curriculum"
    mapper.generate_all(out)
    guardrail = json.loads((out / "guardrail_result_2026_05_23.json").read_text())
    assert guardrail["status"] == "PASS"
    assert guardrail["copied_text_included"] is False


def test_mapper_cli_outputs_topic_spine(tmp_path):
    out = tmp_path / "curriculum"
    mapper.generate_all(out)
    topic = json.loads((out / "topic_spine_2026_05_23.json").read_text())
    assert len(topic["chapter_families"]) == 5


def test_mapper_cli_outputs_capcard_plan(tmp_path):
    out = tmp_path / "curriculum"
    mapper.generate_all(out)
    plan = json.loads((out / "capcard_candidate_plan_2026_05_23.json").read_text())
    assert plan["candidate_count"] >= 5


def test_slug_is_stable():
    assert mapper.slug("Turing Machines") == "turing_machines"


def test_family_candidate_mapping():
    assert mapper.candidate_for_family("regular_expressions_fsa") == "dfa_trace_kernel"


def test_family_senses_mapping():
    assert mapper.senses_for_family("grammars") == "grammar_senses"
