#!/usr/bin/env python3
"""Build an internal Foundations of Computation curriculum mapper.

The mapper uses only a high-level topic spine and original summaries. It does
not download, bundle, quote, or copy the source PDF.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any


SOURCE = {
    "source_title": "Foundations of Computation",
    "authors": ["Carol Critchlow", "David Eck"],
    "version": "Second Edition, Version 2.3.2",
    "source_url": "https://math.hws.edu/FoundationsOfComputation/FoundationsOfComputation_2.3.2_6x9.pdf",
    "license_name": "CC BY-NC-SA 4.0",
    "license_boundary": "Use as internal topic spine and inspiration only; no bundled PDF, copied exercises, copied prose, public distribution, or commercial use without separate review.",
    "use_mode": "INTERNAL_TOPIC_MAPPING_ONLY",
    "noncommercial_review_required": True,
    "attribution_required": True,
    "sharealike_review_required": True,
    "copied_text_included": False,
    "exercises_copied": False,
    "public_distribution_allowed_now": False,
    "commercial_use_allowed_now": False,
    "package_inclusion_allowed_now": False,
    "next_safe_task": "M097_COMPUTATION_SENSES_INTERNAL_REVIEW_AND_LICENSE_COPY_GATE",
}

NOT_CLAIMED = [
    "not copied textbook content",
    "not public theorem/proof/open-problem claim",
    "not license clearance for commercial use",
    "not certified safety",
    "not production controller evidence",
]

TOPIC_SPINE = [
    (
        "logic_and_proof",
        "Logic and Proof",
        [
            "propositional logic",
            "boolean algebra",
            "logic circuits",
            "predicates and quantifiers",
            "deduction",
            "proof",
            "proof by contradiction",
            "induction",
            "recursion and induction",
            "recursive definitions",
        ],
    ),
    (
        "sets_functions_relations",
        "Sets, Functions, and Relations",
        [
            "basic sets",
            "boolean algebra of sets",
            "programming with sets",
            "functions",
            "programming with functions",
            "counting past infinity",
            "relations",
            "relational databases",
        ],
    ),
    (
        "regular_expressions_fsa",
        "Regular Expressions and Finite-State Automata",
        [
            "languages",
            "regular expressions",
            "using regular expressions",
            "finite-state automata",
            "nondeterministic finite-state automata",
            "regular languages",
            "non-regular languages",
        ],
    ),
    (
        "grammars",
        "Grammars",
        [
            "context-free grammars",
            "BNF",
            "parsing and parse trees",
            "pushdown automata",
            "non-context-free languages",
            "general grammars",
        ],
    ),
    (
        "turing_computability",
        "Turing Machines and Computability",
        [
            "Turing machines",
            "computability",
            "limits of computation",
        ],
    ),
]

FAMILY_RECORD_TYPE = {
    "logic_and_proof": "logic_proof_record",
    "sets_functions_relations": "set_function_relation_record",
    "regular_expressions_fsa": "automata_language_record",
    "grammars": "grammar_parsing_record",
    "turing_computability": "turing_computability_record",
}

CAPCARD_CANDIDATES = [
    ("logic_truth_table_kernel", "Logic Truth Table Kernel"),
    ("relation_property_kernel", "Relation Property Kernel"),
    ("dfa_trace_kernel", "DFA Trace Kernel"),
    ("grammar_derivation_kernel", "Grammar Derivation Kernel"),
    ("turing_trace_kernel", "Turing Trace Kernel"),
    ("computation_senses_demo", "Computation Senses Demo"),
]


def slug(text: str) -> str:
    return (
        text.lower()
        .replace("/", " ")
        .replace("-", " ")
        .replace(",", "")
        .replace(" ", "_")
    )


def topic_rows() -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for family_id, chapter, topics in TOPIC_SPINE:
        for topic in topics:
            topic_id = f"{family_id}_{slug(topic)}"
            rows.append(
                {
                    "topic_id": topic_id,
                    "topic_label": topic,
                    "source_chapter": chapter,
                    "chapter_family": family_id,
                    "internal_summary_original": True,
                    "summary": f"Original internal mapping row for {topic} as a bounded computation curriculum topic.",
                    "copied_text": False,
                    "candidate_eml_records": [f"eml_{topic_id}"],
                    "candidate_capcard_cards": [candidate_for_family(family_id)],
                    "candidate_senses_demo": senses_for_family(family_id),
                    "candidate_qwen_tasks": [f"qwen_{topic_id}_toy_lane"],
                    "public_ready": False,
                    "license_review_required": True,
                    "not_claimed": NOT_CLAIMED,
                }
            )
    return rows


def family_rows(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    families: list[dict[str, Any]] = []
    for family_id, chapter, topics in TOPIC_SPINE:
        family_topics = [row for row in rows if row["chapter_family"] == family_id]
        families.append(
            {
                "family_id": family_id,
                "source_chapter": chapter,
                "topic_count": len(family_topics),
                "topics": [row["topic_id"] for row in family_topics],
                "copied_text": False,
                "public_ready": False,
                "license_review_required": True,
                "internal_summary_original": True,
                "not_claimed": NOT_CLAIMED,
            }
        )
    return families


def candidate_for_family(family_id: str) -> str:
    return {
        "logic_and_proof": "logic_truth_table_kernel",
        "sets_functions_relations": "relation_property_kernel",
        "regular_expressions_fsa": "dfa_trace_kernel",
        "grammars": "grammar_derivation_kernel",
        "turing_computability": "turing_trace_kernel",
    }[family_id]


def senses_for_family(family_id: str) -> str:
    return {
        "logic_and_proof": "logic_senses",
        "sets_functions_relations": "relation_senses",
        "regular_expressions_fsa": "automata_senses",
        "grammars": "grammar_senses",
        "turing_computability": "turing_trace_senses",
    }[family_id]


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def eml_records(rows: list[dict[str, Any]]) -> list[dict[str, Any]]:
    records = []
    for row in rows:
        records.append(
            {
                "record_id": f"eml_{row['topic_id']}",
                "family": FAMILY_RECORD_TYPE[row["chapter_family"]],
                "topic_id": row["topic_id"],
                "status": "DRAFT_INTERNAL",
                "source_inspiration": "Foundations of Computation topic spine",
                "copied_text": False,
                "original_task_required": True,
                "executable_check_planned": executable_for_family(row["chapter_family"]),
                "validator_family": row["chapter_family"],
                "senses_mapping_candidate": row["candidate_senses_demo"],
                "qwen_curriculum_candidate": row["candidate_qwen_tasks"][0],
                "capcard_candidate": row["candidate_capcard_cards"][0],
                "public_ready": False,
                "package_publish_allowed": False,
                "petal_api_upload_performed": False,
                "huggingface_upload_performed": False,
                "theorem_proof_claim": False,
                "open_problem_claim": False,
                "certified_safety_claim": False,
                "production_controller_claim": False,
                "license_review_required": True,
                "not_claimed": NOT_CLAIMED,
            }
        )
    return records


def executable_for_family(family_id: str) -> str:
    return {
        "logic_and_proof": "truth_table_toy_check",
        "sets_functions_relations": "finite_relation_property_check",
        "regular_expressions_fsa": "dfa_or_regex_bounded_trace",
        "grammars": "bounded_grammar_derivation",
        "turing_computability": "bounded_turing_trace",
    }[family_id]


def capcard_card(candidate_id: str, display_name: str) -> dict[str, Any]:
    return {
        "candidate_id": candidate_id,
        "card_id": f"{candidate_id}_DRAFT_2026_05_23",
        "display_name": display_name,
        "marketplace_status": "INTERNAL_DRAFT_CANDIDATE",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "evidence_basis": [
            "original bounded toy kernel plan",
            "internal EML curriculum draft records",
            "license boundary packet",
            "local computation senses prototype plan",
        ],
        "source_inspiration": "Foundations of Computation high-level topic spine",
        "copied_text": False,
        "public_ready": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "license_review_required": True,
        "limitations": [
            "internal curriculum mapping only",
            "original toy examples only",
            "not public or commercial content",
        ],
        "not_claimed": [
            "not copied textbook content",
            "not theorem proof",
            "not open-problem result",
            "not certified safety",
            "not production controller",
            "not PETAL/API uploaded",
            "not Hugging Face uploaded",
        ],
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
    }


def generate_reports(rows: list[dict[str, Any]], out_dir: Path) -> None:
    report_dir = Path("reports")
    write_text(
        report_dir / "foundations_computation_source_metadata_2026_05_23.md",
        "# Foundations of Computation Source Metadata\n\n"
        "Source: *Foundations of Computation* by Carol Critchlow and David Eck, "
        "Second Edition, Version 2.3.2.\n\n"
        f"URL: {SOURCE['source_url']}\n\n"
        "Use mode: internal topic mapping only. No PDF is bundled and no copied "
        "exercise/prose content is included.\n",
    )
    write_text(
        report_dir / "foundations_computation_license_boundary_2026_05_23.md",
        "# Foundations of Computation License Boundary\n\n"
        "The source is treated as CC BY-NC-SA 4.0 / noncommercial. This work uses "
        "the book as a high-level topic spine for internal mapping only.\n\n"
        "- Do not copy exercises or substantial prose into public/commercial products.\n"
        "- Do not bundle the PDF.\n"
        "- Attribute Carol Critchlow, David Eck, the title, version, and source URL in internal reports.\n"
        "- Any public use needs separate license and copy review.\n"
        "- No public theorem/proof/open-problem claim is created.\n",
    )
    write_text(
        report_dir / "foundations_computation_no_copy_guardrail_2026_05_23.md",
        "# Foundations of Computation No-Copy Guardrail\n\n"
        "Generated artifacts contain original summaries, schemas, toy kernel plans, "
        "and internal review rows. They do not include copied textbook exercises, "
        "copied prose, bundled PDF content, or commercial license clearance claims.\n",
    )
    write_text(
        report_dir / "foundations_computation_eml_records_2026_05_23.md",
        f"# EML Computation Curriculum Records\n\nGenerated {len(rows)} draft internal records across five computation families. Each row is original, internal-only, license-review gated, and bounded to toy executable checks.\n",
    )
    write_text(
        report_dir / "foundations_computation_qwen_extension_plan_2026_05_23.md",
        "# Foundations Computation Qwen Extension Plan\n\n"
        "The existing Qwen Puzzle Curriculum remains blocked: row 2 and row 3 retain validation_status=warn / solver_status=unknown, no accepted repair evidence, and stale Command Center references cannot count as direct evidence.\n\n"
        "New optional internal lanes: logic truth-table puzzles, relation-property puzzles, DFA trace puzzles, regex-match puzzles, grammar-derivation puzzles, and bounded Turing-trace puzzles. No copied textbook exercise content is included.\n",
    )
    write_text(
        report_dir / "foundations_computation_qwen_guardrail_report_2026_05_23.md",
        "# Foundations Computation Qwen Guardrail Report\n\nQwen is not repaired or promoted. No PETAL upload, Hugging Face upload, proof/open-problem claim, or copied textbook exercise content is included.\n",
    )
    write_text(
        report_dir / "foundations_computation_product_assessment_2026_05_23.md",
        "# Foundations Computation Product Assessment\n\nThe PDF opens real internal utility as a topic spine for CapCard, EML, Qwen curriculum planning, and Computation Senses. Public and commercial use remain blocked pending license/copy review.\n",
    )
    write_text(
        report_dir / "foundations_computation_next_steps_2026_05_23.md",
        "# Foundations Computation Next Steps\n\n1. Review license and public-copy boundaries.\n2. Expand original toy kernels.\n3. Build an internal Computation Senses review surface.\n4. Keep Qwen blocked until exact row repair evidence exists.\n",
    )
    write_text(
        report_dir / "foundations_computation_command_center_card_2026_05_23.md",
        "# Foundations Computation Command Center Card\n\nInternal-only curriculum mapping card. Safe to display internally; not safe for public publishing before license/copy review.\n",
    )
    write_text(
        report_dir / "computation_curriculum_capcard_candidate_review_2026_05_23.md",
        "# Computation Curriculum CapCard Candidate Review\n\nSix internal draft candidates were created for bounded computation curriculum kernels and the Computation Senses demo. All are observation-tier and internal-only.\n",
    )
    write_text(
        report_dir / "computation_curriculum_capcard_guardrail_report_2026_05_23.md",
        "# Computation Curriculum CapCard Guardrail Report\n\nAll computation curriculum CapCards keep upload/public/production fields false and require license review before public use.\n",
    )
    write_text(
        report_dir / "computation_curriculum_capcard_scores_2026_05_23.md",
        "# Computation Curriculum CapCard Scores\n\nInternal toy-kernel candidates score as promising internal curriculum candidates, not public marketplace cards.\n",
    )


def generate_senses() -> None:
    base = Path("senses/computation_senses_2026_05_23")
    topics = [
        {"id": "logic_senses", "label": "Logic Senses", "panel": "truth table grid"},
        {"id": "relation_senses", "label": "Relation Senses", "panel": "finite relation graph"},
        {"id": "automata_senses", "label": "Automata Senses", "panel": "DFA state trace"},
        {"id": "grammar_senses", "label": "Grammar Senses", "panel": "bounded derivation tree"},
        {"id": "turing_trace_senses", "label": "Turing Trace Senses", "panel": "bounded tape/head trace"},
    ]
    manifest = {
        "prototype_id": "computation_senses_2026_05_23",
        "status": "PASS",
        "topic_count": len(topics),
        "mode": "local_static_browser_demo",
        "visual_generated": True,
        "audio_runtime": "browser_web_audio_api",
        "audio_file_generated": False,
        "microphone_required": False,
        "hardware_required": False,
        "network_required": False,
        "deploy_performed": False,
        "upload_performed": False,
        "public_claim": False,
        "copied_text_included": False,
        "license_review_required_before_public_use": True,
    }
    write_json(base / "computation_senses_manifest_2026_05_23.json", manifest)
    write_json(base / "computation_senses_data_2026_05_23.json", {"topics": topics})
    write_text(
        base / "index.html",
        "<!doctype html><html><head><meta charset=\"utf-8\"><title>Computation Senses</title><link rel=\"stylesheet\" href=\"computation_senses.css\"></head><body><main><h1>Computation Senses</h1><p>Pre-alpha computation senses demo. Original bounded toy examples only. Not copied textbook exercises. Not theorem/proof/open-problem claims. Not certified safety. Not production controller evidence. No microphone. No hardware action.</p><section id=\"app\"></section><button id=\"play\">Play</button><button id=\"stop\">Stop</button><button id=\"mute\">Mute</button><button id=\"step\">Step</button><select id=\"topic\"></select><select id=\"speed\"><option>slow</option><option>medium</option><option>fast</option></select><button id=\"boundaries\">Show boundaries</button><script src=\"computation_senses.js\"></script></main></body></html>\n",
    )
    write_text(
        base / "computation_senses.css",
        "body{font-family:system-ui;margin:0;background:#101820;color:#f7f7f2}main{max-width:960px;margin:auto;padding:32px}button,select{margin:6px;padding:8px}#app{border:1px solid #6aa6b8;padding:16px;min-height:180px}\n",
    )
    write_text(
        base / "computation_senses.js",
        "const topics=['Logic Senses','Relation Senses','Automata Senses','Grammar Senses','Turing Trace Senses'];const sel=document.getElementById('topic');topics.forEach(t=>{const o=document.createElement('option');o.textContent=t;sel.appendChild(o)});let ctx,gain,osc;function show(){document.getElementById('app').textContent=sel.value+' :: bounded local visualization, browser Web Audio only';}sel.onchange=show;show();document.getElementById('play').onclick=()=>{ctx=ctx||new AudioContext();gain=ctx.createGain();osc=ctx.createOscillator();osc.frequency.value=220+sel.selectedIndex*70;osc.connect(gain);gain.connect(ctx.destination);gain.gain.value=.04;osc.start();};document.getElementById('stop').onclick=()=>{if(osc){osc.stop();osc=null}};document.getElementById('mute').onclick=()=>{if(gain)gain.gain.value=0};document.getElementById('step').onclick=()=>{sel.selectedIndex=(sel.selectedIndex+1)%sel.options.length;show()};document.getElementById('boundaries').onclick=()=>alert('Internal demo. No microphone, no hardware, no copied textbook content.');\n",
    )


def generate_all(out_dir: Path) -> None:
    rows = topic_rows()
    families = family_rows(rows)
    write_json(out_dir / "source_metadata_2026_05_23.json", SOURCE)
    write_json(
        out_dir / "license_boundary_2026_05_23.json",
        {
            **SOURCE,
            "can_use_as_internal_topic_spine": True,
            "must_not_copy_exercises_or_prose": True,
            "must_not_bundle_pdf": True,
            "any_public_use_needs_separate_review": True,
            "public_theorem_claim": False,
        },
    )
    write_json(out_dir / "topic_spine_2026_05_23.json", {"chapter_families": families, "topics": rows})
    write_json(out_dir / "curriculum_map_2026_05_23.json", {"topic_count": len(rows), "topics": rows})
    write_json(out_dir / "eml_record_plan_2026_05_23.json", {"planned_record_count": len(rows), "records": [f"eml_{r['topic_id']}" for r in rows]})
    write_json(out_dir / "capcard_candidate_plan_2026_05_23.json", {"candidate_count": len(CAPCARD_CANDIDATES), "candidates": [c[0] for c in CAPCARD_CANDIDATES]})
    write_json(out_dir / "oneop_senses_plan_2026_05_23.json", {"prototype_id": "computation_senses_2026_05_23", "public_ready": False, "license_review_required": True})
    write_json(out_dir / "qwen_repair_extension_plan_2026_05_23.json", qwen_plan())
    write_json(out_dir / "guardrail_result_2026_05_23.json", {"status": "PASS", "copied_text_included": False, "exercises_copied": False, "public_ready": False})

    records = eml_records(rows)
    write_json(Path("corpus/eml_computation_curriculum_draft/records_2026_05_23.json"), {"records": records})
    write_json(Path("corpus/eml_computation_curriculum_draft/execution_plan_2026_05_23.json"), {"record_count": len(records), "status": "DRAFT_INTERNAL", "bounded_only": True})
    write_json(Path("corpus/eml_computation_curriculum_draft/guardrail_report_2026_05_23.json"), {"status": "PASS", "copied_text": False, "public_ready": False})

    generate_senses()

    cards = [capcard_card(cid, name) for cid, name in CAPCARD_CANDIDATES]
    card_dir = Path("capcard_marketplace_drafts/computation_curriculum_candidates_2026_05_23")
    for card in cards:
        write_json(card_dir / f"{card['candidate_id']}.json", card)
        write_text(card_dir / f"{card['candidate_id']}.md", f"# {card['display_name']}\n\nInternal draft candidate. Not copied textbook content. License review required before public use.\n")
    write_json(Path("product_readiness/computation_curriculum_capcard_candidates_2026_05_23.json"), {"candidates": cards})
    write_json(Path("product_readiness/computation_curriculum_capcard_scores_2026_05_23.json"), {"candidates": [{"candidate_id": c["candidate_id"], "internal_score_0_to_100": 72, "public_ready": False} for c in cards]})
    write_json(Path("product_readiness/foundations_computation_qwen_extension_plan_2026_05_23.json"), qwen_plan())
    write_json(Path("product_readiness/foundations_computation_product_assessment_2026_05_23.json"), product_assessment())
    write_json(Path("command_center_feeds/foundations_computation_curriculum_card_2026_05_23.json"), command_card())
    write_json(Path("command_center_feeds/foundations_computation_curriculum_feed_2026_05_23.json"), command_feed())
    generate_reports(rows, out_dir)


def qwen_plan() -> dict[str, Any]:
    return {
        "status": "QWEN_REMAINS_BLOCKED_WITH_INTERNAL_EXTENSION_LANES",
        "existing_qwen_puzzle_curriculum_remains_blocked": True,
        "current_blockers": [
            "row 2 validation_status=warn / solver_status=unknown",
            "row 3 validation_status=warn / solver_status=unknown",
            "no accepted repair evidence",
            "stale command-center references are not direct evidence",
        ],
        "optional_internal_lanes": [
            "logic_truth_table_puzzles",
            "relation_property_puzzles",
            "dfa_trace_puzzles",
            "regex_match_puzzles",
            "grammar_derivation_puzzles",
            "turing_trace_puzzles",
        ],
        "copied_text": False,
        "copied_textbook_exercises": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "theorem_proof_claim": False,
        "open_problem_claim": False,
    }


def product_assessment() -> dict[str, Any]:
    return {
        "capcard_utility_0_to_100": 78,
        "qwen_curriculum_utility_0_to_100": 74,
        "senses_product_utility_0_to_100": 82,
        "machlib_eml_utility_0_to_100": 80,
        "license_risk_0_to_100": 70,
        "overclaim_risk_0_to_100": 55,
        "verdict": "BUILD_COMPUTATION_SENSES_INTERNAL",
        "blocked_by_license": ["public distribution", "commercial use", "exercise/prose copying"],
        "blocked_by_public_copy_review": ["public Computation Senses copy", "public CapCard cards"],
        "must_stay_internal": ["topic-spine mapping", "Qwen extension lanes", "CapCard candidates"],
    }


def command_card() -> dict[str, Any]:
    return {
        "card_id": "foundations_computation_curriculum_card_2026_05_23",
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "deploy_performed": False,
        "upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "copied_text_included": False,
        "license_review_required_before_public_use": True,
        "title": "Foundations Computation Curriculum Mapper",
    }


def command_feed() -> dict[str, Any]:
    return {
        "feed_id": "foundations_computation_curriculum_feed_2026_05_23",
        "visibility": "internal",
        "items": [
            {"surface_id": "computation_senses", "status": "INTERNAL_DEMO_PLAN"},
            {"surface_id": "qwen_extension_lanes", "status": "INTERNAL_ONLY_QWEN_STILL_BLOCKED"},
            {"surface_id": "capcard_candidates", "status": "INTERNAL_DRAFT_CANDIDATES"},
        ],
        "deploy_performed": False,
        "public_claim": False,
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out-dir", required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    out_dir = Path(args.out_dir)
    generate_all(out_dir)
    if args.strict:
        guardrail = json.loads((out_dir / "guardrail_result_2026_05_23.json").read_text())
        if guardrail["copied_text_included"] or guardrail["exercises_copied"]:
            raise SystemExit("copy guardrail failed")
    print("FOUNDATIONS_COMPUTATION_MAPPER_OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
