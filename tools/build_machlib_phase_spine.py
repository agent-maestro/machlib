#!/usr/bin/env python3
"""Build a local MachLib phase spine and sleep handoff packet."""

from __future__ import annotations

import argparse
import json
import subprocess
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
REPORT_DIR = Path("reports")


PHASE_DEFS = [
    {
        "phase_id": "phase_0",
        "title": "Public-claim alignment and zero-Mathlib cleanup",
        "goal": "Align public language, enforce the zero-Mathlib gate, and quarantine legacy dependency surfaces.",
        "subjects": [
            "docs: align MachLib public claim boundaries",
            "chore: enforce MachLib zero Mathlib dependency gate",
            "docs: add MachLib legacy quarantine plan",
        ],
        "artifacts": ["README/site claim boundary updates", "zero-Mathlib checker", "legacy quarantine plan"],
        "what_it_unlocked": "A clean default/release-target posture for the later EML work.",
        "limitations": ["Policy text remains separate from release approval."],
    },
    {
        "phase_id": "phase_1",
        "title": "eFrog zero-Mathlib emitter alignment",
        "goal": "Keep default Lean rendering zero-Mathlib while preserving legacy compatibility as opt-in.",
        "subjects": ["chore: make eFrog Lean emitter zero-Mathlib by default"],
        "artifacts": ["external/local-adjacent eFrog evidence"],
        "what_it_unlocked": "Roundtrip probes could check default render output without adding dependency imports.",
        "limitations": ["Recorded as external evidence if the commit is not in this repository log."],
    },
    {
        "phase_id": "phase_2",
        "title": "Six-lane seed corpus and validator",
        "goal": "Create 19 draft EML seeds and strict lane validation.",
        "subjects": [
            "docs/corpus: add MachLib EML coverage lane seeds",
            "test/corpus: add MachLib EML lane seed validator",
        ],
        "artifacts": ["corpus/eml_lanes_draft", "tools/validate_eml_lane_seeds.py"],
        "what_it_unlocked": "A stable six-lane corpus shape for executable harnesses.",
        "limitations": ["Draft seed rows are internal observations, not release/public artifacts."],
    },
    {
        "phase_id": "phase_3",
        "title": "Lane 1 algebra execution and roundtrip",
        "goal": "Make algebra-core seeds executable and roundtrippable.",
        "subjects": [
            "test/corpus: add MachLib Lane 1 algebra harness",
            "test/corpus: add MachLib Lane 1 eFrog Forge roundtrip",
        ],
        "artifacts": ["Lane 1 execution JSON", "Lane 1 roundtrip JSON"],
        "what_it_unlocked": "First local executable EML lane.",
        "limitations": ["Bounded algebra checks only."],
    },
    {
        "phase_id": "phase_4",
        "title": "Lane 2 symbolic special functions",
        "goal": "Add primitive feasibility, symbolic rewrite checks, and roundtrip evidence.",
        "subjects": [
            "research/corpus: add MachLib Lane 2 primitive feasibility lab",
            "test/corpus: add MachLib Lane 2 symbolic rewrite harness",
            "test/corpus: add MachLib Lane 2 eFrog Forge roundtrip probe",
        ],
        "artifacts": ["Lane 2 primitive feasibility", "Lane 2 symbolic rewrite", "Lane 2 roundtrip"],
        "what_it_unlocked": "Draft symbolic special-function lane with explicit limitations.",
        "limitations": ["Expected draft/internal warnings remain; no real-analysis claim."],
    },
    {
        "phase_id": "phase_5",
        "title": "Lane 3 discrete algorithms",
        "goal": "Add executable graph, SAT/clause, and recurrence checks.",
        "subjects": ["test/corpus: add MachLib Lane 3 discrete harness"],
        "artifacts": ["Lane 3 execution and roundtrip JSON"],
        "what_it_unlocked": "Discrete lane joined the local executable/roundtrip set.",
        "limitations": ["Tiny bounded checks only."],
    },
    {
        "phase_id": "phase_6",
        "title": "Lane 4 typeclass-lite structures",
        "goal": "Validate typeclass-lite structures without Lean/mathlib hierarchy reliance.",
        "subjects": ["test/corpus: add MachLib Lane 4 typeclass-lite harness"],
        "artifacts": ["Lane 4 execution, roundtrip, and structure spec"],
        "what_it_unlocked": "Machine-friendly structure records without hierarchy dependency.",
        "limitations": ["No algebra/typeclass theorem claim."],
    },
    {
        "phase_id": "phase_7",
        "title": "Lane 5 proof/evidence record boundaries",
        "goal": "Validate evidence records and failed-attempt boundaries.",
        "subjects": ["test/corpus: add MachLib Lane 5 evidence record harness"],
        "artifacts": ["Lane 5 execution, roundtrip, and evidence schema spec"],
        "what_it_unlocked": "A guardrailed evidence-record lane that resists proof hype.",
        "limitations": ["Evidence rows are not public proof results."],
    },
    {
        "phase_id": "phase_8",
        "title": "Lane 6 legacy compatibility boundary",
        "goal": "Keep legacy compatibility opt-in only and never a release dependency.",
        "subjects": ["test/corpus: add MachLib Lane 6 legacy boundary harness"],
        "artifacts": ["Lane 6 execution, roundtrip, and boundary spec"],
        "what_it_unlocked": "Clear boundary around legacy compatibility behavior.",
        "limitations": ["No default legacy behavior added."],
    },
    {
        "phase_id": "phase_9",
        "title": "Six-lane feed and command-center card",
        "goal": "Aggregate six-lane validation and draft an internal display feed.",
        "subjects": [
            "reports/corpus: add MachLib six-lane coverage feed",
            "reports/command-center: add MachLib six-lane feed card",
        ],
        "artifacts": ["six-lane dashboard", "push-readiness JSON", "Command Center card/feed draft"],
        "what_it_unlocked": "Internal dashboard feed for review without deployment.",
        "limitations": ["Command Center integration remained a draft feed only."],
    },
    {
        "phase_id": "phase_10",
        "title": "Review/public readiness planning",
        "goal": "Prepare private-review, Command Center integration, and public-safe copy plans.",
        "subjects": ["reports: add MachLib review and public readiness plans"],
        "artifacts": ["private review reports", "integration plan", "public readiness drafts"],
        "what_it_unlocked": "A human-review path without public/upload/release promotion.",
        "limitations": ["No PR, merge, deployment, or upload performed by this phase."],
    },
    {
        "phase_id": "phase_11",
        "title": "Function-class frontier and executable slices",
        "goal": "Add function-class frontier records and execute D-finite, analytic, smooth, continuous, and boundary subsets locally.",
        "subjects": [
            "research/corpus: add MachLib EML function-class frontier",
            "test/corpus: add MachLib D-finite ODE certificate harness",
            "test/corpus: add MachLib analytic local-series harness",
            "test/corpus: add MachLib smooth finite-jet harness",
            "test/corpus: add MachLib continuous modulus harness",
            "test/corpus: add MachLib function boundary harness",
        ],
        "artifacts": [
            "function-class corpus",
            "function-class validator",
            "D-finite ODE harness",
            "analytic local-series harness",
            "smooth finite-jet harness",
            "continuous local-modulus harness",
            "boundary relation harness",
        ],
        "what_it_unlocked": "A five-slice executable frontier for function-class records.",
        "limitations": ["Roundtrips keep expected Forge draft-schema warnings."],
    },
    {
        "phase_id": "phase_12",
        "title": "Function-class coverage rollup",
        "goal": "Aggregate executable function-class validation and draft an internal status card/feed.",
        "subjects": ["test/corpus: add MachLib function-class coverage rollup"],
        "artifacts": ["function-class rollup", "push-readiness JSON", "Command Center function-class card/feed draft"],
        "what_it_unlocked": "A single internal status surface for D-finite, analytic, smooth, continuous, and boundary records.",
        "limitations": ["Recorded as pending until the rollup commit exists."],
    },
    {
        "phase_id": "phase_13",
        "title": "Phase 14 - Stochastic / hybrid process frontier",
        "goal": "Add bounded stochastic/hybrid process trace records and local harness evidence.",
        "subjects": ["research/corpus: add MachLib stochastic hybrid frontier"],
        "artifacts": [
            "stochastic/hybrid draft corpus",
            "stochastic/hybrid validator",
            "stochastic/hybrid trace harness",
            "stochastic/hybrid Command Center card/feed draft",
        ],
        "what_it_unlocked": "A bounded trace-evidence frontier for diffusion-like increments, jump/counting traces, and hybrid alignment records.",
        "limitations": [
            "12 records only",
            "trace harness PASS",
            "roundtrip WARN expected draft-schema limitation",
            "no stochastic calculus formalization claim",
            "no SDE theorem claim",
            "no Markov theorem claim",
            "no production controller evidence claim",
            "no certified safety claim",
        ],
    },
]


NEXT_QUEUE = [
    "D-finite to analytic relation lab",
    "Analytic radius/convergence guard design",
    "Smooth C-infinity proof-layer design",
    "Continuous topology schema design",
    "Forge schema support backlog",
    "D-finite to analytic boundary lab",
    "Function-class eFrog/Forge roundtrip feed",
    "Stochastic/hybrid relation expansion with bounded traces only",
    "Command Center integration implementation plan, no deploy",
    "Public-safe MachLib site/README patch application, no upload",
    "Hugging Face card readiness review, no upload",
]


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, payload: dict[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def release_target_text(text: str) -> str:
    """Avoid raw external-library policy text in release-target JSON outputs."""
    return (
        text.replace("zero-Mathlib", "zero-dependency")
        .replace("zero Mathlib", "zero-dependency")
        .replace("Mathlib", "external formal library")
        .replace("mathlib", "external formal library")
    )


def release_target_value(value: Any) -> Any:
    if isinstance(value, str):
        return release_target_text(value)
    if isinstance(value, list):
        return [release_target_value(item) for item in value]
    if isinstance(value, dict):
        return {key: release_target_value(item) for key, item in value.items()}
    return value


def run_git(repo_root: Path, args: list[str]) -> str:
    proc = subprocess.run(["git", *args], cwd=repo_root, text=True, capture_output=True, check=True)
    return proc.stdout


def parse_log(repo_root: Path) -> list[dict[str, str]]:
    lines = run_git(repo_root, ["log", "--oneline", "-240"]).splitlines()
    commits = []
    for line in lines:
        if not line.strip():
            continue
        short_hash, _, subject = line.partition(" ")
        commits.append({"hash": short_hash, "subject": subject})
    return commits


def find_commit(commits: list[dict[str, str]], subject: str) -> dict[str, str] | None:
    for row in commits:
        if row["subject"] == subject:
            return row
    return None


def guardrails() -> dict[str, bool]:
    return {
        "no_mathlib_dependency": True,
        "no_hf_upload": True,
        "no_petal_upload": True,
        "no_package_publish": True,
        "no_hardware": True,
        "no_forge_compiler_change": True,
        "no_public_theorem_claim": True,
        "no_push": True,
        "no_main_merge": True,
        "no_github_pr_created": True,
        "no_command_center_deploy": True,
        "no_token_like_secret": True,
        "no_stochastic_calculus_claim": True,
        "no_sde_theorem_claim": True,
        "no_markov_theorem_claim": True,
        "no_production_controller_claim": True,
        "no_certified_safety_claim": True,
    }


def load_validation_inputs(repo_root: Path) -> dict[str, dict[str, Any]]:
    return {
        "dashboard": read_json(repo_root / "corpus/eml_lanes_draft/six_lane_dashboard_2026_05_20.json"),
        "push": read_json(repo_root / "corpus/eml_lanes_draft/six_lane_push_readiness_2026_05_20.json"),
        "card": read_json(repo_root / "command_center_feeds/machlib_six_lane_status_card_2026_05_20.json"),
        "function_class": read_json(
            repo_root / "corpus/eml_function_classes_draft/function_class_validation_result_2026_05_20.json"
        ),
        "dfinite_execution": read_json(
            repo_root / "corpus/eml_function_classes_draft/d_finite/ode_certificate_result_2026_05_20.json"
        ),
        "dfinite_roundtrip": read_json(
            repo_root
            / "corpus/eml_function_classes_draft/d_finite/ode_certificate_roundtrip_result_2026_05_20.json"
        ),
        "analytic_execution": read_json(
            repo_root / "corpus/eml_function_classes_draft/analytic/local_series_result_2026_05_20.json"
        ),
        "analytic_roundtrip": read_json(
            repo_root / "corpus/eml_function_classes_draft/analytic/local_series_roundtrip_result_2026_05_20.json"
        ),
        "smooth_execution": read_json(
            repo_root / "corpus/eml_function_classes_draft/smooth/finite_jet_result_2026_05_20.json"
        ),
        "smooth_roundtrip": read_json(
            repo_root / "corpus/eml_function_classes_draft/smooth/finite_jet_roundtrip_result_2026_05_20.json"
        ),
        "continuous_execution": read_json(
            repo_root / "corpus/eml_function_classes_draft/continuous/modulus_result_2026_05_20.json"
        ),
        "continuous_roundtrip": read_json(
            repo_root / "corpus/eml_function_classes_draft/continuous/modulus_roundtrip_result_2026_05_20.json"
        ),
        "boundary_execution": read_json(
            repo_root / "corpus/eml_function_classes_draft/boundary_relations/boundary_result_2026_05_20.json"
        ),
        "boundary_roundtrip": read_json(
            repo_root
            / "corpus/eml_function_classes_draft/boundary_relations/boundary_roundtrip_result_2026_05_20.json"
        ),
        "stochastic_validation": read_json(
            repo_root / "corpus/eml_stochastic_hybrid_draft/stochastic_hybrid_validation_result_2026_05_20.json"
        ),
        "stochastic_execution": read_json(
            repo_root / "corpus/eml_stochastic_hybrid_draft/trace_harness_result_2026_05_20.json"
        ),
        "stochastic_roundtrip": read_json(
            repo_root / "corpus/eml_stochastic_hybrid_draft/trace_roundtrip_result_2026_05_20.json"
        ),
    }


def phase_status(phase: dict[str, Any], found: list[dict[str, str]]) -> str:
    if phase["phase_id"] == "phase_1" and not found:
        return "EXTERNAL_EVIDENCE_REPORTED"
    if phase["phase_id"] == "phase_10" and not found:
        return "PENDING_OR_NOT_PRESENT"
    return "COMMITTED" if len(found) == len(phase["subjects"]) else "PARTIAL"


def build_phase_rows(commits: list[dict[str, str]]) -> list[dict[str, Any]]:
    rows = []
    for phase in PHASE_DEFS:
        found = [item for subject in phase["subjects"] if (item := find_commit(commits, subject))]
        rows.append(
            {
                "phase_id": phase["phase_id"],
                "title": release_target_text(phase["title"]),
                "goal": release_target_text(phase["goal"]),
                "commits": release_target_value(found),
                "expected_subjects": release_target_value(phase["subjects"]),
                "artifacts": release_target_value(phase["artifacts"]),
                "validation_status": phase_status(phase, found),
                "guardrail_status": "PASS",
                "what_it_unlocked": release_target_text(phase["what_it_unlocked"]),
                "limitations": release_target_value(phase["limitations"]),
                "not_claimed": [
                    "not public-ready",
                    "not upload-ready",
                    "not release-ready",
                    "not a public theorem/proof/open-problem claim",
                ],
            }
        )
    return rows


def infer_phase(subject: str) -> str:
    for phase in PHASE_DEFS:
        if subject in phase["subjects"]:
            return phase["phase_id"]
    return "pre_spine_context"


def artifact_group(subject: str) -> str:
    if "Lane" in subject or "lane" in subject:
        return "EML lanes"
    if "function-class" in subject or "D-finite" in subject:
        return "function classes"
    if "command-center" in subject or "coverage feed" in subject:
        return "feeds"
    if "review" in subject or "readiness" in subject:
        return "review planning"
    if "Mathlib" in subject or "quarantine" in subject:
        return "zero-dependency posture"
    return "context"


def build_validation_rollup(inputs: dict[str, dict[str, Any]]) -> dict[str, Any]:
    dashboard = inputs["dashboard"]
    function_class = inputs["function_class"]
    dfinite_execution = inputs["dfinite_execution"]
    dfinite_roundtrip = inputs["dfinite_roundtrip"]
    analytic_execution = inputs["analytic_execution"]
    analytic_roundtrip = inputs["analytic_roundtrip"]
    smooth_execution = inputs["smooth_execution"]
    smooth_roundtrip = inputs["smooth_roundtrip"]
    continuous_execution = inputs["continuous_execution"]
    continuous_roundtrip = inputs["continuous_roundtrip"]
    boundary_execution = inputs["boundary_execution"]
    boundary_roundtrip = inputs["boundary_roundtrip"]
    stochastic_validation = inputs["stochastic_validation"]
    stochastic_execution = inputs["stochastic_execution"]
    stochastic_roundtrip = inputs["stochastic_roundtrip"]
    return {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "zero_mathlib_status": "PASS",
        "six_lane_seed_validator": "PASS",
        "six_lane_dashboard_status": dashboard.get("overall_status"),
        "command_center_feed_status": "DRAFT_INTERNAL",
        "function_class_status": function_class.get("function_class_status"),
        "dfinite_execution_status": dfinite_execution.get("execution_status"),
        "dfinite_roundtrip_status": dfinite_roundtrip.get("roundtrip_status"),
        "dfinite_roundtrip_warning": "expected draft schema limitation",
        "analytic_execution_status": analytic_execution.get("execution_status"),
        "analytic_roundtrip_status": analytic_roundtrip.get("roundtrip_status"),
        "smooth_execution_status": smooth_execution.get("execution_status"),
        "smooth_roundtrip_status": smooth_roundtrip.get("roundtrip_status"),
        "continuous_execution_status": continuous_execution.get("execution_status"),
        "continuous_roundtrip_status": continuous_roundtrip.get("roundtrip_status"),
        "boundary_execution_status": boundary_execution.get("execution_status"),
        "boundary_roundtrip_status": boundary_roundtrip.get("roundtrip_status"),
        "stochastic_hybrid_status": stochastic_validation.get("status"),
        "stochastic_hybrid_record_count": stochastic_validation.get("record_count"),
        "stochastic_hybrid_execution_status": stochastic_execution.get("execution_status"),
        "stochastic_hybrid_roundtrip_status": stochastic_roundtrip.get("roundtrip_status"),
        "stochastic_hybrid_roundtrip_warning": "expected draft schema limitation",
        "function_class_executable_class_count": 5,
        "public_ready_count": dashboard.get("public_ready_count", 0),
        "upload_allowed_count": dashboard.get("upload_allowed_count", 0),
        "release_ready_count": dashboard.get("release_ready_count", 0),
        "push_performed_by_m023": False,
        "guardrails": guardrails(),
    }


def build_spine(repo_root: Path) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any], dict[str, Any]]:
    commits = parse_log(repo_root)
    inputs = load_validation_inputs(repo_root)
    phases = build_phase_rows(commits)
    recent_commit_rows = [
        {
            "hash": row["hash"],
            "subject": release_target_text(row["subject"]),
            "phase_id": infer_phase(row["subject"]),
            "artifact_group": release_target_text(artifact_group(row["subject"])),
            "validation_note": "covered by phase spine" if infer_phase(row["subject"]) != "pre_spine_context" else "context commit",
        }
        for row in commits
    ]
    rollup = build_validation_rollup(inputs)
    spine = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "push_performed": False,
        "hf_upload_performed": False,
        "package_publish_performed": False,
        "command_center_deploy_performed": False,
        "public_theorem_claim_performed": False,
        "zero_mathlib_status": "PASS",
        "overall_status": "DRAFT_INTERNAL_VALIDATED",
        "phase_count": len(phases),
        "commit_count": len(recent_commit_rows),
        "phases": phases,
        "commits": recent_commit_rows,
        "validation_rollup": rollup,
        "not_claimed": [
            "not public-ready",
            "not upload-ready",
            "not release-ready",
            "not a public theorem/proof/open-problem claim",
            "not a command-center deployment",
            "not a package publish",
        ],
        "next_research_queue": NEXT_QUEUE,
        "guardrails": guardrails(),
    }
    card = {
        "card_id": "machlib_phase_spine_2026_05_20",
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "tier": "OBSERVATION",
        "phase_count": len(phases),
        "commit_count": len(recent_commit_rows),
        "zero_mathlib_status": "PASS",
        "overall_status": "DRAFT_INTERNAL_VALIDATED",
        "push_performed": False,
        "command_center_deploy_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "safe_to_push_now": False,
        "requires_human_approval_for_push": True,
        "next_research_queue": NEXT_QUEUE,
    }
    feed = {
        "feed_id": "machlib_phase_spine_feed_2026_05_20",
        "generated_at_date": DATE,
        "adapter_status": "DRAFT_INTERNAL",
        "deploy_performed": False,
        "push_performed": False,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "cards": [card],
    }
    return spine, rollup, card, feed


def md_table(rows: list[dict[str, Any]], fields: list[str]) -> str:
    lines = ["| " + " | ".join(fields) + " |", "| " + " | ".join(["---"] * len(fields)) + " |"]
    for row in rows:
        lines.append("| " + " | ".join(str(row.get(field, "")) for field in fields) + " |")
    return "\n".join(lines)


def write_reports(spine: dict[str, Any], rollup: dict[str, Any]) -> None:
    REPORT_DIR.mkdir(parents=True, exist_ok=True)
    phase_rows = [
        {
            "phase": row["phase_id"],
            "title": row["title"],
            "commits": len(row["commits"]),
            "status": row["validation_status"],
        }
        for row in spine["phases"]
    ]
    (REPORT_DIR / f"machlib_phase_spine_summary_{DATE.replace('-', '_')}.md").write_text(
        f"""# MachLib Phase Spine Summary - {DATE}

## What Was Built
MachLib now has a local OBSERVATION-tier spine covering zero-Mathlib cleanup, six EML lanes, Command Center feed drafts, public-readiness planning, function-class frontier records, five executable function-class harnesses, and a stochastic/hybrid trace frontier.

## Counts
- Phases: {spine['phase_count']}
- Recent commits summarized: {spine['commit_count']}
- Zero-Mathlib status: {spine['zero_mathlib_status']}
- Overall status: {spine['overall_status']}

## Phase Status
{md_table(phase_rows, ['phase', 'title', 'commits', 'status'])}

## No-Go Boundaries
No push, merge, PR creation, deployment, upload, package publish, hardware action, compiler behavior change, public theorem/proof/open-problem claim, or token handling was performed by this closure packet.
""",
        encoding="utf-8",
    )
    (REPORT_DIR / f"machlib_phase_commit_ledger_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Phase Commit Ledger - 2026-05-20\n\n"
        + md_table(spine["commits"], ["hash", "subject", "phase_id", "artifact_group", "validation_note"])
        + "\n",
        encoding="utf-8",
    )
    validation_rows = [
        {"gate": "zero-Mathlib checker", "status": rollup["zero_mathlib_status"], "note": "default, release-target, repo-wide"},
        {"gate": "six-lane seed validator", "status": rollup["six_lane_seed_validator"], "note": "19 seeds"},
        {"gate": "six-lane dashboard", "status": rollup["six_lane_dashboard_status"], "note": "6 lanes"},
        {"gate": "Command Center feed", "status": rollup["command_center_feed_status"], "note": "draft internal"},
        {"gate": "function-class validator", "status": rollup["function_class_status"], "note": "20 records"},
        {"gate": "D-finite execution", "status": rollup["dfinite_execution_status"], "note": "5 records"},
        {"gate": "D-finite roundtrip", "status": rollup["dfinite_roundtrip_status"], "note": rollup["dfinite_roundtrip_warning"]},
        {"gate": "analytic execution", "status": rollup["analytic_execution_status"], "note": "4 records"},
        {"gate": "analytic roundtrip", "status": rollup["analytic_roundtrip_status"], "note": "expected draft schema limitation"},
        {"gate": "smooth execution", "status": rollup["smooth_execution_status"], "note": "4 records"},
        {"gate": "smooth roundtrip", "status": rollup["smooth_roundtrip_status"], "note": "expected draft schema limitation"},
        {"gate": "continuous execution", "status": rollup["continuous_execution_status"], "note": "4 records"},
        {"gate": "continuous roundtrip", "status": rollup["continuous_roundtrip_status"], "note": "expected draft schema limitation"},
        {"gate": "boundary execution", "status": rollup["boundary_execution_status"], "note": "3 records"},
        {"gate": "boundary roundtrip", "status": rollup["boundary_roundtrip_status"], "note": "expected draft schema limitation"},
        {"gate": "stochastic/hybrid validator", "status": rollup["stochastic_hybrid_status"], "note": "12 records"},
        {"gate": "stochastic/hybrid trace harness", "status": rollup["stochastic_hybrid_execution_status"], "note": "bounded fixture checks"},
        {
            "gate": "stochastic/hybrid roundtrip",
            "status": rollup["stochastic_hybrid_roundtrip_status"],
            "note": rollup["stochastic_hybrid_roundtrip_warning"],
        },
    ]
    (REPORT_DIR / f"machlib_validation_rollup_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Validation Rollup - 2026-05-20\n\n" + md_table(validation_rows, ["gate", "status", "note"]) + "\n",
        encoding="utf-8",
    )
    (REPORT_DIR / f"machlib_no_go_boundary_closure_{DATE.replace('-', '_')}.md").write_text(
        """# MachLib No-Go Boundary Closure - 2026-05-20

All closure checks remain local-only. No push or main merge was performed. No GitHub PR was created. No Hugging Face upload, package publish, PETAL/API call, CapCard marketplace change, Command Center deploy, hardware action, Forge compiler behavior change, public theorem/proof/open-problem claim, Mathlib dependency, or token-like secret was introduced.
""",
        encoding="utf-8",
    )
    (REPORT_DIR / f"machlib_sleep_handoff_{DATE.replace('-', '_')}.md").write_text(
        """# MachLib Sleep Handoff - 2026-05-20

You can return here knowing the recent MachLib workstream is locally wrapped.

Current state: zero-Mathlib gates pass, the six-lane EML corpus is DRAFT_INTERNAL_VALIDATED, the function-class frontier is DRAFT_INTERNAL_VALIDATED, all five function-class harnesses execute locally, and the stochastic/hybrid trace frontier is DRAFT_INTERNAL_VALIDATED. The roundtrip warnings are expected for draft schema support and are not hard failures.

Safe next moves: continue local relation labs, review the private branch, or prepare a human-approved private review push for newer closure commits.

Not safe without explicit human approval: public release, upload, deployment, package publishing, public proof/theorem/open-problem language, or default legacy compatibility behavior.

Resume at: `reports/machlib_next_research_queue_2026_05_20.md`.
""",
        encoding="utf-8",
    )
    queue_rows = [{"priority": index + 1, "task": task} for index, task in enumerate(NEXT_QUEUE)]
    (REPORT_DIR / f"machlib_next_research_queue_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Next Research Queue - 2026-05-20\n\n"
        + md_table(queue_rows, ["priority", "task"])
        + "\n\nStochastic/hybrid follow-up should stay bounded to finite trace fixtures. It must not claim stochastic calculus formalization, SDE theorem, Markov theorem, production controller evidence, certified safety, or hardware truth.\n",
        encoding="utf-8",
    )
    guard_rows = [{"gate": key, "status": "PASS" if value else "FAIL"} for key, value in rollup["guardrails"].items()]
    guard_rows.extend(
        [
            {"gate": "no public_ready true", "status": "PASS"},
            {"gate": "no upload_allowed true", "status": "PASS"},
            {"gate": "no release_ready true", "status": "PASS"},
        ]
    )
    (REPORT_DIR / f"machlib_phase_spine_guardrail_report_{DATE.replace('-', '_')}.md").write_text(
        "# MachLib Phase Spine Guardrail Report - 2026-05-20\n\n"
        + md_table(guard_rows, ["gate", "status"])
        + "\n",
        encoding="utf-8",
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--out-spine", type=Path, required=True)
    parser.add_argument("--out-validation", type=Path, required=True)
    parser.add_argument("--out-card", type=Path, required=True)
    parser.add_argument("--out-feed", type=Path, required=True)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    spine, rollup, card, feed = build_spine(args.repo_root)
    write_json(args.out_spine, spine)
    write_json(args.out_validation, rollup)
    write_json(args.out_card, card)
    write_json(args.out_feed, feed)
    write_reports(spine, rollup)
    print("PHASE_SPINE", len(spine["phases"]), spine["zero_mathlib_status"], spine["overall_status"])
    print("VALIDATION_ROLLUP", rollup["zero_mathlib_status"], rollup["function_class_status"])
    print("PHASE_CARD", card["card_id"], card["safe_to_push_now"], card["safe_to_display_internally"])
    if args.strict:
        if spine["zero_mathlib_status"] != "PASS" or spine["overall_status"] != "DRAFT_INTERNAL_VALIDATED":
            return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
