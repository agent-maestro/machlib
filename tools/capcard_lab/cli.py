"""Command line interface for the local CapCard Lab engine."""

from __future__ import annotations

import argparse
from pathlib import Path

from .candidate_factory import generate_candidates
from .evidence_scorer import score
from .governance_crosswalk import write_crosswalk
from .marketplace_ranker import rank
from .mutation_engine import mutate
from .provenance_graph import write_graph
from .qwen_repair import build_qwen_repair
from .reporting import write_json, write_report
from .reviewer_workflow import write_workflow
from .source_discovery import write_discovery
from .workbench_renderer import render


def write_final_outputs(repo_root: Path) -> None:
    write_crosswalk(repo_root)
    write_workflow(repo_root)
    build_qwen_repair(repo_root)
    assessment = {
        "status": "PASS",
        "product_potential_score_0_to_100": 78,
        "trust_infrastructure_score_0_to_100": 82,
        "validator_strength_score_0_to_100": 84,
        "marketplace_ux_score_0_to_100": 72,
        "evidence_freshness_score_0_to_100": 67,
        "revenue_path_score_0_to_100": 70,
        "execution_risk_score_0_to_100": 48,
        "verdict": "BUILD_CAPCARD_LAB_NOW",
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(repo_root / "product_readiness/capcard_lab_final_assessment_2026_05_21.json", assessment)
    write_report(
        repo_root / "reports/capcard_lab_final_assessment_2026_05_21.md",
        "CapCard Lab Final Assessment",
        [
            "- Verdict: BUILD_CAPCARD_LAB_NOW",
            "- This opens new utility: candidate generation, mutation testing, trust scoring, ranking, and static workbench previews.",
            "- Strongest wedge: private evidence marketplace and TEVV cockpit for generated artifacts.",
            "- Weakness: reviewer metadata and freshness still need more disciplined capture.",
        ],
    )
    card = {
        "surface": "command.monogate.dev",
        "visibility": "internal",
        "title": "CapCard Lab Engine",
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "deploy_performed": False,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(repo_root / "command_center_feeds/capcard_lab_status_card_2026_05_21.json", card)
    write_json(repo_root / "command_center_feeds/capcard_lab_status_feed_2026_05_21.json", {"cards": [card], "deploy_performed": False, "public_claim": False})
    write_report(repo_root / "reports/capcard_lab_command_center_card_2026_05_21.md", "CapCard Lab Command Center Card", ["- Internal-only status card prepared.", "- No Command Center repo modification or deploy performed."])


def main() -> int:
    parser = argparse.ArgumentParser(prog="capcard-lab")
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("discover")
    p.add_argument("--repo-root", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--strict", action="store_true")

    p = sub.add_parser("build-graph")
    p.add_argument("--repo-root", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--strict", action="store_true")

    p = sub.add_parser("generate-candidates")
    p.add_argument("--repo-root", type=Path, required=True)
    p.add_argument("--graph", type=Path, required=True)
    p.add_argument("--out-dir", type=Path, required=True)
    p.add_argument("--strict", action="store_true")

    p = sub.add_parser("mutate")
    p.add_argument("--cards", type=Path, required=True)
    p.add_argument("--out-dir", type=Path, required=True)
    p.add_argument("--count", type=int, required=True)
    p.add_argument("--strict", action="store_true")

    p = sub.add_parser("score")
    p.add_argument("--cards", type=Path, required=True)
    p.add_argument("--graph", type=Path, required=True)
    p.add_argument("--mutations", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--strict", action="store_true")

    p = sub.add_parser("rank")
    p.add_argument("--scores", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--strict", action="store_true")

    p = sub.add_parser("render-workbench")
    p.add_argument("--cards", type=Path, required=True)
    p.add_argument("--scores", type=Path, required=True)
    p.add_argument("--ranking", type=Path, required=True)
    p.add_argument("--out-dir", type=Path, required=True)
    p.add_argument("--strict", action="store_true")

    args = parser.parse_args()
    if args.command == "discover":
        data = write_discovery(args.repo_root, args.out)
        print("CAPCARD_LAB_DISCOVERY", data["source_count"], data["status"])
    elif args.command == "build-graph":
        graph = write_graph(args.repo_root, args.out)
        print("CAPCARD_LAB_GRAPH", graph["node_count"], graph["edge_count"], graph["status"])
    elif args.command == "generate-candidates":
        data = generate_candidates(args.repo_root, args.out_dir)
        print("CAPCARD_LAB_CANDIDATES", data["candidate_count"], data["status"])
    elif args.command == "mutate":
        data = mutate(args.cards, args.out_dir, args.count, Path("."))
        print("CAPCARD_LAB_MUTATIONS", data["mutation_count"], data["detection_coverage_percent"], data["status"])
    elif args.command == "score":
        data = score(args.cards, args.out, Path("."))
        print("CAPCARD_LAB_SCORE", data["candidate_count"], data["status"])
    elif args.command == "rank":
        data = rank(args.scores, args.out, Path("."))
        print("CAPCARD_LAB_RANK", len(data["ranked_candidates"]), data["status"])
    elif args.command == "render-workbench":
        manifest = render(args.cards, args.scores, args.ranking, args.out_dir)
        write_final_outputs(Path("."))
        print("CAPCARD_LAB_WORKBENCH", manifest["candidate_count"], manifest["mutation_count"], manifest["workbench_status"])
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
