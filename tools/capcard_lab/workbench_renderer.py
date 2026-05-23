"""Render a static CapCard Lab workbench."""

from __future__ import annotations

import html
from pathlib import Path

from .reporting import read_json, write_json


def page(title: str, body: str) -> str:
    return (
        "<!doctype html><html><head><meta charset='utf-8'>"
        f"<title>{html.escape(title)}</title>"
        "<style>body{font-family:system-ui,sans-serif;max-width:1120px;margin:32px auto;padding:0 20px}"
        "table{border-collapse:collapse;width:100%}td,th{border:1px solid #ccc;padding:6px}"
        ".pill{border:1px solid #777;border-radius:999px;padding:2px 8px}</style></head><body>"
        f"<h1>{html.escape(title)}</h1>{body}<footer><p>Internal-only CapCard Lab. No deploy, upload, PETAL/API, Hugging Face, production marketplace, or public claim.</p></footer></body></html>"
    )


def render(cards_dir: Path, scores_path: Path, ranking_path: Path, out_dir: Path) -> dict:
    out_dir.mkdir(parents=True, exist_ok=True)
    scores = read_json(scores_path)
    ranking = read_json(ranking_path)
    rows = scores.get("candidates", [])
    mutation_manifest = Path("product_readiness/capcard_lab_mutation_gauntlet_2026_05_21.json")
    mutation_count = read_json(mutation_manifest).get("mutation_count", 0) if mutation_manifest.exists() else 0
    table = "<table><tr><th>Candidate</th><th>Band</th><th>Score</th></tr>" + "".join(
        f"<tr><td>{html.escape(row['candidate_id'])}</td><td>{html.escape(row['readiness_band'])}</td><td>{row['overall_trust_score_0_to_100']}</td></tr>"
        for row in rows
    ) + "</table>"
    pages = {
        "index.html": page("CapCard Lab Workbench v2", table),
        "strong.html": page("Strong Candidates", table_for(rows, "STRONG_INTERNAL")),
        "ready.html": page("Ready Candidates", table_for(rows, "READY")),
        "blocked.html": page("Blocked Candidates", table_for(rows, "BLOCKED")),
        "future.html": page("Future Candidates", table_for(rows, "FUTURE")),
        "support_only.html": page("Support Only", table_for(rows, "SUPPORT")),
        "mutations.html": page("Mutation Gauntlet", f"<p>Mutation fixtures: {mutation_count}</p>"),
        "graph.html": page("Provenance Graph", "<p>Graph JSON: product_readiness/capcard_lab_provenance_graph_2026_05_21.json</p>"),
        "reviewer_queue.html": page("Reviewer Queue", "<p>Review strong and ready cards; repair blocked cards.</p>"),
        "buyer_utility.html": page("Buyer Utility", "<p>Best wedge: internal evidence review workbench.</p>"),
        "governance_crosswalk.html": page("Governance Crosswalk", "<p>Conceptually aligned with model cards, datasheets, factsheets, and TEVV patterns; not certified compliant.</p>"),
    }
    for filename, text in pages.items():
        (out_dir / filename).write_text(text)
    write_json(out_dir / "candidate_index.json", rows)
    manifest = {
        "workbench_status": "PASS",
        "candidate_count": len(rows),
        "mutation_count": mutation_count,
        "html_generated": True,
        "deploy_performed": False,
        "upload_performed": False,
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write_json(out_dir / "workbench_manifest_2026_05_21.json", manifest)
    return manifest


def table_for(rows: list[dict], needle: str) -> str:
    selected = [row for row in rows if needle in row["readiness_band"]]
    if not selected:
        return "<p>No candidates in this bucket.</p>"
    return "<ul>" + "".join(f"<li>{html.escape(row['candidate_id'])}: {row['overall_trust_score_0_to_100']}</li>" for row in selected) + "</ul>"
