#!/usr/bin/env python3
"""Generate a local static CapCard workbench."""

from __future__ import annotations

import argparse
import html
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from tools.score_capcard_evidence import collect_cards, score_card


def page(title: str, body: str) -> str:
    return f"<!doctype html><html><head><meta charset='utf-8'><title>{html.escape(title)}</title><style>body{{font-family:system-ui,sans-serif;max-width:960px;margin:40px auto;padding:0 20px}}.pill{{border:1px solid #999;border-radius:999px;padding:2px 8px}}</style></head><body><h1>{html.escape(title)}</h1>{body}<footer><p>Internal CapCard workbench. No deploy, no upload, no public claim.</p></footer></body></html>"


def write(path: Path, text: str) -> None:
    path.write_text(text)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--drafts", required=True, type=Path)
    parser.add_argument("--out-dir", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    inventory_path = Path("product_readiness/capcard_marketplace_strengthening_source_inventory_2026_05_21.json")
    inventory = json.loads(inventory_path.read_text()) if inventory_path.exists() else {"sources": []}
    cards = collect_cards(args.drafts)
    scored = [score_card(card, inventory) for card in cards]
    strong = [row for row in scored if row["score_band"] in {"STRONG_INTERNAL_CANDIDATE", "READY_FOR_HUMAN_INTERNAL_REVIEW"}]
    blocked = [row for row in scored if row["score_band"] in {"BLOCKED", "PROMISING_BUT_NEEDS_REPAIR"}]
    write(args.out_dir / "candidate_index.json", json.dumps(scored, indent=2, sort_keys=True) + "\n")
    rows = "".join(f"<li><a href='{html.escape(row['candidate_id'])}.html'>{html.escape(row['candidate_id'])}</a> <span class='pill'>{row['score']} {html.escape(row['score_band'])}</span></li>" for row in scored)
    write(args.out_dir / "index.html", page("CapCard Workbench", f"<ul>{rows}</ul>"))
    write(args.out_dir / "strong_candidates.html", page("Strong Candidates", "<ul>" + "".join(f"<li>{html.escape(row['candidate_id'])}</li>" for row in strong) + "</ul>"))
    write(args.out_dir / "blocked_candidates.html", page("Blocked Candidates", "<ul>" + "".join(f"<li>{html.escape(row['candidate_id'])}</li>" for row in blocked) + "</ul>"))
    write(args.out_dir / "reviewer_queue.html", page("Reviewer Queue", "<p>Review strong candidates and repair blocked candidates.</p>"))
    write(args.out_dir / "risk_dashboard.html", page("Risk Dashboard", "<p>PETAL/HF uploads false. Production marketplace false. Public claims false.</p>"))
    for card, row in zip(cards, scored):
        body = f"<p>Status: {html.escape(row['score_band'])}</p><p>Score: {row['score']}</p><h2>Evidence</h2><pre>{html.escape(json.dumps(card.get('evidence_basis', []), indent=2))}</pre><h2>Blockers</h2><pre>{html.escape(json.dumps(card.get('blockers', []), indent=2))}</pre>"
        write(args.out_dir / f"{card['candidate_id']}.html", page(card.get("display_name", card["candidate_id"]), body))
    manifest = {
        "workbench_status": "PASS",
        "candidate_count": len(scored),
        "strong_candidate_count": len(strong),
        "blocked_candidate_count": len(blocked),
        "html_generated": True,
        "deploy_performed": False,
        "upload_performed": False,
        "marketplace_upload_performed": False,
        "production_marketplace_modified": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
    }
    write(args.out_dir / "workbench_manifest_2026_05_21.json", json.dumps(manifest, indent=2, sort_keys=True) + "\n")
    print("CAPCARD_WORKBENCH", len(scored), "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
