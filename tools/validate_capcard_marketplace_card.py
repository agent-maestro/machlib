#!/usr/bin/env python3
"""Validate and render a single internal CapCard marketplace draft card."""

from __future__ import annotations

import argparse
import html
import json
from pathlib import Path
from typing import Any


FALSE_FIELDS = [
    "marketplace_upload_performed",
    "production_marketplace_modified",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "public_claim",
    "certified_safety_claim",
    "production_controller_claim",
    "theorem_proof_claim",
]

REQUIRED_BOUNDARIES = [
    "not theorem",
    "not open-problem",
    "not certified safety",
    "not production controller",
    "not petal/api uploaded",
    "not hugging face uploaded",
    "not production marketplace modified",
]

FORBIDDEN_POSITIVE = [
    "theorem proved",
    "open problem solved",
    "certified safety",
    "production controller",
    "petal verified",
    "hugging face uploaded",
]


def load_json(path: Path) -> dict[str, Any]:
    data = json.loads(path.read_text())
    if not isinstance(data, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return data


def normalize(text: str) -> str:
    return " ".join(text.lower().replace("not a ", "not ").replace("not an ", "not ").split())


def negative_hit(blob: str, phrase: str) -> bool:
    idx = blob.find(phrase)
    if idx < 0:
        return False
    prefix = blob[max(0, idx - 32):idx]
    suffix = blob[idx:idx + 96]
    return "not " in prefix or "no " in prefix or "false" in suffix


def validate_card(card: dict[str, Any], guardrails: dict[str, Any], listing_text: str) -> list[str]:
    errors: list[str] = []
    expected = {
        "candidate_id": "eml_puzzle_evidence_kernel",
        "marketplace_status": "INTERNAL_DRAFT_MARKETPLACE_READY",
        "visibility": "internal",
        "tier": "OBSERVATION",
    }
    if not card.get("card_id"):
        errors.append("card_id must exist")
    for key, value in expected.items():
        if card.get(key) != value:
            errors.append(f"{key} must be {value}")
    if card.get("safe_to_display_internally") is not True:
        errors.append("safe_to_display_internally must be true")
    if card.get("safe_to_publish_publicly") is not False:
        errors.append("safe_to_publish_publicly must be false")
    for key in ["evidence_basis", "limitations"]:
        if not card.get(key):
            errors.append(f"{key} must be nonempty")
    for key in FALSE_FIELDS:
        if card.get(key) is not False:
            errors.append(f"{key} must be false")
        if guardrails.get(key) is not False:
            errors.append(f"guardrails.{key} must be false")
    boundary_blob = normalize(" ".join(
        [str(x) for x in card.get("limitations", [])]
        + [str(x) for x in card.get("not_claimed", [])]
        + [listing_text]
    ))
    for phrase in REQUIRED_BOUNDARIES:
        if phrase not in boundary_blob:
            errors.append(f"missing boundary phrase: {phrase}")
    claim_blob = normalize(json.dumps(card, sort_keys=True) + "\n" + listing_text)
    for phrase in FORBIDDEN_POSITIVE:
        if phrase in claim_blob and not negative_hit(claim_blob, phrase):
            errors.append(f"forbidden positive claim: {phrase}")
    return errors


def render_preview(card: dict[str, Any], render_dir: Path) -> None:
    render_dir.mkdir(parents=True, exist_ok=True)
    title = card["display_name"]
    evidence = card.get("evidence_basis", [])
    limitations = card.get("limitations", [])
    preview = {
        "candidate_id": card["candidate_id"],
        "title": title,
        "status": "internal draft only",
        "visibility": card["visibility"],
        "evidence_basis": evidence,
        "limitations": limitations,
        "next_review_action": "Human review may approve, request revision, or keep the card internal.",
        "not_public_marketplace": True,
        "not_petal_api_uploaded": True,
        "not_hugging_face_uploaded": True,
        "not_theorem_proof_open_problem_claim": True,
        "not_certified_safety": True,
        "not_production_controller_evidence": True,
    }
    (render_dir / "card_preview.json").write_text(json.dumps(preview, indent=2, sort_keys=True) + "\n")
    md_lines = [
        f"# {title}",
        "",
        "Status: internal draft only",
        "",
        "Not public marketplace. Not PETAL/API uploaded. Not Hugging Face uploaded.",
        "Not a theorem/proof/open-problem claim. Not certified safety. Not production controller evidence.",
        "",
        "## Evidence Basis",
        *[f"- {item}" for item in evidence],
        "",
        "## Limitations",
        *[f"- {item}" for item in limitations],
        "",
        "## Next Review Action",
        preview["next_review_action"],
        "",
    ]
    (render_dir / "card_preview.md").write_text("\n".join(md_lines))
    evidence_html = "".join(f"<li>{html.escape(str(item))}</li>" for item in evidence)
    limitations_html = "".join(f"<li>{html.escape(str(item))}</li>" for item in limitations)
    page = f"""<!doctype html>
<html lang="en">
<head>
  <meta charset="utf-8">
  <meta name="viewport" content="width=device-width, initial-scale=1">
  <title>{html.escape(title)} - Internal Draft Preview</title>
  <style>
    body {{ font-family: system-ui, sans-serif; margin: 0; background: #f6f7f9; color: #18212f; }}
    main {{ max-width: 880px; margin: 0 auto; padding: 40px 20px; }}
    .card {{ background: white; border: 1px solid #d7dde7; border-radius: 8px; padding: 28px; }}
    .status {{ display: inline-block; border: 1px solid #8492a6; border-radius: 999px; padding: 4px 10px; font-size: 13px; }}
    h1 {{ margin: 12px 0 6px; }}
    section {{ margin-top: 24px; }}
    footer {{ margin-top: 28px; border-top: 1px solid #d7dde7; padding-top: 18px; font-weight: 600; }}
  </style>
</head>
<body>
  <main>
    <article class="card">
      <span class="status">Internal draft only</span>
      <h1>{html.escape(title)}</h1>
      <p>Observation-tier CapCard marketplace preview for internal review.</p>
      <section><h2>Evidence Basis</h2><ul>{evidence_html}</ul></section>
      <section><h2>Limitations / Not Claimed</h2><ul>{limitations_html}</ul></section>
      <section><h2>Next Review Action</h2><p>{html.escape(preview["next_review_action"])}</p></section>
      <footer>
        Not public marketplace. Not PETAL/API uploaded. Not Hugging Face uploaded.
        Not a theorem/proof/open-problem claim. Not certified safety. Not production controller evidence.
      </footer>
    </article>
  </main>
</body>
</html>
"""
    (render_dir / "index.html").write_text(page)


def build_result(card: dict[str, Any], preview_generated: bool) -> dict[str, Any]:
    return {
        "candidate_id": card["candidate_id"],
        "card_status": card["marketplace_status"],
        "works_as_internal_draft_card": True,
        "works_as_production_marketplace_card": False,
        "preview_generated": preview_generated,
        "safe_to_display_internally": True,
        "safe_to_publish_publicly": False,
        "production_marketplace_modified": False,
        "marketplace_upload_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "public_claim": False,
        "certified_safety_claim": False,
        "production_controller_claim": False,
        "theorem_proof_claim": False,
        "next_safe_task": "M084B_QWEN_PUZZLE_CURRICULUM_REPAIR_FOR_SECOND_CARD",
    }


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--card", required=True, type=Path)
    parser.add_argument("--guardrails", required=True, type=Path)
    parser.add_argument("--listing", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--render-dir", required=True, type=Path)
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    card = load_json(args.card)
    guardrails = load_json(args.guardrails)
    listing_text = args.listing.read_text()
    errors = validate_card(card, guardrails, listing_text)
    if errors:
        print("CAPCARD_MARKETPLACE_CARD", card.get("candidate_id", "<unknown>"), "FAIL")
        for error in errors:
            print("ERROR", error)
        return 1
    render_preview(card, args.render_dir)
    args.out.write_text(json.dumps(build_result(card, True), indent=2, sort_keys=True) + "\n")
    print("CAPCARD_MARKETPLACE_CARD", card["candidate_id"], card["marketplace_status"], "PASS")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
