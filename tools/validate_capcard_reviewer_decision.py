#!/usr/bin/env python3
"""Validate local CapCard reviewer decisions."""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ALLOWED = {"approve_internal_display", "request_revision", "keep_blocked", "retire_candidate"}
FORBIDDEN = {"approve_public_marketplace", "approve_petal_upload", "approve_hf_upload", "approve_certified_safety", "approve_production_controller"}
FALSE_FIELDS = ["marketplace_upload_performed", "production_marketplace_modified", "petal_api_upload_performed", "huggingface_upload_performed", "public_claim", "certified_safety_claim", "production_controller_claim", "theorem_proof_claim"]


def validate_decision(row: dict) -> list[str]:
    errors = []
    for key in ["candidate_id", "reviewer_id", "reviewer_role", "review_date", "review_decision"]:
        if not row.get(key):
            errors.append(f"missing {key}")
    decision = row.get("review_decision")
    if decision in FORBIDDEN:
        errors.append(f"forbidden decision {decision}")
    if decision not in ALLOWED:
        errors.append(f"unsupported decision {decision}")
    for key in FALSE_FIELDS:
        if row.get(key) is not False:
            errors.append(f"{key} must be false")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("decision", type=Path)
    args = parser.parse_args()
    row = json.loads(args.decision.read_text())
    errors = validate_decision(row)
    print("CAPCARD_REVIEWER_DECISION", row.get("candidate_id", "<unknown>"), "PASS" if not errors else "FAIL")
    for error in errors:
        print("ERROR", error)
    return 0 if not errors else 1


if __name__ == "__main__":
    raise SystemExit(main())
