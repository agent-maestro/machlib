"""Governance crosswalk for CapCard Lab."""

from __future__ import annotations

from pathlib import Path

from .reporting import write_json, write_report


PATTERNS = [
    "model-card-style reporting",
    "dataset/datasheet-style documentation",
    "AI factsheet-style lifecycle metadata",
    "NIST AI RMF-style risk management",
    "AI Verify-style testing/reporting concepts",
    "TEVV/capability-evaluation workflows",
]


def write_crosswalk(repo_root: Path) -> dict:
    data = {
        "status": "PASS",
        "patterns": [
            {
                "pattern": pattern,
                "relationship": "conceptually_aligned",
                "what_capcard_borrows": ["intended use", "limitations", "evidence traceability"],
                "what_capcard_lacks": ["certification", "regulatory control", "public compliance claim"],
                "what_capcard_adds": ["mutation gauntlet", "marketplace readiness", "no-go action fields"],
                "overclaim_risk": "confusing internal evidence with certification",
                "product_opportunity": "private TEVV cockpit for generated artifacts",
                "not_certified_compliant": True,
                "not_regulatory_control": True,
            }
            for pattern in PATTERNS
        ],
    }
    write_json(repo_root / "product_readiness/capcard_lab_governance_crosswalk_2026_05_21.json", data)
    write_report(
        repo_root / "reports/capcard_lab_governance_crosswalk_2026_05_21.md",
        "CapCard Lab Governance Crosswalk",
        ["- CapCard is inspired by model cards, datasheets, factsheets, AI risk workflows, and TEVV concepts.", "- It does not claim compliance, certification, or regulatory-control status."],
    )
    return data
