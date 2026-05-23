from pathlib import Path

from tools.capcard_lab.governance_crosswalk import PATTERNS, write_crosswalk


def test_patterns_present():
    assert len(PATTERNS) >= 6


def test_crosswalk_no_compliance_claim():
    data = write_crosswalk(Path("."))
    for row in data["patterns"]:
        assert row["not_certified_compliant"] is True
        assert row["not_regulatory_control"] is True


def test_crosswalk_status():
    assert write_crosswalk(Path("."))["status"] == "PASS"
