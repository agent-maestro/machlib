"""Static package summary for the minimal MachLib umbrella."""

from __future__ import annotations

RELATED_TOOLS = [
    {
        "package_name": "zero-mathlib-checker",
        "purpose": "checks intentional no-Mathlib dependency boundaries",
    },
    {
        "package_name": "claim-boundary",
        "purpose": "scans public copy for overclaim boundaries",
    },
    {
        "package_name": "eml-records",
        "purpose": "validates small EML-style evidence records",
    },
    {
        "package_name": "review-branch-packet",
        "purpose": "structures private review branch packet metadata",
    },
]


def toolchain() -> list[dict[str, str]]:
    """Return the related public packages in the MachLib toolchain."""
    return [dict(row) for row in RELATED_TOOLS]


def package_summary() -> dict[str, object]:
    """Return a non-mutating summary of the package identity."""
    return {
        "package_name": "machlib",
        "version": "0.0.1",
        "status": "pre-alpha",
        "purpose": (
            "Minimal umbrella for zero-Mathlib evidence tooling, EML record "
            "validation, claim-boundary scanning, and private review packet workflows."
        ),
        "boundary": "minimal public umbrella package, not the full MachLib repository",
        "related_tools": toolchain(),
    }
