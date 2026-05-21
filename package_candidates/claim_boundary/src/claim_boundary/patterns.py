"""Pattern definitions for the local claim-boundary scanner."""

from __future__ import annotations

import re


def phrase(*parts: str) -> str:
    return "".join(parts)


SUSPICIOUS_PATTERNS: dict[str, tuple[str, ...]] = {
    "PUBLIC_THEOREM_CLAIM": (
        phrase("theorem ", "proved"),
        "proof complete",
        "public theorem claim",
    ),
    "OPEN_PROBLEM_CLAIM": (phrase("open problem ", "solved"),),
    "CERTIFIED_SAFETY_CLAIM": (phrase("certified ", "safety"),),
    "PRODUCTION_CONTROLLER_CLAIM": (phrase("production ", "controller"),),
    "CAPCARD_CERTIFICATION_CLAIM": (phrase("CapCard ", "certifies"),),
    "PETAL_VERIFICATION_CLAIM": (phrase("PETAL ", "verifies"),),
    "PACKAGE_PUBLISH_CLAIM": (phrase("package publish ", "performed"),),
    "HUGGINGFACE_UPLOAD_CLAIM": (phrase("Hugging Face upload ", "performed"),),
    "PETAL_API_UPLOAD_CLAIM": (phrase("PETAL/API upload ", "performed"),),
    "COMMAND_CENTER_DEPLOY_CLAIM": (phrase("command-center deploy ", "performed"),),
    "FORGE_COMPILER_CHANGE_CLAIM": (phrase("Forge compiler behavior change ", "performed"),),
    "HARDWARE_ACTION_CLAIM": (phrase("hardware action ", "performed"),),
    "PUBLIC_READY_TRUE": ("public_ready: true", '"public_ready": true'),
    "UPLOAD_ALLOWED_TRUE": ("upload_allowed: true", '"upload_allowed": true'),
    "RELEASE_READY_TRUE": ("release_ready: true", '"release_ready": true'),
    "MARKETPLACE_READY_TRUE": ("marketplace_ready: true", '"marketplace_ready": true'),
}

BOUNDARY_PATTERNS = (
    "no public theorem/proof/open-problem claim",
    phrase("not certified ", "safety"),
    phrase("no package publish ", "performed"),
    phrase("Hugging Face upload was not ", "performed"),
    "PETAL/API upload remains blocked",
    phrase("not production ", "controller evidence"),
    "release-ready: false",
    "public_ready: false",
    "upload_allowed: false",
    '"public_ready": false',
    '"upload_allowed": false',
    '"release_ready": false',
)

POLICY_MARKERS = ("POLICY_TEXT", "HISTORICAL_TEXT", "NO_GO_BOUNDARY", "BOUNDARY_TEXT")

TOKEN_PATTERNS = (
    re.compile(r"hf_[A-Za-z0-9]{20,}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
    re.compile(r"pypi-[A-Za-z0-9]{20,}"),
)

DEFAULT_EXCLUDE_DIRS = {
    ".git",
    ".venv",
    "__pycache__",
    "node_modules",
    "dist",
    "build",
    ".mypy_cache",
    ".pytest_cache",
}

DEFAULT_TEXT_SUFFIXES = {
    ".lean",
    ".toml",
    ".json",
    ".md",
    ".txt",
    ".py",
    ".yml",
    ".yaml",
    ".cfg",
    ".ini",
}
