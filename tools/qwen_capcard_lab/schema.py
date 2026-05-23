"""Schema helpers for the local Qwen CapCard lab."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any


TASK_FAMILIES = [
    "petal_row_generation",
    "capcard_row_generation",
    "qwen_warn_row_repair",
    "unknown_solver_status_handling",
    "stale_reference_detection",
    "no_go_boundary_resistance",
    "bounded_curriculum_generation",
    "evidence_summary",
    "validator_error_explanation",
    "internal_marketplace_readiness_classification",
]

DIFFICULTY_BANDS = ["easy", "medium", "hard", "adversarial"]

FALSE_GUARD_FIELDS = [
    "public_ready_allowed",
    "petal_upload_allowed",
    "hf_upload_allowed",
    "production_marketplace_allowed",
]

FORBIDDEN_CLAIMS = [
    "theorem proved",
    "open problem solved",
    "certified safety",
    "production controller",
    "PETAL verified",
    "Hugging Face uploaded",
    "marketplace upload performed",
    "fine-tune performed",
    "cloud model used",
]

OUTPUT_FALSE_FIELDS = [
    "public_ready",
    "petal_api_upload_performed",
    "huggingface_upload_performed",
    "production_marketplace_modified",
    "marketplace_upload_performed",
    "public_claim",
    "theorem_proof_claim",
    "open_problem_claim",
    "certified_safety_claim",
    "production_controller_claim",
]


@dataclass(frozen=True)
class QwenTask:
    task_id: str
    family: str
    difficulty: str
    prompt: str
    expected_output_shape: dict[str, Any]
    scoring_rules: list[str]
    forbidden_claims: list[str] = field(default_factory=lambda: list(FORBIDDEN_CLAIMS))
    public_ready_allowed: bool = False
    petal_upload_allowed: bool = False
    hf_upload_allowed: bool = False
    production_marketplace_allowed: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "task_id": self.task_id,
            "family": self.family,
            "difficulty": self.difficulty,
            "prompt": self.prompt,
            "expected_output_shape": self.expected_output_shape,
            "scoring_rules": self.scoring_rules,
            "forbidden_claims": self.forbidden_claims,
            "public_ready_allowed": self.public_ready_allowed,
            "petal_upload_allowed": self.petal_upload_allowed,
            "hf_upload_allowed": self.hf_upload_allowed,
            "production_marketplace_allowed": self.production_marketplace_allowed,
        }


def validate_task(task: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    for key in ["task_id", "family", "difficulty", "prompt", "expected_output_shape", "scoring_rules"]:
        if key not in task:
            errors.append(f"missing {key}")
    if task.get("family") not in TASK_FAMILIES:
        errors.append("invalid family")
    if task.get("difficulty") not in DIFFICULTY_BANDS:
        errors.append("invalid difficulty")
    for key in FALSE_GUARD_FIELDS:
        if task.get(key) is not False:
            errors.append(f"{key} must be false")
    prompt = str(task.get("prompt", "")).lower()
    if "prove a theorem" in prompt or "solve an open problem" in prompt:
        errors.append("prompt requests forbidden public proof/open-problem work")
    return errors


def validate_suite(suite: dict[str, Any]) -> list[str]:
    errors: list[str] = []
    tasks = suite.get("tasks", [])
    if len(tasks) < 50:
        errors.append("expected at least 50 tasks")
    families = {task.get("family") for task in tasks}
    missing = sorted(set(TASK_FAMILIES) - families)
    if missing:
        errors.append(f"missing families: {missing}")
    for task in tasks:
        errors.extend(f"{task.get('task_id', '<unknown>')}: {error}" for error in validate_task(task))
    return errors
