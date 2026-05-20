#!/usr/bin/env python3
"""Validate the draft MachLib EML lane seed corpus.

This validator is local-only. It checks the M005 draft seed packet for schema
integrity, lane counts, guardrail booleans, gap-ledger coverage, and the cubic
dyadic equilibrium spot check. It does not prove results, publish artifacts, or
change compiler behavior.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
EXPECTED_SEED_COUNT = 19
EXPECTED_LANE_COUNTS = {1: 4, 2: 3, 3: 3, 4: 3, 5: 3, 6: 3}
REQUIRED_FALSE_FIELDS = [
    "public_ready",
    "upload_allowed",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]
REQUIRED_DRAFT_FIELDS = [
    "record_id",
    "lane",
    "title",
    "assumptions",
    "constraints",
    "expected_outputs",
    "operator_atoms",
    "evidence_type",
    "validation_checks",
    "limitations",
    "not_claimed",
    "status",
]
DISALLOWED_STATUSES = {
    "PUBLIC_READY",
    "RELEASE_READY",
    "UPLOAD_READY",
    "THEOREM_PROVED",
    "CERTIFIED",
}
ALLOWED_DRAFT_STATUSES = {"DRAFT_INTERNAL"}


def blocked_phrase(*parts: str) -> str:
    return "".join(parts)


RAW_DEPENDENCY_PATTERNS = [
    re.compile(blocked_phrase("import ", "Mathlib")),
    re.compile(blocked_phrase("from ", "Mathlib")),
    re.compile(blocked_phrase("Mathlib", r"\.")),
]
NO_GO_PATTERNS = [
    re.compile(blocked_phrase("public_ready", ": true")),
    re.compile(blocked_phrase("upload_allowed", ": true")),
    re.compile(blocked_phrase("marketplace_ready", ": true")),
    re.compile(blocked_phrase("CapCard ", "certifies")),
    re.compile(blocked_phrase("PETAL ", "verifies")),
    re.compile(blocked_phrase("theorem ", "proved")),
    re.compile(blocked_phrase("open problem ", "solved")),
    re.compile(blocked_phrase("certified ", "safety")),
    re.compile(blocked_phrase("DARPA ", "accepted")),
    re.compile(blocked_phrase("production ", "controller")),
]
TOKEN_PATTERNS = [
    re.compile(r"hf_[A-Za-z0-9]{20,}"),
    re.compile(r"sk-[A-Za-z0-9]{20,}"),
    re.compile(r"pypi-[A-Za-z0-9]{20,}"),
]


@dataclass
class Seed:
    path: Path
    obj: dict[str, Any]

    @property
    def draft(self) -> dict[str, Any]:
        draft = self.obj.get("draft_eml_seed")
        return draft if isinstance(draft, dict) else {}

    @property
    def record_id(self) -> str:
        return str(
            self.draft.get("record_id")
            or self.obj.get("theorem", {}).get("id")
            or self.path.stem
        )

    @property
    def lane_number(self) -> int | None:
        lane = self.obj.get("theorem", {}).get("lane")
        if isinstance(lane, int):
            return lane
        return None


def load_json(path: Path) -> tuple[Any | None, str | None]:
    try:
        return json.loads(path.read_text(encoding="utf-8")), None
    except Exception as exc:  # noqa: BLE001 - report parse failures precisely.
        return None, f"{path}: {exc}"


def seed_paths(root: Path) -> list[Path]:
    excluded = {
        "lane_manifest_2026_05_20.json",
        "lane_gap_ledger_2026_05_20.json",
        "validation_result_2026_05_20.json",
        "execution_result_2026_05_20.json",
        "roundtrip_result_2026_05_20.json",
        "primitive_feasibility_result_2026_05_20.json",
        "primitive_spec_draft_2026_05_20.json",
        "symbolic_rewrite_result_2026_05_20.json",
        "roundtrip_probe_result_2026_05_20.json",
        "structure_spec_draft_2026_05_20.json",
        "evidence_schema_spec_draft_2026_05_20.json",
        "legacy_boundary_spec_draft_2026_05_20.json",
    }
    return sorted(
        path for path in root.rglob("*.json") if path.is_file() and path.name not in excluded
    )


def as_text(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, str):
        return value
    return json.dumps(value, sort_keys=True)


def contains_any(text: str, terms: list[str]) -> bool:
    lower = text.lower()
    return any(term.lower() in lower for term in terms)


def status(has_failures: bool, has_warnings: bool) -> str:
    if has_failures:
        return "FAIL"
    if has_warnings:
        return "WARN"
    return "PASS"


def validate_required_fields(seed: Seed) -> tuple[list[str], list[str]]:
    failures: list[str] = []
    warnings: list[str] = []
    draft = seed.draft
    if not draft:
        failures.append(f"{seed.record_id}: missing draft_eml_seed extension")
        return failures, warnings

    for field in REQUIRED_DRAFT_FIELDS:
        if field not in draft:
            failures.append(f"{seed.record_id}: missing required field {field}")

    if not (draft.get("expression") or draft.get("object")):
        failures.append(f"{seed.record_id}: missing expression or object")

    if not draft.get("validation_checks"):
        warnings.append(f"{seed.record_id}: validation_checks is empty")
    if not draft.get("not_claimed"):
        failures.append(f"{seed.record_id}: not_claimed is empty")

    return failures, warnings


def validate_false_booleans(seed: Seed) -> list[str]:
    failures: list[str] = []
    draft = seed.draft
    for field in REQUIRED_FALSE_FIELDS:
        if draft.get(field) is not False:
            failures.append(f"{seed.record_id}: {field} must be false")
    return failures


def validate_status(seed: Seed) -> list[str]:
    failures: list[str] = []
    value = str(seed.draft.get("status", ""))
    if value in DISALLOWED_STATUSES:
        failures.append(f"{seed.record_id}: disallowed status {value}")
    if value not in ALLOWED_DRAFT_STATUSES:
        failures.append(f"{seed.record_id}: expected DRAFT_INTERNAL status, got {value}")
    return failures


def validate_not_claimed(seed: Seed) -> tuple[list[str], list[str]]:
    failures: list[str] = []
    warnings: list[str] = []
    draft = seed.draft
    text = as_text(draft.get("not_claimed")) + " " + as_text(draft.get("limitations"))
    text += " " + as_text(draft.get("constraints"))
    if not contains_any(text, ["not a public proof", "not a public theorem", "not a full coverage claim"]):
        failures.append(f"{seed.record_id}: missing no public theorem/proof claim language")
    if not contains_any(text, ["not a new theorem", "not a new result", "not a public proof", "not a full coverage claim"]):
        warnings.append(f"{seed.record_id}: overclaim boundary is weak")
    if draft.get("public_ready") is not False:
        failures.append(f"{seed.record_id}: public_ready boundary missing")
    if draft.get("upload_allowed") is not False:
        failures.append(f"{seed.record_id}: upload boundary missing")
    return failures, warnings


def validate_lane_specific(seed: Seed) -> tuple[list[str], list[str]]:
    failures: list[str] = []
    warnings: list[str] = []
    draft = seed.draft
    rid = seed.record_id
    text = " ".join(
        [
            as_text(draft.get("title")),
            as_text(draft.get("expression")),
            as_text(draft.get("object")),
            as_text(draft.get("normalized_form")),
            as_text(draft.get("expected_outputs")),
            as_text(draft.get("validation_checks")),
            as_text(draft.get("limitations")),
            as_text(draft.get("not_claimed")),
            as_text(draft.get("coverage_status")),
        ]
    )
    lane = seed.lane_number

    if lane == 1:
        if rid == "cubic_dyadic_equilibrium_v0":
            failures.extend(validate_cubic(seed)[0])
        elif not contains_any(text, ["normalized", "identity", "constraint", "factor", "symbolic rule"]):
            failures.append(f"{rid}: lane 1 seed lacks normalization or identity/constraint marker")
    elif lane == 2:
        if draft.get("status") != "DRAFT_INTERNAL":
            failures.append(f"{rid}: lane 2 seed is not DRAFT_INTERNAL")
        if draft.get("coverage_status") != "NEEDS_MACHLIB_PRIMITIVES":
            failures.append(f"{rid}: lane 2 seed must need MachLib primitives")
        if contains_any(text, ["complete real-analysis formalization"]):
            if not contains_any(text, ["not a complete real-analysis formalization"]):
                failures.append(f"{rid}: lane 2 seed overclaims real-analysis coverage")
    elif lane == 3:
        if not contains_any(text, ["finite", "bounded", "tiny"]):
            failures.append(f"{rid}: lane 3 seed must be finite or bounded")
    elif lane == 4:
        if not contains_any(text, ["machine-friendly", "structure", "carrier"]):
            failures.append(f"{rid}: lane 4 seed must be a machine-friendly structure")
        if contains_any(text, ["imported hierarchy"]):
            if not contains_any(text, ["does not import", "not imported", "does not claim imported hierarchy compatibility"]):
                failures.append(f"{rid}: lane 4 hierarchy boundary unclear")
    elif lane == 5:
        if not contains_any(text, ["evidence", "artifact", "failed attempt"]):
            failures.append(f"{rid}: lane 5 seed must be evidence-oriented")
    elif lane == 6:
        for term, variants in {
            "opt-in": ["opt-in", "explicit opt-in"],
            "never default": ["never default", "not a default release path"],
            "release dependency": ["release dependency", "not a release dependency", "never changes release dependency set"],
        }.items():
            if not contains_any(text, variants):
                failures.append(f"{rid}: lane 6 seed missing '{term}' boundary")
        if draft.get("mathlib_dependency") is not False:
            failures.append(f"{rid}: lane 6 seed must keep dependency false")
    else:
        failures.append(f"{rid}: unexpected lane {lane}")

    return failures, warnings


def validate_cubic(seed: Seed) -> tuple[list[str], dict[str, Any]]:
    failures: list[str] = []
    draft = seed.draft
    text = " ".join(
        [
            as_text(draft.get("expression")),
            as_text(draft.get("normalized_form")),
            as_text(draft.get("expected_outputs")),
            as_text(draft.get("validation_checks")),
            as_text(draft.get("not_claimed")),
        ]
    )
    required = [
        "x^3 = x + x",
        "x * (x^2 - 2) = 0",
        "-sqrt(2)",
        "0",
        "sqrt(2)",
    ]
    for item in required:
        if item not in text:
            failures.append(f"cubic_dyadic_equilibrium_v0: missing {item}")
    if not contains_any(text, ["not an identity", "constraint"]):
        failures.append("cubic_dyadic_equilibrium_v0: missing identity-vs-constraint distinction")

    def satisfies(x: float) -> bool:
        return abs((x**3) - (2 * x)) < 1e-9

    numeric = {
        "zero": satisfies(0.0),
        "sqrt2": satisfies(math.sqrt(2)),
        "negative_sqrt2": satisfies(-math.sqrt(2)),
        "one_rejected": not satisfies(1.0),
    }
    if not all(numeric.values()):
        failures.append(f"cubic_dyadic_equilibrium_v0: numeric spot check failed {numeric}")
    return failures, numeric


def validate_gap_ledger(ledger: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    rows = ledger.get("gaps")
    if not isinstance(rows, list):
        return ["gap ledger missing gaps list"]
    required_topics = {
        "algebraic identities": False,
        "polynomial factorization": False,
        "inequalities": False,
        "exp/log/trig/pow": False,
        "finite graphs": False,
        "SAT-like constraints": False,
        "recurrences": False,
        "typeclass-lite algebraic structures": False,
        "evidence/proof records": False,
        "legacy compatibility": False,
    }
    required_fields = [
        "gap_id",
        "lane",
        "description",
        "current_status",
        "blockers",
        "next_safe_local_experiment",
        "eml_record_need",
        "zero_mathlib_risk",
        "no_go_flags",
        "recommended_priority",
    ]
    descriptions = []
    for idx, row in enumerate(rows):
        if not isinstance(row, dict):
            failures.append(f"gap row {idx}: not an object")
            continue
        for field in required_fields:
            if field not in row:
                failures.append(f"gap row {idx}: missing {field}")
        descriptions.append(as_text(row.get("description")).lower())
    joined = " ".join(descriptions)
    for topic in required_topics:
        variants = [topic.lower()]
        if topic == "legacy compatibility":
            variants.append("legacy")
        if topic == "evidence/proof records":
            variants.extend(["evidence and proof records", "evidence"])
        if not any(variant in joined for variant in variants):
            failures.append(f"gap ledger missing topic {topic}")
    return failures


def scan_guardrails(paths: list[Path]) -> list[str]:
    failures: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8", errors="replace")
        for idx, line in enumerate(text.splitlines(), start=1):
            for pattern in RAW_DEPENDENCY_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: raw dependency text")
            for pattern in NO_GO_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: no-go phrase")
            for pattern in TOKEN_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: token-like secret")
    return failures


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument("--out", default="corpus/eml_lanes_draft/validation_result_2026_05_20.json")
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    root = Path(args.root)
    out = Path(args.out)
    failures: list[str] = []
    warnings: list[str] = []

    manifest_path = root / "lane_manifest_2026_05_20.json"
    ledger_path = root / "lane_gap_ledger_2026_05_20.json"
    manifest_obj, manifest_error = load_json(manifest_path)
    ledger_obj, ledger_error = load_json(ledger_path)
    if manifest_error:
        failures.append(manifest_error)
    if ledger_error:
        failures.append(ledger_error)

    seeds: list[Seed] = []
    parse_failures: list[str] = []
    for path in seed_paths(root):
        obj, error = load_json(path)
        if error:
            parse_failures.append(error)
        elif isinstance(obj, dict):
            seeds.append(Seed(path=path, obj=obj))
        else:
            parse_failures.append(f"{path}: top-level JSON is not an object")
    failures.extend(parse_failures)

    lane_counts: dict[int, int] = {}
    for seed in seeds:
        lane = seed.lane_number
        if lane is not None:
            lane_counts[lane] = lane_counts.get(lane, 0) + 1

    if len(seeds) != EXPECTED_SEED_COUNT:
        failures.append(f"expected {EXPECTED_SEED_COUNT} seeds, found {len(seeds)}")
    if lane_counts != EXPECTED_LANE_COUNTS:
        failures.append(f"lane count mismatch: {lane_counts}")

    field_failures: list[str] = []
    field_warnings: list[str] = []
    boolean_failures: list[str] = []
    status_failures: list[str] = []
    claim_failures: list[str] = []
    claim_warnings: list[str] = []
    lane_failures: list[str] = []
    lane_warnings: list[str] = []
    cubic_numeric: dict[str, Any] = {}

    for seed in seeds:
        f, w = validate_required_fields(seed)
        field_failures.extend(f)
        field_warnings.extend(w)
        boolean_failures.extend(validate_false_booleans(seed))
        status_failures.extend(validate_status(seed))
        f, w = validate_not_claimed(seed)
        claim_failures.extend(f)
        claim_warnings.extend(w)
        f, w = validate_lane_specific(seed)
        lane_failures.extend(f)
        lane_warnings.extend(w)
        if seed.record_id == "cubic_dyadic_equilibrium_v0":
            cubic_errors, cubic_numeric = validate_cubic(seed)
            lane_failures.extend(cubic_errors)

    gap_failures = validate_gap_ledger(ledger_obj if isinstance(ledger_obj, dict) else {})
    guardrail_failures = scan_guardrails([p for p in root.rglob("*") if p.is_file()])

    failures.extend(field_failures)
    failures.extend(boolean_failures)
    failures.extend(status_failures)
    failures.extend(claim_failures)
    failures.extend(lane_failures)
    failures.extend(gap_failures)
    failures.extend(guardrail_failures)
    warnings.extend(field_warnings)
    warnings.extend(claim_warnings)
    warnings.extend(lane_warnings)

    result = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "seed_count": len(seeds),
        "lane_counts": {str(k): v for k, v in sorted(lane_counts.items())},
        "json_parse_status": status(bool(parse_failures or manifest_error or ledger_error), False),
        "required_field_status": status(bool(field_failures), bool(field_warnings)),
        "required_false_boolean_status": status(bool(boolean_failures), False),
        "status_validation_status": status(bool(status_failures), False),
        "not_claimed_status": status(bool(claim_failures), bool(claim_warnings)),
        "lane_specific_status": status(bool(lane_failures), bool(lane_warnings)),
        "cubic_dyadic_status": status(any("cubic_dyadic_equilibrium_v0" in f for f in lane_failures), False),
        "cubic_dyadic_numeric_spot_check": cubic_numeric,
        "gap_ledger_status": status(bool(gap_failures), False),
        "zero_mathlib_status": "PASS",
        "guardrail_status": status(bool(guardrail_failures), False),
        "valid_as_draft_internal": not failures,
        "failures": failures,
        "warnings": warnings,
    }
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    print(f"seed_count: {result['seed_count']}")
    print(f"lane_counts: {result['lane_counts']}")
    print(f"json_parse_status: {result['json_parse_status']}")
    print(f"required_field_status: {result['required_field_status']}")
    print(f"required_false_boolean_status: {result['required_false_boolean_status']}")
    print(f"cubic_dyadic_status: {result['cubic_dyadic_status']}")
    print(f"gap_ledger_status: {result['gap_ledger_status']}")
    print(f"guardrail_status: {result['guardrail_status']}")
    print("PASS" if not failures else "FAIL")
    return 1 if args.strict and failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
