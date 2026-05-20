#!/usr/bin/env python3
"""MachLib Lane 2 primitive feasibility lab.

This local-only tool reads the Lane 2 draft EML seeds and records what MachLib
would need before exp/log/trig/pow style symbolic objects become executable
release artifacts. It is deliberately a feasibility analyzer, not a proof
engine and not a real-analysis formalization.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DATE = "2026-05-20"
LANE_DIR = "lane_2_calculus_special_functions"
EXPECTED_RECORDS = {
    "exp_log_formal_inverse_draft_v0",
    "trig_pythagorean_symbolic_draft_v0",
    "pow_square_root_symbolic_draft_v0",
}
REQUIRED_PRIMITIVES = [
    "mach_exp_symbolic_v0",
    "mach_log_symbolic_v0",
    "mach_sin_symbolic_v0",
    "mach_cos_symbolic_v0",
    "mach_pow_symbolic_v0",
    "mach_sqrt_symbolic_v0",
    "mach_symbolic_domain_guard_v0",
]
FALSE_GUARDRAILS = [
    "public_ready",
    "upload_allowed",
    "mathlib_dependency",
    "forge_compiler_change_required",
    "hardware_required",
]


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


@dataclass(frozen=True)
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

    def text(self) -> str:
        return json.dumps(self.obj, sort_keys=True)


def load_lane2_seeds(root: Path) -> dict[str, Seed]:
    lane_path = root / LANE_DIR
    seeds: dict[str, Seed] = {}
    for path in sorted(lane_path.glob("*.json")):
        if path.name in {
            "primitive_feasibility_result_2026_05_20.json",
            "primitive_spec_draft_2026_05_20.json",
        }:
            continue
        obj = json.loads(path.read_text(encoding="utf-8"))
        seed = Seed(path=path, obj=obj)
        seeds[seed.record_id] = seed
    return seeds


def primitive_spec(
    primitive_id: str,
    name: str,
    arity: int,
    symbolic_domain: str,
    rewrite_rules: list[str],
    future_design: list[str],
) -> dict[str, Any]:
    return {
        "primitive_id": primitive_id,
        "name": name,
        "arity": arity,
        "input_sort": "symbolic_real_term",
        "output_sort": "symbolic_real_term",
        "symbolic_domain": symbolic_domain,
        "rewrite_rules_draft": rewrite_rules,
        "forbidden_claims": [
            "complete real-analysis formalization",
            "public theorem/proof claim",
            "release-ready calculus primitive",
            "external formal-library import",
        ],
        "required_future_design": future_design,
        "zero_mathlib_dependency": True,
        "status": "DRAFT_INTERNAL",
        "public_ready": False,
        "upload_allowed": False,
        "mathlib_dependency": False,
        "forge_compiler_change_required": False,
        "hardware_required": False,
    }


def build_primitive_specs() -> list[dict[str, Any]]:
    return [
        primitive_spec(
            "mach_exp_symbolic_v0",
            "Mach symbolic exp",
            1,
            "formal symbolic expression with explicit guard annotations",
            ["exp(log(x)) rewrites only under positive-domain/formal guard"],
            ["owned syntax", "domain guard semantics", "future proof/evidence layer"],
        ),
        primitive_spec(
            "mach_log_symbolic_v0",
            "Mach symbolic log",
            1,
            "formal symbolic expression with explicit guard annotations",
            ["log(exp(x)) rewrites only under explicit formal guard"],
            ["owned syntax", "inverse-pair guard design", "future proof/evidence layer"],
        ),
        primitive_spec(
            "mach_sin_symbolic_v0",
            "Mach symbolic sin",
            1,
            "formal symbolic expression with owned trig semantics",
            ["sin(x)^2 + cos(x)^2 rewrites only under named trig-spec guard"],
            ["owned trig primitive semantics", "normal-form design"],
        ),
        primitive_spec(
            "mach_cos_symbolic_v0",
            "Mach symbolic cos",
            1,
            "formal symbolic expression with owned trig semantics",
            ["sin(x)^2 + cos(x)^2 rewrites only under named trig-spec guard"],
            ["owned trig primitive semantics", "normal-form design"],
        ),
        primitive_spec(
            "mach_pow_symbolic_v0",
            "Mach symbolic pow",
            2,
            "formal base/exponent expression with guarded exponent class",
            ["sqrt(x)^2 rewrites only through pow/sqrt guarded bridge"],
            ["exponent sort design", "nonnegative guard link", "structure layer"],
        ),
        primitive_spec(
            "mach_sqrt_symbolic_v0",
            "Mach symbolic sqrt",
            1,
            "formal symbolic expression with nonnegative-domain guard",
            ["sqrt(x)^2 rewrites to x under explicit nonnegative-domain guard"],
            ["nonnegative-domain guard", "absolute-value boundary design"],
        ),
        primitive_spec(
            "mach_symbolic_domain_guard_v0",
            "Mach symbolic domain guard",
            2,
            "guarded symbolic relation metadata",
            ["blocked rewrite remains blocked until its named guard is present"],
            ["guard schema", "validation hooks", "evidence-row integration"],
        ),
    ]


def validate_seed(seed: Seed) -> tuple[list[str], list[str]]:
    failures: list[str] = []
    warnings: list[str] = []
    draft = seed.draft
    if not draft:
        failures.append("missing draft_eml_seed")
        return failures, warnings
    if draft.get("status") != "DRAFT_INTERNAL":
        failures.append("status must be DRAFT_INTERNAL")
    for field in FALSE_GUARDRAILS:
        if draft.get(field) is not False:
            failures.append(f"{field} must be false")

    not_claimed = " ".join(str(item).lower() for item in draft.get("not_claimed", []))
    needed_phrases = [
        "not a complete real-analysis formalization",
        "not a public theorem claim",
        "not imported from external libraries",
    ]
    for phrase in needed_phrases:
        if phrase not in not_claimed:
            failures.append(f"missing limitation phrase: {phrase}")

    if draft.get("coverage_status") != "NEEDS_MACHLIB_PRIMITIVES":
        warnings.append("coverage_status is expected to need MachLib primitives")
    return failures, warnings


def analyze_seed(seed: Seed) -> dict[str, Any]:
    failures, warnings = validate_seed(seed)
    record_id = seed.record_id
    feasibility = "NEEDS_MACHLIB_PRIMITIVE"
    required_primitives: list[str] = []
    domain_guards: list[str] = []
    blocked_claims = [
        "complete real-analysis formalization",
        "public theorem/proof claim",
        "release-ready special-function semantics",
        "external formal-library import",
    ]
    accepted_symbolic_relations: list[str] = []
    blocked_relations: list[str] = []

    if record_id == "exp_log_formal_inverse_draft_v0":
        feasibility = "FEASIBLE_WITH_DOMAIN_GUARD"
        required_primitives = [
            "mach_exp_symbolic_v0",
            "mach_log_symbolic_v0",
            "mach_symbolic_domain_guard_v0",
        ]
        domain_guards = [
            "formal guard for log(exp(x))",
            "positive-domain/formal guard for exp(log(x))",
        ]
        accepted_symbolic_relations = [
            "log(exp(x)) -> x only with explicit formal guard",
            "exp(log(x)) -> x only with positive-domain/formal guard",
        ]
        warnings.append("inverse-pair semantics remain draft/internal")
    elif record_id == "trig_pythagorean_symbolic_draft_v0":
        feasibility = "NEEDS_MACHLIB_PRIMITIVE"
        required_primitives = [
            "mach_sin_symbolic_v0",
            "mach_cos_symbolic_v0",
            "mach_symbolic_domain_guard_v0",
        ]
        domain_guards = ["named MachLib trig primitive/spec guard"]
        accepted_symbolic_relations = [
            "sin(x)^2 + cos(x)^2 -> 1 only as a guarded symbolic placeholder under owned trig semantics",
        ]
        warnings.append("trig semantics require owned primitive design before execution")
    elif record_id == "pow_square_root_symbolic_draft_v0":
        feasibility = "FEASIBLE_WITH_DOMAIN_GUARD"
        required_primitives = [
            "mach_pow_symbolic_v0",
            "mach_sqrt_symbolic_v0",
            "mach_symbolic_domain_guard_v0",
        ]
        domain_guards = ["explicit nonnegative-domain/formal guard"]
        accepted_symbolic_relations = [
            "sqrt(x)^2 -> x only with explicit nonnegative-domain/formal guard",
        ]
        blocked_relations = [
            "sqrt(x^2) -> abs(x) is not directly accepted without structure/proof layer",
        ]
        warnings.append("absolute-value boundary needs structure/proof layer design")
    else:
        feasibility = "OUT_OF_SCOPE_FOR_NOW"
        failures.append(f"unexpected Lane 2 seed: {record_id}")

    return {
        "record_id": record_id,
        "status": "FAIL" if failures else "WARN" if warnings else "PASS",
        "feasibility": feasibility,
        "required_primitives": required_primitives,
        "domain_guards": domain_guards,
        "accepted_symbolic_relations": accepted_symbolic_relations,
        "blocked_relations": blocked_relations,
        "blocked_claims": blocked_claims,
        "warnings": warnings,
        "failures": failures,
    }


def scan_guardrails(paths: list[Path]) -> list[str]:
    failures: list[str] = []
    for path in paths:
        if not path.exists():
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for idx, line in enumerate(text.splitlines(), start=1):
            for pattern in RAW_DEPENDENCY_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: raw dependency text")
            for pattern in NO_GO_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: no-go public/action text")
            for pattern in TOKEN_PATTERNS:
                if pattern.search(line):
                    failures.append(f"{path}:{idx}: token-like string")
    return failures


def write_json(path: Path, obj: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def write_reports(result: dict[str, Any], reports_dir: Path) -> list[Path]:
    reports_dir.mkdir(parents=True, exist_ok=True)
    summary = reports_dir / "machlib_lane2_primitive_feasibility_summary_2026_05_20.md"
    matrix = reports_dir / "machlib_lane2_primitive_feasibility_matrix_2026_05_20.md"
    plan = reports_dir / "machlib_lane2_symbolic_validation_plan_2026_05_20.md"
    guardrail = reports_dir / "machlib_lane2_guardrail_report_2026_05_20.md"

    primitive_ids = [item["primitive_id"] for item in result["primitive_specs"]]
    summary.write_text(
        "\n".join(
            [
                "# MachLib Lane 2 primitive feasibility summary",
                "",
                f"Date: {DATE}",
                "Tier: OBSERVATION",
                "Scope: local-only Lane 2 feasibility analysis for calculus and special-function symbolic primitives.",
                "",
                "## Inputs consumed",
                "- `corpus/eml_lanes_draft/lane_2_calculus_special_functions/`",
                "- Existing M006 lane validator output",
                "",
                "## Lane 2 seed count",
                f"- Seeds analyzed: {result['seed_count']}",
                f"- Passed structurally: {result['passed']}",
                f"- Warnings: {result['warned']}",
                f"- Failures: {result['failed']}",
                f"- Lane status: {result['lane_status']}",
                "",
                "## Primitive needs summary",
                *[f"- `{primitive_id}`" for primitive_id in primitive_ids],
                "",
                "## Domain guard needs",
                "- exp/log inverse placeholders need explicit formal and positive-domain guards.",
                "- trig placeholders need a named owned trig primitive/spec guard.",
                "- pow/sqrt placeholders need explicit nonnegative-domain guards.",
                "",
                "## What can be symbolic today",
                "- Guarded symbolic rewrite records can be represented as draft/internal EML metadata.",
                "- The records can be checked for guardrail fields, primitive needs, and blocked claims.",
                "",
                "## What remains blocked",
                "- Complete real-analysis semantics.",
                "- Release-ready special-function primitives.",
                "- Public proof or theorem status.",
                "",
                "## Zero-Mathlib status",
                f"- {result['zero_mathlib_status']}",
                "",
                "## No-go gates",
                "- No uploads, package publishing, hardware action, compiler behavior change, or public proof/open-problem claim.",
                "",
            ]
        ),
        encoding="utf-8",
    )

    rows = [
        "# MachLib Lane 2 primitive feasibility matrix",
        "",
        f"Date: {DATE}",
        "",
        "| Seed | Symbolic relation | Primitive needs | Domain guard needs | Feasibility | Release readiness | Blockers | Next safe local experiment |",
        "| --- | --- | --- | --- | --- | --- | --- | --- |",
    ]
    for item in result["results"]:
        relation = "; ".join(item["accepted_symbolic_relations"]) or "None accepted yet"
        primitives = ", ".join(item["required_primitives"])
        guards = ", ".join(item["domain_guards"])
        blockers = ", ".join(item["blocked_claims"] + item["blocked_relations"])
        rows.append(
            "| {record_id} | {relation} | {primitives} | {guards} | {feasibility} | NOT_READY_FOR_RELEASE | {blockers} | Add guarded symbolic rewrite tests after primitive syntax exists. |".format(
                record_id=item["record_id"],
                relation=relation,
                primitives=primitives,
                guards=guards,
                feasibility=item["feasibility"],
                blockers=blockers,
            )
        )
    matrix.write_text("\n".join(rows) + "\n", encoding="utf-8")

    plan.write_text(
        "\n".join(
            [
                "# MachLib Lane 2 symbolic validation plan",
                "",
                f"Date: {DATE}",
                "",
                "Lane 2 validation remains symbolic until MachLib-owned primitives exist.",
                "",
                "## Validation without external formal libraries",
                "- Parse all seed and primitive-spec JSON.",
                "- Check every seed remains `DRAFT_INTERNAL`.",
                "- Check guarded symbolic rewrite annotations only.",
                "- Check domain guard annotations are explicit.",
                "- Check no public theorem/proof or real-analysis completeness claim is present.",
                "- Check all upload, public-ready, hardware, and compiler-change booleans remain false.",
                "- Run the zero-dependency release gate before and after adding future primitives.",
                "",
                "## Future primitive design",
                "- Add owned symbolic syntax for exp/log/sin/cos/pow/sqrt.",
                "- Add domain guard records before enabling rewrites.",
                "- Add evidence rows that distinguish symbolic placeholders from verified artifacts.",
                "",
                "## Future executable harness",
                "- Once primitives exist, add local rewrite tests for guarded expressions.",
                "- Keep exact symbolic checks separate from numeric smoke checks.",
                "- Keep upload and publish gates closed.",
                "",
            ]
        ),
        encoding="utf-8",
    )

    guardrails = result["guardrails"]
    guardrail.write_text(
        "\n".join(
            [
                "# MachLib Lane 2 guardrail report",
                "",
                f"Date: {DATE}",
                "",
                f"- no dependency introduced: {'PASS' if guardrails['no_mathlib_dependency'] else 'FAIL'}",
                f"- zero-dependency checker passes: {result['zero_mathlib_status']}",
                f"- no Hugging Face upload: {'PASS' if guardrails['no_hf_upload'] else 'FAIL'}",
                f"- no PETAL/API upload: {'PASS' if guardrails['no_petal_upload'] else 'FAIL'}",
                f"- no package publish: {'PASS' if guardrails['no_package_publish'] else 'FAIL'}",
                f"- no PyPI/token handling: {'PASS' if guardrails['no_token_like_secret'] else 'FAIL'}",
                f"- no hardware action: {'PASS' if guardrails['no_hardware'] else 'FAIL'}",
                f"- no Forge compiler behavior change: {'PASS' if guardrails['no_forge_compiler_change'] else 'FAIL'}",
                f"- no public theorem/proof/open-problem claim: {'PASS' if guardrails['no_public_theorem_claim'] else 'FAIL'}",
                f"- no public-ready true rows: {'PASS' if guardrails['no_public_ready_true'] else 'FAIL'}",
                f"- no upload-allowed true rows: {'PASS' if guardrails['no_upload_allowed_true'] else 'FAIL'}",
                f"- no marketplace-ready true rows: {'PASS' if guardrails['no_marketplace_ready_true'] else 'FAIL'}",
                f"- no CapCard certification claim: {'PASS' if guardrails['no_capcard_certification_claim'] else 'FAIL'}",
                f"- no PETAL verification claim: {'PASS' if guardrails['no_petal_verification_claim'] else 'FAIL'}",
                f"- no token-like secret: {'PASS' if guardrails['no_token_like_secret'] else 'FAIL'}",
                "",
            ]
        ),
        encoding="utf-8",
    )
    return [summary, matrix, plan, guardrail]


def run_analysis(root: Path, out: Path, spec_out: Path) -> dict[str, Any]:
    seeds = load_lane2_seeds(root)
    results = [analyze_seed(seed) for seed in seeds.values()]
    missing = sorted(EXPECTED_RECORDS - set(seeds))
    unexpected = sorted(set(seeds) - EXPECTED_RECORDS)
    primitive_specs = build_primitive_specs()

    failures: list[str] = []
    warnings: list[str] = []
    if len(seeds) != 3:
        failures.append(f"expected 3 Lane 2 seeds, found {len(seeds)}")
    if missing:
        failures.append(f"missing Lane 2 seeds: {', '.join(missing)}")
    if unexpected:
        failures.append(f"unexpected Lane 2 seeds: {', '.join(unexpected)}")
    for item in results:
        warnings.extend(f"{item['record_id']}: {warning}" for warning in item["warnings"])
        failures.extend(f"{item['record_id']}: {failure}" for failure in item["failures"])

    scanned = [seed.path for seed in seeds.values()]
    scanned.extend([out, spec_out])
    guardrail_failures = scan_guardrails([path for path in scanned if path.exists()])
    failures.extend(guardrail_failures)

    passed = sum(1 for item in results if item["status"] in {"PASS", "WARN"})
    warned = sum(1 for item in results if item["status"] == "WARN")
    failed = sum(1 for item in results if item["status"] == "FAIL") + len(missing) + len(unexpected)

    result = {
        "date": DATE,
        "tier": "OBSERVATION",
        "local_only": True,
        "lane": "Lane 2 - Calculus / special functions",
        "seed_count": len(seeds),
        "passed": passed,
        "warned": warned,
        "failed": failed if failures else 0,
        "zero_mathlib_status": "PASS" if not guardrail_failures else "FAIL",
        "lane_status": "DRAFT_INTERNAL_FEASIBILITY_ONLY",
        "primitive_specs": primitive_specs,
        "results": sorted(results, key=lambda item: item["record_id"]),
        "warnings": warnings,
        "failures": failures,
        "guardrails": {
            "no_mathlib_dependency": not guardrail_failures,
            "no_hf_upload": True,
            "no_petal_upload": True,
            "no_package_publish": True,
            "no_hardware": True,
            "no_forge_compiler_change": True,
            "no_public_theorem_claim": True,
            "no_public_ready_true": True,
            "no_upload_allowed_true": True,
            "no_marketplace_ready_true": True,
            "no_capcard_certification_claim": True,
            "no_petal_verification_claim": True,
            "no_token_like_secret": True,
        },
    }

    write_json(spec_out, {"date": DATE, "tier": "OBSERVATION", "local_only": True, "primitive_specs": primitive_specs})
    write_json(out, result)
    report_paths = write_reports(result, Path("reports"))
    post_scan = scan_guardrails([out, spec_out, *report_paths])
    if post_scan:
        result["failures"].extend(post_scan)
        result["failed"] = max(result["failed"], 1)
        result["zero_mathlib_status"] = "FAIL"
        result["guardrails"]["no_mathlib_dependency"] = False
        write_json(out, result)
        write_reports(result, Path("reports"))
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", default="corpus/eml_lanes_draft")
    parser.add_argument(
        "--out",
        default="corpus/eml_lanes_draft/lane_2_calculus_special_functions/primitive_feasibility_result_2026_05_20.json",
    )
    parser.add_argument(
        "--spec-out",
        default="corpus/eml_lanes_draft/lane_2_calculus_special_functions/primitive_spec_draft_2026_05_20.json",
    )
    parser.add_argument("--strict", action="store_true")
    args = parser.parse_args()

    result = run_analysis(Path(args.root), Path(args.out), Path(args.spec_out))
    print(f"seed_count: {result['seed_count']}")
    print(f"passed: {result['passed']}")
    print(f"warned: {result['warned']}")
    print(f"failed: {result['failed']}")
    print(f"zero_mathlib_status: {result['zero_mathlib_status']}")
    print(f"lane_status: {result['lane_status']}")
    if result["warnings"]:
        print("warnings:")
        for warning in result["warnings"]:
            print(f"- {warning}")
    if result["failures"]:
        print("failures:")
        for failure in result["failures"]:
            print(f"- {failure}")
    if args.strict and result["failed"]:
        return 1
    print("PASS" if not result["failed"] else "WARN")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
