"""Phase 2 corpus generation — run the 5 base strategies against
the imported PETAL records, write each candidate variant out as a
MachLib v1.0.0 record.

Verification is deferred: candidates are written with
`metadata.verified = false` and an explanatory note. The Phase 1
foundations are independent of Mathlib but the legacy proof
templates carried over from PETAL still reference Mathlib idioms;
Phase 1.5 (porting the 50 monogate-lean theorems to MachLib
foundations) is a prerequisite for kernel re-verification.
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

# Allow running both as a module and as a script.
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from tools.generator.strategies import (  # type: ignore  # noqa: E402
    EMLTheoremGenerator,
)


PHASE2_VARIANT_COUNTS: dict[str, int] = {
    "constant_swap": 10,
    "domain_change": 5,
    "operator_swap": 8,
    "composition_depth": 5,
    "negation": 3,
}


_LANE_DIRS = {
    1: "lane1_foundations",
    2: "lane2_lower_bounds",
    3: "lane3_advanced",
    4: "lane4_expert",
    5: "lane5_open_problems",
    6: "lane6_cross_domain",
}

_STRATEGY_DIRS = {
    "constant_swap": "constant_swap",
    "domain_change": "domain_change",
    "operator_swap": "operator_swap",
    "composition_depth": "composition_depth",
    "negation": "negation",
}


def _load_petal_records(seed_path: Path) -> list[dict]:
    """Load the original PETAL seed JSON (still in PETAL schema)
    so the generator's templates can match its field names."""
    return json.loads(seed_path.read_text(encoding="utf-8"))["records"]


def _to_machlib_record(
    variant: dict[str, Any],
    parent_petal: dict[str, Any],
) -> dict[str, Any]:
    """Convert a `GeneratedVariant.to_dict()` payload into a
    MachLib v1.0.0 record."""
    informal = variant.get("natural_language", "")
    formal = variant.get("statement_lean4", "")
    proof = variant.get("proof_lean4", "")
    parent_lane = int(parent_petal.get("lane", 1))
    return {
        "schema_version": "1.0.0",
        "theorem": {
            "id": variant["theorem_id"],
            "base_id": variant["base_theorem_id"],
            "variant_strategy": variant["strategy"],
            "statement": {
                "informal": informal,
                "formal_lean": formal,
                "formal_eml_lang": None,
            },
            "domain": "eml",
            "lane": parent_lane,
            "tags": [variant["strategy"], "generated", "lane-%d" % parent_lane],
        },
        "proofs": [
            {
                "id": "p1",
                "tactics": [proof] if proof else [],
                "tactic_count": 1 if proof else 0,
                "eml_node_cost": 0,
                "style": "definitional",
                "is_optimal": True,
                "discovered_by": "machlib_generator_v1",
                "discovery_date": "2026-04-30",
            }
        ],
        "difficulty": {
            "lane": parent_lane,
            "label": (
                ["beginner", "beginner", "intermediate", "advanced",
                 "expert", "advanced"][parent_lane - 1]
            ),
            "calibrated_from_attempts": 0,
            "average_hint_level_at_solve": 0.0,
            "prerequisite_skills": [],
        },
        "common_mistakes": [],
        "tactic_trace": {
            "successful": {},
            "failed": {},
            "success_rate_by_tactic": {},
        },
        "structural_profile": {
            "chain_order": None,
            "cost_class": None,
            "eml_depth": None,
            "dynamics": {"oscillations": 0, "decays": 0},
            "drift_risk": "LOW",
            "fpga_estimate": None,
        },
        "relationships": {
            "parent": variant["base_theorem_id"],
            "siblings": [],
            "depends_on": [],
            "structural_siblings": [],
        },
        "metadata": {
            "verified": False,
            "verification_method": None,
            "verification_pending": (
                "Phase 1.5 — port legacy theorems to MachLib foundations "
                "before kernel re-verification."
            ),
            "generated_by": "machlib_generator_v1",
            "creation_date": "2026-04-30",
        },
    }


def add_arguments(ap: argparse.ArgumentParser) -> None:
    ap.add_argument(
        "--petal-seed",
        default="D:/monogate-research/petal/seed_v1/data/petal_eml.json",
        help="PETAL seed JSON (the generator's templates need PETAL schema).",
    )
    ap.add_argument(
        "--out",
        default="corpus/eml/generated",
        help="Output root for generated variants.",
    )
    ap.add_argument(
        "--strategy",
        default=None,
        choices=tuple(PHASE2_VARIANT_COUNTS),
        help="Run only one strategy (default: all five).",
    )
    ap.add_argument(
        "--limit",
        type=int,
        default=None,
        help="Cap total written variants (across all strategies).",
    )


def run(args: argparse.Namespace) -> int:

    petal_records = _load_petal_records(Path(args.petal_seed))

    counts = (
        {args.strategy: PHASE2_VARIANT_COUNTS[args.strategy]}
        if args.strategy
        else PHASE2_VARIANT_COUNTS
    )

    gen = EMLTheoremGenerator(
        petal_records,
        variants_per_strategy=counts,
        seed=1,
    )
    out_root = Path(args.out)

    by_strategy: dict[str, int] = {}
    by_petal: dict[str, dict] = {r["theorem_id"]: r for r in petal_records}

    written = 0
    for variant in gen.generate_all():
        if args.limit is not None and written >= args.limit:
            break
        v_dict = variant.to_dict()
        parent = by_petal.get(v_dict["base_theorem_id"], {})
        record = _to_machlib_record(v_dict, parent)
        strategy = v_dict["strategy"]
        sub_dir = out_root / _STRATEGY_DIRS[strategy]
        sub_dir.mkdir(parents=True, exist_ok=True)
        target = sub_dir / f"{record['theorem']['id']}.json"
        target.write_text(
            json.dumps(record, indent=2, ensure_ascii=False),
            encoding="utf-8",
        )
        by_strategy[strategy] = by_strategy.get(strategy, 0) + 1
        written += 1
        if args.limit is not None:
            print(f"  + {record['theorem']['id']}")

    total = sum(by_strategy.values())
    print(f"wrote {total} variants:")
    for k, v in sorted(by_strategy.items()):
        print(f"  {k:20s} {v}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    add_arguments(ap)
    return run(ap.parse_args())


if __name__ == "__main__":
    sys.exit(main())
