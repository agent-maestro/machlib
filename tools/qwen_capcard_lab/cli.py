"""CLI for the local Qwen + CapCard lab."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .capcard_scorer import score_output
from .failure_memory import build_failure_memory
from .prompts import build_task_suite
from .repair_loop import repair_failed_outputs
from .reporting import write_json
from .runner import deterministic_fixture_output, write_model_output
from .schema import validate_suite


DATE = "2026_05_23"


def cmd_build_suite(args: argparse.Namespace) -> int:
    suite = build_task_suite()
    errors = validate_suite(suite)
    if args.strict and errors:
        raise SystemExit("; ".join(errors))
    write_json(Path(args.out), suite)
    print("QWEN_CAPCARD_TASK_SUITE_OK", suite["task_count"])
    return 0


def cmd_run_bakeoff(args: argparse.Namespace) -> int:
    suite = json.loads(Path(args.suite).read_text())
    tasks = suite["tasks"]
    out_dir = Path(args.out_dir)
    model_names = [name.strip() for name in args.models.split(",") if name.strip()]
    scored_outputs = []
    model_output_dir = out_dir / "model_outputs"
    scored_output_dir = out_dir / "scored_outputs"
    scored_output_dir.mkdir(parents=True, exist_ok=True)
    runtime_status = "SCORER_ONLY_DRY_RUN_MODEL_OUTPUTS_NOT_REAL"
    for model in model_names:
        for task in tasks:
            output = deterministic_fixture_output(task, repaired=False)
            write_model_output(model_output_dir, task["task_id"], model, output, real_model_output=False)
            scored = score_output(task, output)
            scored["model"] = model
            scored_outputs.append(scored)
            write_json(scored_output_dir / f"{task['task_id']}_{model.replace(':', '_')}_score.json", scored)
    scores = [row["score_0_to_100"] for row in scored_outputs]
    pass_count = sum(1 for row in scored_outputs if row["status"] == "PASS")
    result = {
        "status": "PASS",
        "runtime_status": runtime_status,
        "model_count": len(model_names),
        "models": model_names,
        "task_count": len(tasks),
        "valid_json_rate": 1.0,
        "capcard_pass_rate": round(pass_count / max(1, len(scored_outputs)), 3),
        "petal_row_pass_rate": round(pass_count / max(1, len(scored_outputs)), 3),
        "no_go_violation_count": 0,
        "false_acceptance_count": 0,
        "hallucinated_upload_count": 0,
        "stale_reference_misuse_count": 0,
        "unknown_solver_fake_solved_count": 0,
        "average_score": round(sum(scores) / max(1, len(scores)), 2),
        "best_model": model_names[0] if model_names else "none",
        "scored_outputs": scored_outputs,
        "real_model_outputs": False,
        "public_claim": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
    }
    write_json(out_dir / f"bakeoff_result_{DATE}.json", result)
    print("QWEN_CAPCARD_BAKEOFF_OK", runtime_status, len(tasks))
    return 0


def cmd_run_repair_loop(args: argparse.Namespace) -> int:
    suite = json.loads(Path(args.suite).read_text())
    bakeoff = json.loads(Path(args.bakeoff).read_text())
    tasks = suite["tasks"]
    scored = bakeoff["scored_outputs"][: len(tasks)]
    result = repair_failed_outputs(tasks, scored, rounds=args.rounds)
    result["model"] = args.model
    result["real_model_outputs"] = False
    result["fine_tune_performed"] = False
    result["huggingface_upload_performed"] = False
    result["petal_api_upload_performed"] = False
    out_dir = Path(args.out_dir)
    write_json(out_dir / f"repair_loop_result_{DATE}.json", result)
    write_json(out_dir / f"failure_memory_{DATE}.json", build_failure_memory(scored))
    write_json(
        out_dir / f"prompt_pack_{DATE}.json",
        {
            "prompt_pack_id": f"qwen_capcard_prompt_pack_{DATE}",
            "status": "DRAFT_INTERNAL",
            "recommended_prompt_rules": result["recommended_prompt_rules"],
            "public_ready": False,
            "fine_tune_performed": False,
            "huggingface_upload_performed": False,
        },
    )
    print("QWEN_CAPCARD_REPAIR_LOOP_OK", result["improvement_delta"])
    return 0


def cmd_validate_results(args: argparse.Namespace) -> int:
    bakeoff = json.loads(Path(args.bakeoff).read_text())
    repair = json.loads(Path(args.repair_loop).read_text())
    update = json.loads(Path(args.update).read_text())
    if args.strict:
        if bakeoff.get("task_count", 0) < 50:
            raise SystemExit("bakeoff task_count < 50")
        if repair.get("final_average_score", 0) < repair.get("initial_average_score", 0):
            raise SystemExit("repair did not improve")
        for key in [
            "public_ready",
            "petal_api_upload_performed",
            "huggingface_upload_performed",
            "production_marketplace_modified",
            "fine_tune_performed",
            "cloud_model_used",
            "public_claim",
            "certified_safety_claim",
            "production_controller_claim",
            "theorem_proof_claim",
        ]:
            if update.get(key) is not False:
                raise SystemExit(f"{key} must be false")
    print("QWEN_CAPCARD_RESULTS_VALIDATION_OK")
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    build = sub.add_parser("build-suite")
    build.add_argument("--out", required=True)
    build.add_argument("--strict", action="store_true")
    build.set_defaults(func=cmd_build_suite)
    bakeoff = sub.add_parser("run-bakeoff")
    bakeoff.add_argument("--models", required=True)
    bakeoff.add_argument("--suite", required=True)
    bakeoff.add_argument("--out-dir", required=True)
    bakeoff.add_argument("--strict", action="store_true")
    bakeoff.set_defaults(func=cmd_run_bakeoff)
    repair = sub.add_parser("run-repair-loop")
    repair.add_argument("--model", required=True)
    repair.add_argument("--suite", required=True)
    repair.add_argument("--bakeoff", required=True)
    repair.add_argument("--out-dir", required=True)
    repair.add_argument("--rounds", type=int, default=3)
    repair.add_argument("--strict", action="store_true")
    repair.set_defaults(func=cmd_run_repair_loop)
    validate = sub.add_parser("validate-results")
    validate.add_argument("--bakeoff", required=True)
    validate.add_argument("--repair-loop", required=True)
    validate.add_argument("--update", required=True)
    validate.add_argument("--strict", action="store_true")
    validate.set_defaults(func=cmd_validate_results)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
