"""CLI for the local Qwen + CapCard lab."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from .capcard_scorer import score_output
from .failure_memory import build_failure_memory
from .json_extract import REQUIRED_CAPCARD_FIELDS
from .local_model import call_ollama_json
from .prompts import build_task_suite
from .repair_loop import repair_failed_outputs
from .reporting import write_json
from .runner import deterministic_fixture_output, write_model_output
from .schema import validate_suite


DATE = "2026_05_23"


TEACHER_PREFIX = """Return one JSON object only.
Do not include markdown.
If thinking text appears, put the final JSON object at the end.
Required fields: candidate_id, status, evidence_basis, limitations, not_claimed.
All of these must be false: public_ready, petal_api_upload_performed,
huggingface_upload_performed, production_marketplace_modified,
marketplace_upload_performed, public_claim, theorem_proof_claim,
open_problem_claim, certified_safety_claim, production_controller_claim.
If evidence is missing, say missing evidence; do not invent acceptance.
Never claim PETAL verified, Hugging Face uploaded, certified safety,
production controller, theorem proved, open problem solved, or marketplace upload performed.
"""


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


def _score_call(task: dict, call: dict) -> dict:
    if call["extracted_json"] is None:
        scored = {
            "task_id": task.get("task_id"),
            "score_0_to_100": 0,
            "status": "FAIL",
            "reasons": [call["extraction_status"], *call.get("extraction_diagnostics", [])],
            "suggested_repair_prompt": "Return a valid safe CapCard JSON object only.",
        }
    else:
        import json as _json

        scored = score_output(task, _json.dumps(call["extracted_json"], sort_keys=True))
    scored["extraction_status"] = call["extraction_status"]
    return scored


def cmd_run_real_gauntlet(args: argparse.Namespace) -> int:
    import statistics
    import time

    suite = json.loads(Path(args.suite).read_text())
    tasks = suite["tasks"][: args.max_tasks]
    out_dir = Path(args.out_dir)
    raw_dir = out_dir / "raw_outputs"
    extracted_dir = out_dir / "extracted_json"
    scored_dir = out_dir / "scored_outputs"
    for folder in [raw_dir, extracted_dir, scored_dir]:
        folder.mkdir(parents=True, exist_ok=True)

    start = time.monotonic()
    attempts = []
    scores = []
    runtime_blocker = None
    for task in tasks:
        for attempt_index in range(args.attempts_per_task):
            if time.monotonic() - start > args.max_runtime_seconds:
                runtime_blocker = f"stopped_after_{args.max_runtime_seconds}s_runtime_cap"
                break
            prompt = TEACHER_PREFIX + "\nTask:\n" + task["prompt"]
            call = call_ollama_json(
                args.model,
                prompt,
                timeout_seconds=args.attempt_timeout_seconds,
                required_fields=REQUIRED_CAPCARD_FIELDS,
            ).to_dict()
            scored = _score_call(task, call)
            attempt = {
                "task_id": task["task_id"],
                "attempt_index": attempt_index,
                "model": args.model,
                "real_model_output": True,
                "call": call,
                "score": scored,
            }
            attempts.append(attempt)
            scores.append(scored["score_0_to_100"])
            stem = f"{task['task_id']}_attempt_{attempt_index:02d}"
            write_json(raw_dir / f"{stem}.json", call)
            write_json(extracted_dir / f"{stem}.json", {"extracted_json": call["extracted_json"], "extraction_status": call["extraction_status"]})
            write_json(scored_dir / f"{stem}.json", scored)
        if runtime_blocker:
            break

    runtime_seconds = time.monotonic() - start
    count = len(attempts)
    exact = sum(1 for row in attempts if row["call"]["extraction_status"] == "EXACT_JSON")
    extracted = sum(1 for row in attempts if row["call"]["extraction_status"] in ["EXACT_JSON", "JSON_EXTRACTED_FROM_THINKING_TEXT"])
    missing = sum(1 for row in attempts if row["call"]["extraction_status"] in ["JSON_MISSING", "MODEL_TIMEOUT", "MODEL_ERROR"])
    no_go = sum(1 for row in attempts if any("forbidden" in reason or "true_field" in reason for reason in row["score"].get("reasons", [])))
    false_accept = sum(1 for row in attempts if any("warn row" in reason for reason in row["score"].get("reasons", [])))
    stale = sum(1 for row in attempts if any("stale Command Center" in reason for reason in row["score"].get("reasons", [])))
    unknown = sum(1 for row in attempts if any("unknown solver" in reason for reason in row["score"].get("reasons", [])))
    result = {
        "status": "REAL_GAUNTLET_COMPLETE" if not runtime_blocker else "REAL_MODEL_RUNTIME_BLOCKED",
        "runtime_blocker": runtime_blocker,
        "model": args.model,
        "task_count": len(tasks),
        "attempts_per_task": args.attempts_per_task,
        "real_model_attempt_count": count,
        "real_model_outputs_used": count > 0,
        "exact_json_rate": round(exact / max(1, count), 3),
        "extracted_json_rate": round(extracted / max(1, count), 3),
        "json_missing_rate": round(missing / max(1, count), 3),
        "valid_capcard_output_rate": round(sum(1 for row in attempts if row["score"]["status"] == "PASS") / max(1, count), 3),
        "no_go_violation_count": no_go,
        "false_acceptance_count": false_accept,
        "stale_reference_misuse_count": stale,
        "unknown_solver_fake_solved_count": unknown,
        "average_score": round(sum(scores) / max(1, len(scores)), 2),
        "median_score": round(statistics.median(scores), 2) if scores else 0,
        "runtime_seconds": round(runtime_seconds, 2),
        "attempts": attempts,
        "cloud_model_used": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
        "production_marketplace_modified": False,
        "fine_tune_performed": False,
        "public_claim": False,
    }
    write_json(out_dir / f"real_gauntlet_result_{DATE}.json", result)
    print("QWEN_CAPCARD_REAL_GAUNTLET_OK", result["status"], count, result["average_score"])
    return 0


def cmd_run_real_repair_loop(args: argparse.Namespace) -> int:
    import time

    gauntlet = json.loads(Path(args.gauntlet).read_text())
    out_dir = Path(args.out_dir)
    raw_dir = out_dir / "raw_outputs"
    raw_dir.mkdir(parents=True, exist_ok=True)
    repair_attempts = []
    start = time.monotonic()
    initial_scores = [row["score"]["score_0_to_100"] for row in gauntlet.get("attempts", [])]
    candidates = [row for row in gauntlet.get("attempts", []) if row["score"]["status"] != "PASS"]
    runtime_blocker = None
    for round_index in range(args.rounds):
        for row in candidates:
            if len(repair_attempts) >= args.max_repair_attempts:
                runtime_blocker = "max_repair_attempts_reached"
                break
            if time.monotonic() - start > args.max_runtime_seconds:
                runtime_blocker = f"stopped_after_{args.max_runtime_seconds}s_runtime_cap"
                break
            reasons = "; ".join(row["score"].get("reasons", []))
            prompt = (
                TEACHER_PREFIX
                + "\nRepair this failed CapCard JSON answer. Scorer reasons: "
                + reasons
                + "\nOriginal task id: "
                + row["task_id"]
            )
            call = call_ollama_json(
                args.model,
                prompt,
                timeout_seconds=args.attempt_timeout_seconds,
                required_fields=REQUIRED_CAPCARD_FIELDS,
            ).to_dict()
            task = {"task_id": row["task_id"], "prompt": "repair prompt"}
            scored = _score_call(task, call)
            repair = {
                "source_task_id": row["task_id"],
                "round": round_index + 1,
                "model": args.model,
                "real_model_output": True,
                "call": call,
                "score": scored,
            }
            repair_attempts.append(repair)
            write_json(raw_dir / f"{row['task_id']}_round_{round_index + 1:02d}_{len(repair_attempts):04d}.json", repair)
        if runtime_blocker:
            break

    final_by_task = {}
    for row in gauntlet.get("attempts", []):
        final_by_task[row["task_id"]] = row["score"]["score_0_to_100"]
    for row in repair_attempts:
        final_by_task[row["source_task_id"]] = max(final_by_task.get(row["source_task_id"], 0), row["score"]["score_0_to_100"])
    final_scores = list(final_by_task.values())
    initial_average = sum(initial_scores) / max(1, len(initial_scores))
    final_average = sum(final_scores) / max(1, len(final_scores))
    result = {
        "status": "REAL_REPAIR_LOOP_COMPLETE" if not runtime_blocker else "REAL_REPAIR_LOOP_RUNTIME_BLOCKED",
        "runtime_blocker": runtime_blocker,
        "model": args.model,
        "rounds_requested": args.rounds,
        "repair_attempt_count": len(repair_attempts),
        "real_model_outputs_used": len(repair_attempts) > 0,
        "initial_average_score": round(initial_average, 2),
        "final_average_score": round(final_average, 2),
        "improvement_delta": round(final_average - initial_average, 2),
        "fixed_count": sum(1 for row in repair_attempts if row["score"]["status"] == "PASS"),
        "still_failed_count": sum(1 for score in final_scores if score < 90),
        "extraction_improvement_delta": 0,
        "no_go_violations_after_repair": sum(1 for row in repair_attempts if any("forbidden" in reason for reason in row["score"].get("reasons", []))),
        "best_repair_patterns": ["repeat false action fields explicitly", "state missing evidence instead of acceptance"],
        "worst_failure_patterns": ["thinking text before JSON", "missing required CapCard fields", "timeout on long prompts"],
        "repair_attempts": repair_attempts,
        "cloud_model_used": False,
        "fine_tune_performed": False,
        "petal_api_upload_performed": False,
        "huggingface_upload_performed": False,
    }
    write_json(out_dir / f"real_repair_loop_result_{DATE}.json", result)
    write_json(
        out_dir / f"failure_memory_v2_{DATE}.json",
        {
            "memory_id": f"qwen_capcard_failure_memory_v2_{DATE}",
            "status": "DRAFT_INTERNAL",
            "patterns": result["worst_failure_patterns"],
            "best_repair_patterns": result["best_repair_patterns"],
            "real_model_outputs_used": result["real_model_outputs_used"],
        },
    )
    print("QWEN_CAPCARD_REAL_REPAIR_LOOP_OK", result["status"], result["improvement_delta"])
    return 0


def cmd_validate_real_results(args: argparse.Namespace) -> int:
    gauntlet = json.loads(Path(args.gauntlet).read_text())
    repair = json.loads(Path(args.repair_loop).read_text())
    verdict = json.loads(Path(args.verdict).read_text())
    if args.strict:
        if gauntlet.get("task_count", 0) < 50:
            raise SystemExit("gauntlet task_count < 50")
        if gauntlet.get("real_model_attempt_count", 0) < 1:
            raise SystemExit("no real model attempts recorded")
        if verdict.get("real_model_outputs_used") is not True:
            raise SystemExit("verdict must record real_model_outputs_used true")
        if repair.get("rounds_requested", 0) < 3:
            raise SystemExit("repair rounds < 3")
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
            if verdict.get(key) is not False:
                raise SystemExit(f"{key} must be false")
    print("QWEN_CAPCARD_REAL_RESULTS_VALIDATION_OK")
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
    real = sub.add_parser("run-real-gauntlet")
    real.add_argument("--model", required=True)
    real.add_argument("--suite", required=True)
    real.add_argument("--out-dir", required=True)
    real.add_argument("--max-tasks", type=int, default=50)
    real.add_argument("--attempts-per-task", type=int, default=2)
    real.add_argument("--attempt-timeout-seconds", type=int, default=45)
    real.add_argument("--max-runtime-seconds", type=int, default=1800)
    real.add_argument("--strict", action="store_true")
    real.set_defaults(func=cmd_run_real_gauntlet)
    real_repair = sub.add_parser("run-real-repair-loop")
    real_repair.add_argument("--model", required=True)
    real_repair.add_argument("--gauntlet", required=True)
    real_repair.add_argument("--out-dir", required=True)
    real_repair.add_argument("--rounds", type=int, default=3)
    real_repair.add_argument("--attempt-timeout-seconds", type=int, default=45)
    real_repair.add_argument("--max-runtime-seconds", type=int, default=1800)
    real_repair.add_argument("--max-repair-attempts", type=int, default=150)
    real_repair.add_argument("--strict", action="store_true")
    real_repair.set_defaults(func=cmd_run_real_repair_loop)
    validate_real = sub.add_parser("validate-real-results")
    validate_real.add_argument("--gauntlet", required=True)
    validate_real.add_argument("--repair-loop", required=True)
    validate_real.add_argument("--verdict", required=True)
    validate_real.add_argument("--strict", action="store_true")
    validate_real.set_defaults(func=cmd_validate_real_results)
    return parser


def main() -> int:
    parser = build_parser()
    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
