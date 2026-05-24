# Qwen CapCard Structured Capability Verdict

- Models tested: qwen3:30b, qwen3-coder:30b.
- Best model/runtime: `qwen3:30b` / `api_schema_format_think_false`.
- Real attempts: 300 across 50 tasks.
- Structured output unlocked: False.
- Gauntlet average score: 48.35; repair-loop final score: 100.0; delta: 51.65.
- Per-model rollup: `[{"attempts": 150, "average_score": 96.7, "model": "qwen3:30b", "runtime_mode": "api_schema_format_think_false", "schema_valid_rate": 1.0}, {"attempts": 150, "average_score": 0.0, "model": "qwen3-coder:30b", "runtime_mode": "cli_think_false", "schema_valid_rate": 0.0}]`.
- Blunt answer: structured output unlocked `qwen3:30b` for CapCard-style local work; `qwen3-coder:30b` did not beat it in this run because the selected CLI no-think mode produced invalid structured outputs.
- Qwen Puzzle rows 2/3 remain ready for human repair review, not marketplace-ready.
- No fine-tuning, cloud model, PETAL/API upload, Hugging Face upload, production marketplace modification, public theorem/proof/open-problem claim, certified safety claim, or production controller claim.
