# Qwen CapCard Model Recommendation

- Default now: `qwen3:30b` through Ollama API JSON Schema mode with `think=false`.
- Do not make `qwen3-coder:30b` the default yet; it needs a separate API/schema prompt pass because its probe-selected CLI mode failed the full gauntlet.
- Fine-tuning is not worth doing yet. First lock down structured output and repair prompts with the local API path.
