# Qwen CapCard Model Selection

- Preferred primary: `qwen3-coder:30b`.
- Pull attempted: `ollama pull qwen3-coder:30b`.
- Result: blocked by transfer speed/ETA, then stopped to avoid a multi-hour install in this task.
- Selected primary for this checkpoint: already-installed local `qwen3:30b`.
- Important honesty note: bakeoff artifacts in this checkpoint are scorer-only dry-run fixtures, not real Qwen outputs.
- Local `qwen3:30b` smoke probe: callable, but raw CLI output included thinking text before JSON; strict JSON controls are required before real bakeoff scoring.
