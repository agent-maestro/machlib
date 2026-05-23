# Qwen CapCard Local Runtime Inventory

Date: 2026-05-23

- Ollama available: yes (`/usr/local/bin/ollama`, version 0.23.2).
- Installed Qwen-family model: `qwen3:30b` (18 GB).
- `llama-cli`, `llama-server`, and `vllm`: not found in PATH during this inspection.
- GPU: NVIDIA GB10 visible; VRAM reporting was not supported in the displayed `nvidia-smi` table.
- RAM/disk: 121 GiB RAM total, about 2.8T free on the repo filesystem at inspection.
- Boundary: no cloud model, no fine-tune, no PETAL/API upload, no Hugging Face upload.
- Local `qwen3:30b` smoke probe: callable, but raw CLI output included thinking text before JSON; strict JSON controls are required before real bakeoff scoring.
