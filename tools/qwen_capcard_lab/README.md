# Qwen CapCard Lab

Local-only closed-loop lab for using CapCard scoring as an evaluator, repair coach, and evidence memory for Qwen-family model outputs.

This package does not fine-tune, upload datasets, call PETAL/API, upload to Hugging Face, modify production CapCard marketplace assets, publish packages, deploy, or create public theorem/proof/open-problem claims.

The default generated checkpoint is honest about dry-run scorer fixtures. Real local model execution can be added through the Ollama runner, but dry-run outputs are never labeled as real model answers.
