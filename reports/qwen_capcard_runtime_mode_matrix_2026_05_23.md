# Qwen CapCard Runtime Mode Matrix

Local Ollama runtime matrix for QWEN-CAPCARD-004.

| model | mode | available | schema rate | average score | no-go count | median latency |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| qwen3:30b | api_schema_format_think_false | True | 1.0 | 82.5 | 1 | 4.89s |
| qwen3:30b | api_schema_format | True | 0.0 | 0.0 | 0 | 2.49s |
| qwen3:30b | cli_think_false | True | 0.0 | 0.0 | 0 | 30.008s |
| qwen3:30b | cli_hide_thinking | True | 0.0 | 0.0 | 0 | 18.25s |
| qwen3-coder:30b | api_schema_format_think_false | True | 1.0 | 82.5 | 1 | 5.315s |
| qwen3-coder:30b | api_schema_format | True | 1.0 | 82.5 | 1 | 2.506s |
| qwen3-coder:30b | cli_think_false | True | 0.5 | 50.0 | 0 | 2.453s |
| qwen3-coder:30b | cli_hide_thinking | True | 0.0 | 0.0 | 0 | 2.639s |

Result: qwen3-coder:30b API/schema was tested directly. It starts and produces schema JSON, but the conservative default remains qwen3:30b api_schema_format_think_false until coder clears adversarial thresholds cleanly.

No cloud model, upload, fine-tune, package publish, deploy, hardware action, or public claim was performed.
