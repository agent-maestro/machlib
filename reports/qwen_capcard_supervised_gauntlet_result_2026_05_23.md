# Qwen CapCard Supervised Gauntlet Result

Status: SUPERVISED_GAUNTLET_COMPLETE.

Real local model attempts: 600.
Tasks: 100 normal + 100 adversarial.
Model usage: {'qwen3:30b': 600}.
Runtime mode usage: {'api_schema_format_think_false': 600}.
Schema JSON rate: 1.0.
Valid CapCard output rate: 1.0.
Average initial score: 96.67.
Average final score: 96.67.
Improvement delta: 0.
No-go violation count: 19.
False acceptance count: 0.
Unknown solver fake-solved count: 0.
Timeout count: 0.

Interpretation: the supervisor made local Qwen useful as a schema-bound CapCard assistant, but adversarial forbidden-field failures remain and must stay in the teacher memory.
