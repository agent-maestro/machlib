# MachLib — for machines, by machines

[![cold build](https://img.shields.io/endpoint?url=https://raw.githubusercontent.com/agent-maestro/machlib/master/.github/build-time.json)](.github/workflows/build-time.yml)

A self-contained formal mathematics library built for machine
consumption. Independent foundations. Multi-proof corpus. Verified
by the Lean 4 kernel.

## Install

```bash
pip install machlib
```

## Try it

```python
from machlib import load

ds = load("machlib-eml-1k")
print(ds[0]["theorem"]["statement"]["informal"])
# eml(x, 1) equals exp(x) for all real x

print(len(ds[0]["proofs"]))  # 2 — multiple ranked proofs per theorem
```

## What's here

| | |
|---|---|
| `foundations/` | Independent Lean 4 foundations — ~3,400 lines, zero Mathlib |
| `corpus/` | 1K+ verified theorem-proof records with full metadata |
| `gym/` | Gymnasium-compatible training environment, 54-tactic vocabulary |
| `tools/` | Generator, verifier, ranker, exporter, CLI |
| `api/` | REST API for theorems, proofs, tactics, search |
| `docs/` | Audience-organised guides + reference |

## Why MachLib (not Mathlib)

Mathlib is the cathedral, by humans, for humans.
MachLib is the training gym, for machines, by machines.
You don't train for a marathon inside a cathedral.

See [PHILOSOPHY.md](PHILOSOPHY.md) for the full case.

## Status

Seed phase. 256 records, foundations built on Mathlib (transitional).
Phase 1 (independence) and Phase 2 (1K records) in progress.

## License

[CC BY 4.0](LICENSE) — open, citable, usable by anyone.
