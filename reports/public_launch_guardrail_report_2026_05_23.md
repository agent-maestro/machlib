# Public Launch Guardrail Report - 2026-05-23

## Result

PASS for recordkeeping boundaries.

## Confirmed public/live

- 1op Senses at `https://1op.io/senses`
- Operator Senses inside `/senses`
- machlib `0.0.1` on PyPI

## Confirmed private/internal

- CapCard Lab Workbench
- EML Puzzle Evidence Kernel CapCard
- Qwen repair workbench
- CapCard mutation, scoring, and reviewer internals

## No-go status

| Boundary | Status |
| --- | --- |
| Deploy performed by this task | false |
| Push performed by this task | false |
| Token handling performed | false |
| Package publish performed by this task | false |
| PETAL/API upload performed | false |
| Hugging Face upload performed | false |
| Production CapCard marketplace modified | false |
| CapCard Lab exposed publicly | false |
| EML Puzzle CapCard exposed publicly | false |
| Unsupported theorem claim introduced by this task | false |

## Footer claim guardrail

The existing public 1op footer includes a theorem-count phrase that is not yet supported by a clear source in this audit. Cleanup is recommended before relying on that claim as public product copy.
