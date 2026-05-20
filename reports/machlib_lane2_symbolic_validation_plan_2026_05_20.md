# MachLib Lane 2 symbolic validation plan

Date: 2026-05-20

Lane 2 validation remains symbolic until MachLib-owned primitives exist.

## Validation without external formal libraries
- Parse all seed and primitive-spec JSON.
- Check every seed remains `DRAFT_INTERNAL`.
- Check guarded symbolic rewrite annotations only.
- Check domain guard annotations are explicit.
- Check no public theorem/proof or real-analysis completeness claim is present.
- Check all upload, public-ready, hardware, and compiler-change booleans remain false.
- Run the zero-dependency release gate before and after adding future primitives.

## Future primitive design
- Add owned symbolic syntax for exp/log/sin/cos/pow/sqrt.
- Add domain guard records before enabling rewrites.
- Add evidence rows that distinguish symbolic placeholders from verified artifacts.

## Future executable harness
- Once primitives exist, add local rewrite tests for guarded expressions.
- Keep exact symbolic checks separate from numeric smoke checks.
- Keep upload and publish gates closed.
