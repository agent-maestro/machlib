# Contributing to MachLib

> One-page guide to submitting records. The longer guide with
> examples and verification details is at
> `docs/for-contributors/submission_guide.md`.

## What we accept

  - **New theorem-proof records** for any of the seven supported
    domains (`eml`, `analysis`, `algebra`, `chemistry`,
    `physics`, `finance`, `engineering`).
  - **New proofs of existing theorems**, especially if they are
    shorter than the current optimal, or use a proof style not
    yet represented for that theorem.
  - **Failure data** — annotated tactic-failure traces from agent
    attempts, suitable for the `common_mistakes` field.

## Submission steps

1. **Write the theorem** as a Lean 4 declaration importing only
   `MachLib.*` (no Mathlib).
2. **Prove it.** Multiple proofs are welcome.
3. **Format the record** to match `SCHEMA.md`. The `machlib
   format` CLI helper does most of the work; you fill in the
   informal description, tags, and any failure data.
4. **Self-verify** with `machlib verify <record.json>`. The CLI
   runs schema validation and kernel re-verification on the
   pinned toolchain.
5. **Submit.** Either:
   - Open a PR adding the JSON file under
     `corpus/<domain>/lane<N>/<id>.json`, or
   - POST to `https://api.machlib.org/submit` with the JSON body.

## What happens after submission

The verification pipeline runs the same kernel re-verification
the CLI does, plus a duplicate check against the existing corpus.
Successful submissions are merged. The `discovered_by` field is
preserved as written; you receive credit in the metadata.

## Quality gate

Before merging we require:

  - [x] `verified: true` reflects a green kernel run on CI's
        pinned Lean toolchain.
  - [x] Every field in `SCHEMA.md` is present (or `null` where
        the schema permits).
  - [x] No duplicate of an existing record (by `theorem.id` or by
        identical formal statement modulo alpha-renaming).
  - [x] If the record carries `chain_order`, the value is
        reproducible from `eml-cost analyze` on the formal source.

## Licensing

By submitting a record you agree to license it under
[CC BY 4.0](LICENSE). You retain authorship credit via
`metadata.discovered_by`.

## Code of conduct

Contributions are evaluated on the merits of the record.
Identity, affiliation, and provenance (human or agent) are
recorded in metadata but do not affect merging decisions. Bug
reports and corrections are merged on the same basis.
