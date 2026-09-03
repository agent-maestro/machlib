# MachSig Phase 2A — Statement Census

`MachSig-statement/v0.1` · extractor `tools/machsig/extract_statement.lean` · driver
`tools/machsig/statement.py`

## Population, reported in full

| stage | count |
|---|---:|
| raw eligible (`MachLib.*` + `Certcom.*`, non-internal) | **14,390** |
| compiler-generated exclusions (`.match_`, `.eq_def`, …) | **3,617** |
| analyzed | **10,773** |
| of which theorems (where the digest is meaningful) | **7,569** |

The exclusion policy is explicit and reported at every run, so a future Lean version changing what
it generates cannot silently move the population. Phase 1's figure of 13,486 was **both** too narrow
(`MachLib`-only, excluding `Certcom`) and too broad (no generated filter).

## Scope declaration

The extractor declares its namespace scope in its own output (`STMT_SCOPE`). This exists because the
`MachLib` / `Certcom` boundary has now caused three separate defects: the 220/243 axiom discrepancy,
Phase 1's census excluding the Forge grammar, and a false-absence probe reporting `elet = 0`.

## StatementDigest — what is and is not serialized

SHA-256 over a structural encoding of the **stored Lean type**:

* **kept** — constructor shape, constant names, de Bruijn indices, literals
* **dropped** — binder *names*, `mdata`

Dropping binder names means α-renaming does not move the digest. Dropping `mdata` means elaboration
annotations do not either.

It answers **"did the kernel-facing statement representation change?"** It does **not** answer "are
these two statements mathematically equivalent" — two provably equivalent statements with different
stored types get different digests, and that is correct behaviour for a representation digest.

**It is meaningless for `def`s**, whose "statement" is a bare type signature shared by many
declarations. All grouping analysis is restricted to theorems for that reason.

## Proof side

`proof_expr_fp64` is Lean's cached structural `Expr` hash of the proof term, with `proof_approx_depth`
alongside. This is a **64-bit non-cryptographic fingerprint** — sufficient to detect that one
declaration's proof changed between commits, and deliberately not called a digest. Full proof
serialization was tried and abandoned as too expensive.

`ConstantInfo.value?` returns `none` for theorems in Lean v4.32.2; the extractor destructures
`.thmInfo v` explicitly. Without that, every proof feature is silently empty.

## Determinism

`artifacts/machsig_stability_cases.jsonl` is byte-identical across runs
(`sha256 5f305bf959890228…`), 225 records.
