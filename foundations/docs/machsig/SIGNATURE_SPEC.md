# MachSig/v0.1 — Signature Specification

Two layers, not three. The canonical layer is **explicitly unavailable**, not silently filled.

```
MachSig/v0.1
Object: MachLib.decayFloorUpTo_three   [theorem]   MachLib.EMLDepth3Rung

  StatementSig       N11-D4-C4-I0-E0-A0
  ProofSig           AX40-PD45-V51-S0
  CanonicalSig       UNAVAILABLE
  StatementDigest    fec52a6402faa5ffd792f129f3f515cb…
  ProofFingerprint   2439174189  (64-bit, non-cryptographic)
```

## StatementSig fields

| abbr | field | range in corpus | distinct |
|---|---|---|---:|
| `N` | `statement_expr_node_count` | 1 – 15,501 | 538 |
| `D` | `statement_expr_depth` | 0 – 78 | 60 |
| `C` | `distinct_constant_reference_count` | 1 – 76 | 57 |
| `I` | `implication_count` | 0 – 66 | 32 |
| `E` | `equality_head_count` | 0 – 98 | 13 |
| `A` | `conjunction_count` | 0 – 26 | 14 |

## ProofSig fields

| abbr | field | note |
|---|---|---|
| `AX` | `axiom_dependency_count` | transitive kernel footprint via `Lean.collectAxioms` — the field with real trust weight |
| `PD` | `proof_approx_depth` | proof-term depth |
| `V` | `value_direct_const_count` | **direct** constant references in the proof term, not a transitive closure |
| `S` | `depends_on_sorry` | 0/1 |

## Two candidates deliberately excluded

`disjunction_count` (5 distinct values, median 0) and `existential_count` (9, median 0) were
classified `DEGENERATE` in `STABILITY_REPORT.md` and are **not** in the signature. Including them
would lengthen every signature to carry almost no information. Field selection came from the
census, not from what looked natural to write down.

## Signature vs digest — the separation is deliberate

`StatementSig` is **interpretable but not identifying**: 5,041 distinct values across 7,569
theorems, with a largest collision class of 48. `StatementDigest` is the identity layer — SHA-256
over the structural encoding of the stored `Expr`.

Reading a signature tells you the shape of a claim. Comparing digests tells you whether the
representation is the same. Conflating them would mean either an unreadable signature or a digest
that cannot detect change, and the roadmap's Phase 4 asks for both properties at once.

## What the digests do and do not answer

`StatementDigest` answers **"did the kernel-facing statement representation change?"** It does not
answer "are these two statements mathematically equivalent." Binder names and `mdata` are dropped,
so α-renaming does not move it; two provably equivalent statements with different stored types get
different digests, and that is correct for a representation digest.

`ProofFingerprint64` is Lean's cached structural `Expr` hash. It is a 64-bit **non-cryptographic**
fingerprint — adequate to detect that one declaration's proof changed between commits, and named so
it cannot be mistaken for a digest.

**`StatementDigest` is meaningless for non-theorems** and the CLI says so per object: a `def`'s
"statement" is a bare type signature shared by many declarations.

## Worked pairs

**Proof refactor** — same claim, same trust, different proof:

```
decayFloorUpTo_three           N11-D4-C4-I0-E0-A0   AX40-PD45-V51-S0
decayFloorUpTo_three_via_step  N11-D4-C4-I0-E0-A0   AX40-PD8-V7-S0
```

**Trust-surface difference** — same claim, materially different footprint:

```
Real.mul_left_comm   N77-D12-C5-I0-E3-A0   AX4-PD21-V12-S0
Real.ea_mulswap3     N77-D12-C5-I0-E3-A0   AX19-PD59-V49-S0
```

That second pair is MachSig's most useful output today: two proofs of one statement, one resting on
four axioms and the other on nineteen.

## v0.3 (2026-10-13) — the axiom SET, and where a signature set came from

Two additions, both forced by the trust gate going blind (2026-09-03 to 2026-10-13, see
`TRANSITION_2026-10-13.md`). Nothing above changes value: `StatementSig`, `ProofSig`, `TrustSig`
and both digests are computed exactly as before, which the transition report measures (zero
extractor-caused differences at either revision).

**`TrustAxioms`** — the sorted list of axiom names behind `TrustSig`'s `AX` count, from the same
`Lean.collectAxioms` call (`extract.lean`'s 12th column). `None` exactly when `AX` is `?`. A count
cannot say which axiom entered a footprint and cannot see a swap (one out, another in); the gate now
compares sets.

**The provenance record** — the first line of `artifacts/machsig_signatures.jsonl`:

```
{"kind": "machsig-provenance", "schema": "machsig-provenance/v1", "version": "MachSig/v0.3",
 "machlib_commit": ..., "machlib_sources": "sha256:...",   # Forge's commit-based digest
 "content_digest": "sha256:...", "content_files": {...},   # the bytes Lean read: the staleness key
 "extractor_digest": "sha256:...", "extractor_files": {...},
 "lean_toolchain": ..., "lean_version": ..., "sources_clean": ..., "dirty_source_paths": [...],
 "raw": {"machsig_stmt_raw.tsv": sha256, "machsig_raw.tsv": sha256},
 "records": N, "records_sha256": "sha256:..."}              # over the bytes after this line
```

Only `tools/machsig/regen.py` produces a set `sig.py` will write: it builds, runs both extractors,
refuses if the tree moved while Lean ran, and binds the raw files to the identity. `sig.py` refuses
raw files it cannot bind, a census built from other raw files, and malformed or truncated rows (all
three were skipped silently before v0.3 — and a skipped theorem reads downstream as a *removal*,
which the gate reports as INFO). Consumers skip the record: it has no `object`.

```
python3 tools/machsig/regen.py        # the only supported way to (re)generate signatures
```

## CLI

```
python3 tools/machsig/sig.py inspect <object-name>   # short or fully-qualified
python3 tools/machsig/sig.py sigs                    # whole corpus -> machsig_signatures.jsonl
```

## MachDiff

```
python3 tools/machsig/diff.py <objectA> <objectB> [--json]
python3 tools/machsig/diff.py --snapshot A.jsonl B.jsonl
```

Classification is decided by which layer moved, and nothing is inferred past that:

| StatementDigest | ProofFingerprint | axioms | classification |
|---|---|---|---|
| SAME | SAME | — | `IDENTICAL_REPRESENTATION` |
| SAME | CHANGED | SAME | `PROOF_REFACTOR` |
| SAME | CHANGED | CHANGED | `TRUST_SURFACE_CHANGE` |
| CHANGED | — | — | `STATEMENT_CHANGED` |

### The fifth state cannot be emitted, and MachDiff says so

The roadmap's high-priority case — *source SAME, canonical CHANGED* — **is unreachable here**,
because this corpus has no canonical view (`CANONICALIZER_BRIDGE.md`). MachDiff therefore prints
`CANONICAL UNAVAILABLE` on every comparison rather than carrying a branch that silently never fires.

A category that can never trigger is worse than an absent one: a green result implies a check ran.
