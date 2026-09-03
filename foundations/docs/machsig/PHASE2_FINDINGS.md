# MachSig Phase 2 — Findings

`MachSig-statement/v0.1` · population **raw 14,390 → generated excluded 3,617 → analyzed 10,773**
(`MachLib.*` **and** `Certcom.*`)

## Answers to the twelve required questions

**1. Declarations covered by statement features:** 10,773 analyzed; **7,569 are theorems**, which is
the population where the digest is meaningful (see finding 2).

**2. Statement feature distributions** (theorems only):

| feature | min | max | distinct | median |
|---|---:|---:|---:|---:|
| `statement_expr_node_count` | 1 | 15,501 | 538 | 75 |
| `statement_expr_depth` | 0 | 78 | 60 | 13 |
| `equality_head_count` | 0 | 98 | 13 | 3 |
| `implication_count` | 0 | 66 | 32 | 0 |
| `conjunction_count` | 0 | 26 | 14 | 0 |
| `disjunction_count` | 0 | 8 | 5 | 0 |
| `existential_count` | 0 | 20 | 9 | 0 |
| `distinct_constant_reference_count` | 1 | 76 | 57 | 11 |

**3. Which carry useful variation:** `statement_expr_node_count` (538 distinct),
`statement_expr_depth` (60), `distinct_constant_reference_count` (57) and `implication_count` (32).
Compare with the term layer, where the best feature had **5** distinct values. The statement layer
carries roughly an order of magnitude more variation.

`disjunction_count` (5 distinct, median 0) and `existential_count` (9, median 0) are close to
degenerate and should not be signature components on their own.

**4. Is `StatementDigest` deterministic? Yes.** SHA-256 over a documented structural serialization of
the stored `Expr` that keeps constructor shape, constant names and de Bruijn indices, and **drops
binder names and `mdata`**. 7,569 theorems yield 7,305 distinct digests.

**5. Is `ProofDigest` feasible? Partly — and honestly named.** Serializing full proof terms proved
too expensive, so the proof side uses Lean's cached structural `Expr` hash plus `approxDepth`. That
is a **64-bit non-cryptographic fingerprint**, adequate for detecting change in one declaration
across commits, and it is called `proof_expr_fp64` rather than a digest for that reason.

**6–7. Stability under proof refactor vs statement change:** established from **naturally occurring**
cases rather than synthetic edits, so no MachLib source was modified. Of 225 theorem groups sharing a
statement digest, **204 contain differing proofs** — Class A behaves exactly as specified
(`StatementDigest` SAME, proof fingerprint CHANGED). Worked example:

```
decayFloorUpTo_three           stmt fec52a6402fa   proof_depth 45   fp 2439174189
decayFloorUpTo_three_via_step  stmt fec52a6402fa   proof_depth  8   fp 4033241918
```

**8. Cosmetic rewrites:** binder names and `mdata` are dropped by construction, so a rename cannot
move the digest. This is a property of the encoding rather than a measured result, and is labelled
`definition_read` accordingly — no synthetic Class C corpus was built.

**9. Trust-footprint changes — the headline.** See below.

**10. Term features as annotation:** retained. `syntactic_node_count` with
`node_count_is_lower_bound` remains useful *per declaration*, and is unsuitable as a corpus-wide
discriminator (median 1).

**11. Coverage failures:** two found and both fixed — see "Defects found in my own tooling".

**12. Proceed to MachSig v0? Yes**, on the statement+proof pair, and **no** on canonical views.

---

## The headline: 59 same-statement / different-trust-footprint cases

The directive named this as the primary Phase 2 experiment. It succeeds, on real corpus data:

| spread | example |
|---:|---|
| 16 | `add_lt_add` 6 axioms ↔ `add_lt_add_both` 22 |
| 15 | `mul_left_comm` 4 ↔ `ea_mulswap3` 19 |
| 14 | `halve_in_unit_sorry` 7 ↔ `halve_in_unit` 21 |
| 13 | `natCast_one` 22 ↔ `natCast_one_local2` 9 |
| 13 | `le_of_mul_le_mul_pos_left` 14 ↔ `le_of_mul_le_mul_left'` 27 |

Identical kernel-facing claims, materially different trust surfaces. This is immediately
interpretable by a library reviewer without learning any MachSig vocabulary, needs no
canonicalization, and is available **today** — 59 instances at this commit.

Classification over the 225 groups: **145 Class A** (proof differs, footprint same), **59 Class D**
(proof and footprint differ), **21 identical representation**.

---

## Defects found in my own tooling

**1. `ConstantInfo.value?` returns `none` for theorems in this Lean version.** Every proof-side
feature was therefore empty — `proof_len = 0` and an identical fingerprint (the hash of `""`) for all
7,569 theorems. The first run of the Class A analysis reported plausible numbers built on that
emptiness.

Caught by testing a case whose answer I already knew: `decayFloorUpTo_three` and
`..._via_step` have the same statement and different proofs by construction, and the tool said their
proofs were identical. **The same bug is in Phase 1's `extract.lean`**, where
`value_direct_const_count` was null for every theorem; both are fixed by destructuring `.thmInfo v`
explicitly.

**2. The statement digest is meaningless for `def`s.** For a definition the "statement" is only its
type signature, and many share one (`Type`, `Real → Real`). Grouping over all declarations produced
**282 spurious "proof refactor" groups** of unrelated objects — one contained
`SingleExpStepwiseDecreaseReducer`, `RepresentedCurveArc` and `Certcom.CExpr` together. Restricting
to theorems removes them. The analysis is now theorem-only, with the reason recorded in the code.

Both defects produced *confident, plausible output*. Neither would have been caught by a gate.

---

## Recommendation

**Proceed to MachSig v0 with two layers, not three.** `StatementSig` + `ProofSig` carry real,
interpretable, corpus-wide variation. Representation views stay as optional annotation. Canonical
views stay unavailable, and Phase 6 stays deferred — as established in `CANONICALIZER_BRIDGE.md`,
that is a measured property of the corpus, not a missing feature.

The first product should be the trust-footprint diff, because it already works.
