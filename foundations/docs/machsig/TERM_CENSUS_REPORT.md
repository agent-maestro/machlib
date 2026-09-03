# MachSig Phase 1b — Term Census Report

`MachSig-terms/v0.1` · **1,084 term records** · runtime ~3 s · repeat-run **byte-identical**
(`sha256 2a8672f92b626145…`)

## The headline is a negative result

**MachLib is a corpus about universally-quantified trees, not about concrete terms.** Every
term-level structural feature is therefore close to degenerate, and that is a property of the
mathematics, not of the extractor. The evidence is below; the consequence for MachSig is in the
final section.

## Answers to the twelve required questions

**1. Term records extracted:** 1,084 (authored declarations only).

**2. Declarations containing ≥1 audited term:** 786.

**3. Distribution by representation:** `EMLTree` 993 · `CertcomEML` 91. `FTerm` and
`ElementaryEMLErf` were probed and occur (85 / 25 raw constructor occurrences) but are not walked by
this extractor — see blind spots.

**4. Which features actually vary:** `syntactic_node_count` varies, weakly — range 1–15, **median 1**,
with 561 of 1,084 records (52%) at exactly 1 node. `eml_node_count` / `const_node_count` /
`var_node_count` vary similarly.

**5. Degenerate or redundant:** `emltree_depth` is effectively a three-value feature — 662 records at
depth 1, 298 at depth 2, 91 at depth 0, and only **33 records above depth 2** out of 1,084. Range is
0–4. As a fingerprint component it is nearly constant.

**6. Does `elet` give useful sharing variation? NO.** Total `elet` occurrences across the entire
corpus: **5**. Sharing is present in the grammar and essentially absent from the corpus. No sharing
metric should be built on this, and the Phase 1b instruction to extract reuse counts is answered:
there is nothing to count.

**7. Does `cond_node_count` vary enough to matter? NO.** Total `cond` occurrences: **5**.

**8. Does any representation now have a real canonical view? NO** — see `CANONICALIZER_BRIDGE.md`.
The canonicalizers exist and are clean; the corpus does not supply concrete inputs for them.

**9. Cross-validation:** the raw constructor probe (counting `EMLTree.eml` heads over all
expressions) and the maximal-term walker are independent code paths, and they agree on which
declarations contain terms. `fOcc` was **not** used as a cross-check because `FTerm` is not walked
here — recorded as a gap rather than claimed.

**10. Runtime / determinism:** ~3 s for the walk, ~5 s for the declaration census. Two runs produce
byte-identical JSONL. Measured, not asserted.

**11. Blind spots** — three, and the first two are significant:

* **54% of terms are structurally incomplete.** 584 of 1,084 records contain opaque leaves — free
  variables of tree type. `EMLTree.eml A B` with `A B : EMLTree` universally quantified is *the*
  characteristic shape of this corpus. For those records `syntactic_node_count` is a **lower bound**
  on the tree denoted, and the schema says so (`node_count_is_lower_bound`). Treating it as a count
  would be exactly the count-versus-bound conflation this project is trying to avoid.
* **`FTerm` and `ElementaryEMLErf` are not walked.** They occur (85 and 25 constructor occurrences)
  but have no extractor. Absent, not null.
* **Compiler-generated parents were 60% of the raw yield.** The first run produced 2,685 records, of
  which 1,601 came from `.match_`, `.eq_def` and similar auto-generated companions. `Name.isInternal`
  does **not** catch these. They are now filtered, and the raw/filtered figures are both reported so
  the filter's effect stays visible.

**12. New ambiguity discovered:** yes, in *representation scope* rather than depth. The Forge-facing
`EML` grammar lives under **`Certcom`**, not `MachLib`. Phase 1's declaration census filtered
`isMachLib` and therefore **excluded it entirely** — the same scope boundary that produced the
220/243 axiom discrepancy. A first probe of this grammar reported `tr1 = elet = cond = 0`; that was a
false absence caused by guessing the namespace, caught by checking the real constructor names.

## What this means for MachSig

The term layer carries far less information than the declaration layer. Concretely: the best term
feature (`syntactic_node_count`) has a median of 1 and is a lower bound half the time, while
`axiom_dependency_count` at the declaration layer spans 0–88 with an interpretable distribution.

A `CanonicalSig` or `SourceSig` built on term structure would be nearly constant across the corpus,
and would additionally be a bound rather than a measurement on half its inputs. **The evidence says
MachSig's signal is in declarations and proofs, not in term syntax** — and Phase 2 should test
stability per capability rather than assume three populated signature layers exist.
