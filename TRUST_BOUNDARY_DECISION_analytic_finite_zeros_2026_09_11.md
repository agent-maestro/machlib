# Trust-boundary decision — `analytic_finite_zeros_compact`

## ⚠ VOID — 2026-09-11, same day. The premise was false.

**`MachLib.analytic_finite_zeros_compact` is already in `trustedFootprint`, and it is already
`witnessed`.** There is no fork, nothing to promote, and no trust cost to pay. Everything below was
written on a checking error and is kept only as the record of it.

**The error.** `def trustedFootprint` spans **64 lines**. The check that produced this document read
only the first:

```python
line = next(l for l in s.splitlines() if l.startswith("def trustedFootprint"))   # WRONG
"analytic_finite_zeros_compact" in line                                          # False
```

Reading the whole definition, and stripping the backticked names that appear in its interleaved
*comments*, gives exactly **149** names — matching the count the ledger and manifest both state,
which is the cross-check that should have been run before writing anything. `AXIOM_MANIFEST.md`
lists the axiom as `witnessed` and always did.

**What this changes, and it is good news.** The ray-vs-global gap in `OneQueryLevelSet` can be
attacked **right now**, with an axiom that is already trusted and already witnessed. The cost that
made this a decision does not exist. §2's composition is still unproved and still the thing to try;
it just needs no permission.

**What survives.** §2's shape, §4's blast-radius reasoning, and the criterion in §5 — *the trusted
footprint moves only in exchange for a theorem a shipped artifact consumes* — which is unaffected
and has since found a real instance elsewhere: `MachLib.Real.realOfScientific`, which every Forge
certificate containing a decimal literal depends on and which **is** genuinely outside the trusted
footprint (verified by the corrected method). See
`forge/reports/BUG_certificates_depend_on_unclassified_axiom.md`.

---

*Original text follows, preserved for the record. Its §0 claim that the axiom is "in `knownAxioms`
and not in `trustedFootprint`" is FALSE.*

---

**Status: VOID — see above.**

---

## 0. The framing was wrong, and the correction shrinks the decision

The question was posed as *"should the Mathlib-free base admit compactness and analyticity?"*
It should not be, because **analyticity is already in the trusted footprint**. Nine axioms:

```
analytic_add   analytic_comp  analytic_const      analytic_exp   analytic_id
analytic_log_pos   analytic_mul   analytic_one_div_pos   analytic_sub
```

These are shipped, trusted, and witnessed. So the decision is not about admitting a new domain into
the base. It is about **one axiom, in a domain the base already trusts**:

```
MachLib.analytic_finite_zeros_compact
    -- a not-identically-zero analytic function has finitely many zeros on a compact
```

which is presently in `knownAxioms` and **not** in `trustedFootprint`. Nothing shipped may touch it.

That is a much smaller step than "relax the purity rule," and it should be judged as the small step
it is rather than the large one it was mistaken for.

## 1. Why it is wanted

Two open results are blocked at the same place, and it is the same shape both times: **the corpus's
machinery is RAY-shaped and the theorems are GLOBAL.**

* **`OneQueryLevelSet`** (open row). `oneQueryCtx_mobius` (2026-09-11) made the level-set equation
  linear in the query value, which was the algebraic obstruction. What remains is that the set where
  the context's denominators vanish must be **finite**, and `divClamp_denom_and_divDenomsOK` gives
  only *eventually nonzero* — a ray.
* **The depth ladder.** `EMLDecayLadderStep` §5 records that absorbing a per-tree ray into a
  constant "would need every EML germ bounded on `[1, X₀]`, true presumably, and not something this
  base can prove (no compactness, no continuity)."

## 2. The shape of the unlock — asserted, NOT proved

For `OneQueryLevelSet` the join looks like this, and it is the reason this axiom and not some other:

```
divClamp  :  ∃ X, ∀ x ≥ X, denominators OK          -- a ray, already proved
analytic_finite_zeros_compact
          :  finitely many zeros on [1, X]          -- the missing half
          ⟹  finitely many bad points on [1, ∞)     -- a finite exceptional LIST
```

and the relevant function *is* analytic by axioms the base already trusts — it is polynomial in `x`
and in `Fbasis (P/Q) = exp w + log w`, so `analytic_exp`, `analytic_log_pos`, `analytic_mul`,
`analytic_add`, `analytic_comp`, `analytic_one_div_pos` cover it on the positivity domain.

`EMLZeroListFromBound` already converts a zero *bound* into a zero *list*, in both ray and global
forms, and its header says outright that "the global form is what a level-set theorem consumes."

**This composition has not been carried out.** It is the reason to take the decision seriously, not
evidence that the theorem is done. If it is attempted and fails, that failure is the most valuable
thing in this record, because it means "one lemma away" was wrong.

## 3. What supports it — and the part that changes the cost

`analytic_finite_zeros_compact` is **probably witnessable**, which would mean the trust boundary
expands by a *witnessed* axiom rather than an unwitnessed one. That is a materially different price.

`monogate-lean/MonogateEML/AxiomWitnessBridge.lean` already:

* imports `Mathlib.Analysis.Analytic.IsolatedZeros` and `Mathlib.Topology.Compactness.Compact`;
* proves `realSetFinite_of_finite`, the conversion from Mathlib's `Set.Finite` to MachLib's
  `RealSetFinite` (a length bound on every `Nodup` list drawn from the set — they are *not* the
  same predicate, which is the subtle half);
* states, in its own docstring: *"Only the former is still open; feed its `Set.Finite` to this
  lemma and the witness closes."*

So the remaining work is the analysis half: Mathlib's isolated-zeros machinery to `Set.Finite` on a
compact. **Not verified here.** If it turns out Mathlib does not give this as cleanly as the
docstring assumes, the cost reverts to an unwitnessed axiom and Option B gets weaker.

## 4. What becomes conditional, and what does not

If promoted:

* **Conditional on it:** any theorem whose `#print axioms` footprint contains it. The existing
  machinery makes this automatic and visible — the axiom ledger pins shipped footprints ⊆
  `trustedFootprint`, so the blast radius is mechanically enumerable at any time, not estimated.
* **NOT inheriting it:** everything currently proved. This is an addition to the permitted set, not
  a change to any existing statement. The 720-theorem generated corpus, the closed-loop control
  results, the float-bridge lane and the ℤ-model consistency check are untouched.
* **Disclosure:** one row in `disclosedTrusted` with its reason, which gate 23–24
  (`disclosure_names_check.py`) now requires to name only constants that exist. If witnessed, it
  also appears in the witness registry and the `witnessed` count rises by one; if not, it joins the
  `witnessGap` with a machine-readable reason and the gap count stops being 0 — which is itself a
  visible, gated change.

## 5. The options

**Option A — minimal-core purity.** Do not promote. `OneQueryLevelSet` stays open; the ladder's
`[1, X₀]` friction stays. The base keeps the property that it assumes no finiteness principle.
Legitimate, and cheap to hold.

**Option B — disclosed analytic extension.** Promote `analytic_finite_zeros_compact` into
`trustedFootprint`, witness it if the analysis half closes, and attack `OneQueryLevelSet`.

### Direction set 2026-09-11: the promotion criterion is tightened

The two options were being weighed as if MachLib's trusted base and Forge's research frontier were
one thing. They are not, and separating them dissolves most of the disagreement:

> **The trusted footprint moves only in exchange for a theorem that a SHIPPED ARTIFACT CONSUMES.**

`OneQueryLevelSet` and the depth ladder are research results. No customer artifact consumes either.
So under this criterion the axiom does **not** enter `trustedFootprint` even if the composition in
§2 closes — the research keeps it branch-local, and Forge's base stays frozen.

That is Option A *for the product* and Option B *for the research*, simultaneously, which is what
both readings were actually reaching for. The cost of getting this wrong is asymmetric: a research
frontier that sets a product's trusted base is how a shipped certificate ends up resting on an
assumption admitted for a theorem no customer will ever invoke.

**Recommendation: run the experiments, promote nothing yet.**

1. First, attempt the **witness** in `monogate-lean` — it costs nothing in machlib and answers the
   question that sets the price.
2. Then attempt the **composition** in §2 on a branch, with the axiom promoted there only.
3. Promote in `trustedFootprint` **only if** the composition closes **and** a shipped artifact
   comes to depend on it. Today nothing does, so the expected outcome of a successful experiment is
   a closed theorem on a branch and an UNCHANGED trusted base. If it does not close, the axiom stays
   out and this record gets a section saying what the real missing structure was.

That ordering means the trust boundary moves only in exchange for a theorem somebody ships, never in
anticipation of one. The failure mode it avoids is the one the corpus is built to avoid: widening the
base, finding the proof does not close, and leaving the widened base behind.

## 6. What would make this decision wrong

* If the composition in §2 does not close, promoting buys nothing and costs a row.
* If the witness does not close, this is an unwitnessed axiom in a base whose whole claim is that
  every witnessable axiom is witnessed — the `unmodeled` count is currently **0** and gate 13 fails
  if it is ever nonzero. That figure is quoted publicly.
* If `RealSetFinite` and `Set.Finite` turn out to differ in a way `realSetFinite_of_finite` does not
  bridge, the witness is not a witness. §3 flags this as the subtle half deliberately.

---

**Decision:** _promotion unrecorded and not yet due._ Direction set 2026-09-11: base frozen for the
product; experiments permitted on a branch. The promotion line is filled in only if a shipped
artifact ever consumes the result.
