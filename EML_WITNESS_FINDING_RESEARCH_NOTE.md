# Can a finite EML expression equal `sin`? — A research note

*For readers outside this codebase. Companion to `EML_WITNESS_FINDING_DECISION_2026_07_15.md` (the
full 72-round chronological log) and `EML_WITNESS_FINDING_THEOREM_MAP.md` (the spine, in dependency
order). This note is neither — it's the argument, told once, in order, distinguishing what's
actually proved from what's merely trusted.*

## The question

MachLib's EML tree language builds real-valued functions from a small closed set of operations
(`exp`, a clamped `log`, addition, nesting). It's expressive — but is it *complete*? Can every
"reasonable" target function be written as some finite EML tree?

This note answers it for one natural family: **no finite EML tree equals `sin`, `cos`, or any
member of the `nestedTarget` family** (`sin`, `log(c + sin x)`, `log(d + log(c + sin x))`, and so
on, arbitrarily nested) — **exactly**, at every real `x`, for any finite tree depth. Not "no tree
found yet." Not "no tree under some bound." No tree, period, unconditionally.

## Three kinds of trust — kept explicitly separate

A claim like this is only as good as what it's allowed to assume. Three categories, and it matters
which one each piece of this result falls into:

**1. Formal theorems.** The 16-file proof spine (mapped in `EML_WITNESS_FINDING_THEOREM_MAP.md`)
is machine-checked Lean 4, `sorryAx`-free, and — as of this arc's most recent engineering pass
(`AxiomLedger.lean`'s whole-module guard) — every theorem in it is mechanically confirmed to draw on
nothing beyond the trusted footprint below. This is the actual mathematical content of the result.

**2. Standing analytic axioms.** MachLib does not build its reals on top of Mathlib; it axiomatizes
a real-analysis model directly (`MachLib.Real`) — `sin`, `cos`, `exp`, `log`, `pi`, their basic
identities, and derivative facts (`HasDerivAt_sin`, etc.) are foundational axioms of *this*
codebase, not derived from anything more primitive in Lean. This is no different in kind from any
formalization trusting its base number system — it's the floor the whole library stands on, and
this arc doesn't touch it, question it, or add to it.

**3. Retired validity assumptions.** This is the interesting middle category, and the actual
subject of this arc. `EMLPfaffian.lean` states — as an `axiom`, not a theorem —
`eml_pfaffian_validon_from_sin_equality`: *if* a tree's value equals `sin` everywhere, *then* the
tree is well-behaved (`EMLPfaffianValidOn`) on a specific range. This was standing, unproven trust
for the life of the tool: nobody had shown it was TRUE, only that assuming it let other proofs go
through. This arc's actual finding is that **the axiom's hypothesis is never satisfiable** — no
tree ever equals `sin` — so the axiom is **vacuously true**, provable outright
(`eml_pfaffian_validon_from_sin_equality_proved`). The `axiom` keyword is still physically in the
file (a deliberate, documented, import-graph-driven deferral — see the decision doc's A2 entry,
2026-07-22), but what it asserts is no longer a standing assumption. It's a corollary.

## Why the tail invariant was the right pivot — three routes tried and ruled out first

The proof that eventually closed this used a structural invariant called `TailSign`: every
function built by an EML tree is *eventually* sign-definite or eventually zero — never oscillates
forever. That's not the first idea tried. Three others were, each investigated seriously, each
ruled out for a precise, checked reason:

**Taylor-coefficient / derivative matching.** The natural first instinct: if a tree's value equals
`sin` everywhere, its derivatives must too — match enough of them and pin the tree down. Worked out
concretely: computing a tree's *second* structural derivative introduces the sibling subtree's
*second* derivative as a brand-new unknown. Each additional derivative order buys exactly one new
unknown along with the new equation it produces — the sibling subtree is exactly as unconstrained
after the computation as before. This isn't a limitation of how far the matching was pushed; it's
structural. More Taylor coefficients don't shrink the degrees of freedom.

**Validity-free Pfaffian encoding.** A different tack: instead of proving a tree is well-behaved
(needs `log`'s argument to stay positive), encode the Pfaffian *chain* itself in a way that doesn't
need that positivity — sidestep the requirement rather than establish it. Existing machinery
(`PfaffianExpLogRecipClass.lean`) looked, from its own docstring, like it offered exactly this: a
chain-type where log-valued nodes could be "signed." Checked carefully rather than taken at face
value: the exemption only covers the log node's own *output* value (which was never the problem);
tracing the actual differential relation (`log(v)' = v'·(1/v)`) shows the *reciprocal* factor still
requires the log's *argument* `v` to stay strictly positive, just attached to a different chain
variable than where the docstring drew attention. This isn't a patchable gap in one encoding — it's
forced by `log`'s actual derivative, `1/x`. Any Pfaffian-chain representation of `log`, in any
encoding, can only be valid where the argument avoids zero. Two independent strategies (deriving
validity structurally, and avoiding the need for it) converged on the same underlying fact from
different directions.

**Case-by-case tree-shape classification.** The most productive of the ruled-out routes, and the
most instructive about why the eventual proof needed to be uniform. Rather than one general
argument, this approach classified trees by concrete sign/boundedness behavior and closed each
class by hand — genuinely valuable, genuinely general within its scope, and it closed most shapes.
But the open remainder wasn't empty: a specific, fully constructed tree
(`expWrappedNonMonotonicWitness` — built by wrapping an already-known problem tree in `exp` to fix
its one flaw, unboundedness) escaped every closure built this way. It could still be closed, but
only by an argument specific to *that tree's* numeric parameters (its problematic zero-crossing
happens to sit at a negative `x`, outside the region the heavier machinery needed to check) — not
one that generalizes to every tree with the same qualitative shape. Case-by-case classification
finds real, irreducible cases; it doesn't, by construction, produce a proof that covers every case
at once.

**The pivot.** All three routes fail for related reasons: they each try to *constrain* an
unconstrained sibling subtree, directly or by cataloguing its possible shapes. `TailSign` doesn't —
it observes that *every* EML tree's value, regardless of shape, eventually settles into one of
three behaviors (eventually positive, eventually negative, or eventually zero), proved once by
structural induction over the tree's own recursive definition, no case-by-case classification
needed. `sin` (and the whole `nestedTarget` family) provably has none of the three. That mismatch
is the entire proof, and it applies to every finite tree uniformly — which is exactly the property
none of the three earlier routes could deliver.

## What this doesn't claim

This result is about **exact** representability of specific target functions on **all of** the
reals. It says nothing about: approximate representability (small `ε`-closeness — flagged as
Track C future work, not yet attempted), other target functions not in the `sin`/`nestedTarget`
family, or bounded-domain representability (an EML tree could still match `sin` on some finite
interval — that's a different, easier question this result doesn't address).

## Where to go next

- **The spine, in dependency order:** `EML_WITNESS_FINDING_THEOREM_MAP.md`.
- **The full chronological record**, including every dead end with its own reasoning (not just
  the three summarized above): `EML_WITNESS_FINDING_DECISION_2026_07_15.md`.
- **A minimal reproducer** importing only the public spine and printing the axiom footprint of the
  headline results directly: `foundations/EMLWitnessFindingReproducer.lean` (see its README).
