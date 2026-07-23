# Can a finite EML expression equal `sin`? — A research note

*For readers outside this codebase. Companion to `EML_WITNESS_FINDING_DECISION_2026_07_15.md` (the
full 72-round chronological log) and `EML_WITNESS_FINDING_THEOREM_MAP.md` (the spine, in dependency
order). This note is neither — it's the argument, told once, in order, distinguishing what's
actually proved from what's merely trusted.*

## The question

MachLib's EML tree language builds real-valued functions from an unusually small closed set of
operations. Precisely: `const c`, `var` (the input `x`), and `eml t1 t2`, whose value is FIXED as
`exp(t1.eval x) - log(t2.eval x)` (`log` clamped to `0` off the positive axis). **There is no
addition, no multiplication, no squaring constructor anywhere in the grammar** — every compound
value is irreducibly "a positive `exp` term minus a `log` term." This matters for reading everything
below correctly: it was checked directly (Track C, item C2) that this grammar cannot even build
`x²` — not proved impossible in general (that would be its own theorem, not yet attempted), but
every hand-construction attempt failed, and nothing in the codebase's differential Pfaffian-chain
machinery (which describes derivative RELATIONS, not a tree's own closed-form value) bridges the
gap. State this up front rather than let a reader infer more expressive power than exists: the
non-representability results below are about a genuinely minimal language, and that is itself part
of what makes them informative — a richer grammar (with addition/multiplication) is a live, open
question about SCOPE, not a design choice quietly assumed away. Every barrier theorem in this note
should be read as "no tree IN THIS GRAMMAR" — whether it would survive adding multiplication is, for
each theorem, a separate question not checked here.

Is this narrow language *complete* relative to what it can express? Can every "reasonable" target
function reachable by nested `exp`/clamped-`log` be written as some finite EML tree?

This note answers it for one natural family, since generalized to a much wider one (see "How far
this now reaches," below): **no finite EML tree equals `sin`, `cos`, or any member of the
`nestedTarget` family** (`sin`, `log(c + sin x)`, `log(d + log(c + sin x))`, and so on, arbitrarily
nested) — **exactly**, at every real `x`, for any finite tree depth. Not "no tree found yet." Not
"no tree under some bound." No tree, period, unconditionally.

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

## How far this now reaches (updated past the original `sin`/`nestedTarget` result)

Everything above this section describes the arc as it stood the morning of 2026-07-22. The same day
and the days after, two things happened that change what a reader should take away — recorded here
rather than left for the theorem map or decision doc alone to carry, since both bear directly on
"what this result claims."

**The bounded-domain gap below is CLOSED, not open — an earlier version of this note said
otherwise.** The first cut of this arc's `ε`-closeness result (Track C item C6) was a pure TAIL
statement: no tree stays within `ε < 1` of `sin` for ALL sufficiently large `x`, silent on any fixed
bounded interval, however long. That gap mattered concretely, because a compiled artifact evaluates
on a bounded domain, not `x → ∞`. It has since been closed (`no_tree_eps_close_to_sin_compact_
interval`, decision doc cont. 79–80): no finite EML tree, valid across an interval containing `0`,
stays within `ε < 1` of `sin` on the WHOLE interval once it is longer than an EXPLICIT function of
the tree's own structure (`EMLExplicitBound.combinedBoundE` — a genuine closed-form bound in tree
depth and size, not an abstract "eventually," and not blocked on the harder `exp_hard` Khovanskii
frontier this arc had originally expected to need).

**The abstract result now connects to a real compiled artifact, with real IEEE-754 rounding.**
Everything described so far is about `EMLTree.eval`, a mathematical function — it says nothing
about what happens once a tree is actually compiled and run. The Certcom compositional handshake
(decision doc cont. 82–88) closes that gap for the FULL grammar this arc studies (`const`/`var`/
`eml`, any depth or shape): `Certcom.eml_tree_grounded` gives an explicit, machine-computed
closed-form error bound between (a) `T.eval`, the exact mathematical value, (b) the exact real
value of the compiled expression before rounding, and (c) the actual `Float`-rounded output of a
Certcom-compiled program — grounded against Certcom's own disclosed IEEE-754 rounding axioms for
every one of the 14 transcendental primitives it uses (a full retroactive audit, cont. 86, found and
fixed 10 of those 14 axioms, which had quietly asserted something FALSE of real rounding before this
arc's own external review caught it — see cont. 85's erratum). Nothing about `EMLTree.eval`'s own
non-representability claims changed; what's new is that the trust chain now reaches all the way from
"no finite EML tree equals `sin`" down to "and here is the exact, bounded error of a real compiled
program that tries anyway."

**The `sin`/`nestedTarget`-specific result generalizes to every nonconstant, continuous, periodic
target, not just that one family.** `no_tree_eq_periodic_target` (Track C item C9, decision doc
cont. 89) proves the general case directly: no finite EML tree equals ANY nonconstant,
everywhere-continuous, periodic function — `sin` and the whole `nestedTarget` tower are now
instances of one theorem, not the theorem itself. Built via genuinely new Extreme Value Theorem
attainment machinery this codebase lacked before — though, in an honest erratum caught while
building the actual barrier theorem (not assumed going in), that EVT machinery turned out not to be
what the generalization needed: periodicity alone makes every value of a periodic target recur
arbitrarily far out, not just an extremal one, so an arbitrary basepoint does the same job the
infimum was originally thought to require. (`sin_not_tailSign`, the original hand-built argument
this note describes above, is itself a confirming precedent in hindsight — it already used
`sin 0 = 0`, never `inf(sin) = −1`.)

## What this still doesn't claim

The core scope statement from "The question" above is unchanged: this is about **exact**
representability on **all** of the reals, for the grammar as it stands, and the non-representability
results are specific to targets that are periodic (or otherwise fail `TailSign`) — a target that
settles into one eventual sign or eventually vanishes is NOT covered by any theorem in this arc,
and could, for all this arc shows, be representable. Two chain-order-shaped extensions were
investigated in depth and remain genuinely open, not merely unattempted (decision doc cont. 90):
whether a chain-order-SENSITIVE obstruction (distinct from the periodicity-based `TailSign` used
throughout) could separate what a bounded-order Pfaffian chain can represent from what a
higher-order one can (`sin` itself is chain order 2 classically, so `TailSign` and chain order are
confirmed orthogonal axes, not composable ones as originally hoped) — and whether the validity
threshold inside `eml_tailSign_unconditional`'s own proof can be made an EXPLICIT function of tree
structure, which traces to a `Classical.byContradiction` core that proves the threshold exists
without ever constructing it. Also still open: other target functions beyond the periodic family
covered here (Track C's census-style instantiations are illustrative, not exhaustive), and whether
the grammar's inability to build `x²` (see "The question," above) is a fixed scope commitment or
something a future richer grammar would lift.

## Where to go next

- **The spine, in dependency order, plus everything built since:** `EML_WITNESS_FINDING_THEOREM_MAP.md`.
- **The full chronological record**, including every dead end with its own reasoning (not just
  the three summarized above): `EML_WITNESS_FINDING_DECISION_2026_07_15.md`.
- **A minimal reproducer** importing only the public spine and printing the axiom footprint of the
  headline results directly: `foundations/EMLWitnessFindingReproducer.lean` (see its README).
