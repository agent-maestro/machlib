# Philosophy

## What this file used to say, and why it changed

Until 2026-09-05 this file made the case for MachLib as a *training gym for machines*: a
machine-shaped corpus of theorem records with multiple proofs per theorem, tactic traces with
failures, difficulty labels calibrated from agent attempts, and a schema so other domains could
publish interoperable corpora. The analogy was ImageNet.

That thesis did not survive contact with the work. The record corpus stalled at a few hundred
entries, the gym environment was last touched in May 2026, and every session since has gone into
proving theorems and building gates. Rather than keep a philosophy the repository no longer
practises, this file now states the one it does. The old text is preserved at the tag
`attic/product-wave-2026-05`.

One piece of the old thesis did come true, in a different shape. The machine-shaped corpus exists:
it is `foundations/MachLib/Discovered/`, the 749 proof obligations that Forge's `@verify(lean)`
annotations emit from real kernels, each one a theorem a machine wrote for a machine to close.
Its measured close rate is the training signal the gym was meant to produce, and its failure
classes are the curriculum. Nobody had to design a schema for that; the compiler did it.

## Mathlib-free, by construction, and what that costs

`import Mathlib` is the right choice for almost every Lean project. MachLib does not take it, for
one reason that still holds: this library's job is to be the check target of a compiler that runs
on machines where a forty-minute cold build of Mathlib is not acceptable, and whose emitted
obligations must compile in isolation, thousands of times, on every change. The whole foundation
builds in about a minute.

The cost is explicit and it is the most important sentence in this file. Everything Mathlib
would prove as a theorem — the ordered field of reals, the definitions and derivatives of `exp`,
`log`, `sin`, `cos`, the floating-point model — is an **axiom** here. A library built on axioms
can be vacuous without any `sorry` appearing anywhere, and `#print axioms` cannot tell you.

So the doctrine is not "zero axioms" but **zero unmodeled axioms**. Every trusted axiom is listed
in a generated manifest, and a sibling project that imports both Mathlib and MachLib checks, in
the kernel, that a Mathlib term inhabits each axiom's interpreted type. The 22 axioms about IEEE
floats have no model in ℝ and are kept in their own class, validated by measurement, because a
hardware certificate rests on exactly those and a reader should know it. A gate fails if the
witness project stops running, because it did once, for 33 days, and nothing said so.

## The gate is the source; prose is a copy

Most of what went wrong in this project went wrong in prose. Counts were written from memory and
were fiction. A theorem was proved with hypotheses nobody could satisfy and every gate stayed
green. A ledger row said "open" for weeks after the obligation was closed. An absence claim ("this
lemma does not exist here") stayed true in the text long after someone added the lemma.

Each of those has a gate now, and the gates share one rule: **an instrument must be shown capable
of both verdicts before either is read.** A check that cannot fail is not a check. So every gate
carries a self-test with a specimen that must fire and a control that must stay silent, the runner
proves it conducts a failure to its own exit code, and a number in a document is either the pasted
output of a command or a defect.

## Named obligations, not silent gaps

A partial result is committed by naming what it lacks. An open question becomes a `def` that a
theorem may consume and nothing may conclude; a ledger tracks it in both directions, so a row that
says open when the corpus has closed it fails the build, and a row that says discharged by a
theorem that does not conclude it fails too. A conjecture can be refuted, and that is a third
status, checked the same way. Reductions that go in a circle are detected and counted as one
obligation, not zero.

The point is that the debt is legible. Anyone can read the ledger and know what this library is
still assuming.

## Paper before Lean

The kernel checks proofs; it does not find them, and it will happily check a proof of the wrong
statement. Every result here that cost more than a day was worked out on paper first, checked
numerically where a number could be checked, and priced by opening the layer beneath the layer
that looked cheap. Three of the project's worst weeks were spent on statements that turned out to
be false, each time because the estimate measured the reduction and not the discharge.

The corollary is that a refutation is a result. Two of the depth-3 statements this library needed
were false, and the witnesses that refute them are theorems too.

## Relationship to Mathlib

Complementary, and one-directional. Mathlib is where the mathematics is; MachLib borrows its
truth through the witness project and gives nothing back except, occasionally, a question about
what a small `exp`/`log` grammar can express. If Mathlib ever gains a Khovanskii zero bound, the
one deep classical axiom still cited here should be replaced by a witness the same day.
