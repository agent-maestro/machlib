# Philosophy — for machines, by machines

## The case for machine-native math

Mathlib is the standard formal-math library for the Lean ecosystem.
It is the result of a decade of careful work by hundreds of human
mathematicians. It is also organised the way mathematicians think
about mathematics: by area (analysis, algebra, topology), by level
of abstraction (basic, advanced, frontier), by aesthetic conventions
(short proofs over long, named lemmas over inline derivations).

Those organising principles are correct for humans. They are wrong
for machines.

A machine learning to prove theorems does not need every analytic
result presented as a polished pearl. It needs:

  - **Multiple proofs per theorem**, ranked by cost. So it can
    learn that a theorem has a 2-tactic proof, a 5-tactic proof,
    and a 12-tactic proof — and that the 2-tactic proof was found
    by a human, the 5-tactic proof was found by an agent, and the
    12-tactic proof is what a beginner produces.
  - **Tactic traces with failures**. A successful proof tells the
    agent what works. A failed-and-corrected attempt tells it what
    doesn't. Mathlib's git history has both, but it isn't curated
    that way; you'd have to scrape commit messages and PR review
    threads.
  - **Difficulty calibration from agent attempts**. "Beginner" and
    "expert" need to be measured against a population of provers.
  - **Structural metadata**. Chain order, cost class, eml depth,
    drift risk. Mathlib's lemmas don't carry these annotations
    because human readers don't need them; an agent picking
    representations does.
  - **A schema**. So that other domains can publish corpora that
    interoperate.

Adding any of those things to Mathlib would change Mathlib for its
existing audience. The right move is a separate library.

## The ImageNet analogy

Before ImageNet there were dozens of small, carefully-curated
computer-vision datasets. Each was lovingly assembled, each was
appropriate for the domain it served. None of them produced
AlexNet. AlexNet required a different *kind* of dataset — one
big enough that the failure modes of small-data training showed
up, with labels consistent enough that scale paid off, and with
a permissive license so the whole field could iterate on it.

ImageNet did not replace the small datasets. The small datasets
remained correct for their domains. ImageNet was a different
artefact, with a different goal.

MachLib is to formal math what ImageNet was to vision: a
machine-shaped corpus, organised for training, big enough that
the failure modes of small-data training show up.

## Independence (zero Mathlib at v1.0)

`import Mathlib.Analysis.SpecialFunctions.ExpDeriv` pulls in
~500,000 lines of supporting code. The cold build of that import
takes about 45 minutes. An agent cannot start proving anything
until that build finishes.

EML — the smallest mathematical theory MachLib needs to be useful —
needs about 0.7% of Mathlib:

| Module | Lines |
|---|---|
| Real number basics | ~1,000 |
| Exp and Ln | ~1,000 |
| Trig (sin, cos) | ~800 |
| EML core (universality) | ~600 |
| **Total** | **~3,400** |

Three thousand four hundred lines builds in seconds. The agent
starts proving immediately. There are no breaking changes from
upstream. Every lemma can carry MachLib's own annotations.

This is the correct trade for the audience. A human reviewer
opening MachLib expecting Mathlib's conventions would find it
strange; an agent training on MachLib will not notice.

## Relationship to Mathlib

Complementary, not competing. Same Lean kernel. Same mathematical
results. Different design goals. Different audience.

  - **Mathlib is the cathedral.** It is where formal mathematics
    happens at the frontier. Researchers contribute. Proofs are
    polished. The library reflects the state of formal math.
  - **MachLib is the training gym.** It is where AI agents learn
    to prove. Records are dense. Multiple proofs per theorem.
    The library reflects what a curriculum-shaped corpus needs.

Some researchers may use both. Some agents may train on both. The
two libraries do not need to know about each other.

We expect the long-run shape to be: human mathematicians extend
Mathlib; AI agents extend MachLib; periodically, a discovery in
one moves into the other. The Lean kernel is the lingua franca.

## Honest about what we don't have

  - The independent foundations are partial. v0.1 still imports
    Mathlib for exp / ln / trig. Phase 1 replaces those imports
    with self-contained 3,400-line foundations.
  - The corpus is 256 records, not 100K. We are upfront about
    this; the roadmap shows the path from 256 → 1K → 10K → 100K.
  - The chain-order metadata depends on Pfaffian theory not yet
    formalised in Mathlib (the Khovanskii zero-count gap). Some
    structural claims sit in the corpus as conjectures with
    empirical support, not as machine-checked theorems. We mark
    them clearly.
  - Difficulty calibration starts at "beginner / intermediate /
    expert" labels assigned by the seed authors. As agents log
    attempts in the gym, those labels get re-fitted from data.

The library will improve. We tell you what's done and what isn't.
