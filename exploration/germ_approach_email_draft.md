# Cold-email draft — one specialist, one question

Intended recipients: Matthias Aschenbrenner, Lou van den Dries, Joris van der Hoeven, or another
worker on transseries / H-fields. Send to **one** at a time; swap the bracketed sentence naming
their work. Both links must resolve before sending (the MO post must be live; the repo file must be
pushed to `master`).

**Subject:** A uniformity question about exp–log germs of bounded complexity

---

Dear Professor \<Name\>,

Your work on transseries and H-fields is the nearest thing in the literature to a question I
cannot place, and two lines from you would probably settle it.

Fix the expression class built from real constants, *x*, and one constructor sending (A, B) to
exp(A) − log(B), with log totalised (log y = 0 for y ≤ 0); complexity is tree depth.
Every such expression denotes a germ in Hardy's class 𝓛 of logarithmico-exponential functions.

**The question.** For every depth bound *j*, is there a single *k* such that: whenever A and C have
depth ≤ *j* and C < exp(A) on a ray, the gap eventually satisfies exp(−exp^k(x)) ≤ exp(A) − C ?

With *k* allowed to depend on the pair this is classical (the gap is a nonzero 𝓛-germ, 𝓛 is a
field, every 𝓛-germ is o(exp^k) for some *k*); the open content is that *k* depends on the depth
bound alone. In transseries language: does bounded defining complexity uniformly bound
the asymptotic complexity of the leading surviving term after arbitrary cancellation?

**What has been tried.** Eight descent mechanisms — syntactic measures, measures into arbitrary
well-founded orders, every germ-invariant parameter, a peeling recursion, an enlarged germ class,
relations on pairs — are ruled out by machine-checked theorems, and a falsification search through
depth 7 found no counterexample.

In order of usefulness: a theorem, a counterexample, a citation, or a reason the question is
malformed. If the answer is "that is Theorem X in …", one line saying so is the most valuable
reply I could get, and I will not follow up further.

MathOverflow version: \<MO link\>
Long version, with the machine-checked statements: \<repo link\>

This came out of a Lean formalisation project; nothing practical depends on the answer.

With thanks,

\<Name\>
