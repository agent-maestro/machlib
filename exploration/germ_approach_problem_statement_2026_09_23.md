# Uniform asymptotic separation for exp–log expression germs of bounded complexity

**An open problem, stated for a specialist in Hardy fields, transseries, o-minimality or asymptotic
differential algebra.**

Prepared 2026-09-23, and revised the same day: §5 gained mechanisms 7 and 8, and §4 separates the
two metrics that had been running conflated (`j − 3` and `j − 2`).
The mathematical assertions below are machine-checked in a proof assistant,
the numerical ones come from a documented search program, and the attributions to the literature
are attributions rather than theorems of ours; Appendix A says which is which and where each lives.
You need no background on the project this came from — the problem is self-contained.

---

## 1. The class of germs

Fix the following term grammar. An *expression* is built from

* a constant symbol for each real number `c`;
* the variable `x`;
* one binary constructor: from expressions `A` and `B` form `⟨A, B⟩`.

Each expression `t` denotes a function on the reals by

&nbsp;&nbsp;&nbsp;&nbsp;`⟦c⟧(x) = c`, &nbsp; `⟦x⟧(x) = x`, &nbsp; `⟦⟨A,B⟩⟧(x) = exp(⟦A⟧(x)) − L(⟦B⟧(x))`,

where `L` is the **totalised logarithm**: `L(y) = log y` for `y > 0`, and `L(y) = 0` for `y ≤ 0`.

The *depth* `d(t)` is the usual one: constants and the variable have depth 0, and
`d(⟨A,B⟩) = 1 + max(d(A), d(B))`. Depth is the complexity measure everything below is indexed by.

Three remarks a reader of this area will want immediately.

**What the single constructor gives you.** `⟨A, 0⟩` and `⟨A, 1⟩` both denote `exp ⟦A⟧` — the first
because `L(0) = 0` by totalisation, the second because `log 1 = 0`. So one constructor edge buys one
exponential, and the `k`-fold iterated exponential `T_k`, defined by `T_0(x) = x` and
`T_{k+1} = exp ∘ T_k`, is denoted by an expression of depth exactly `k`. Dually, `⟨0, B⟩` denotes
`1 − L(⟦B⟧)`, so one edge also buys a logarithm (with an additive constant). Composing the two,
`⟨⟨0, B⟩, 1⟩` denotes `e/⟦B⟧` wherever `⟦B⟧ > 0`: **a reciprocal costs two edges.** That fact
recurs below.

**The germs are logarithmico-exponential.** By induction on the expression, every `⟦t⟧` agrees
near `+∞` with a function in Hardy's class `𝓛` of logarithmico-exponential functions. The
totalisation does not leave the class: `L` is first-order definable in `ℝ_exp`, and an `𝓛`-germ has
eventually constant sign, so beyond some point `L(⟦B⟧)` is either `log ⟦B⟧` throughout or `0`
throughout. So each expression has a well-defined `𝓛`-germ at `+∞`, and all the usual structure —
`𝓛` is a field, its germs are totally ordered by eventual domination, each is eventually monotone —
is available.

**What totalisation does that matters.** It makes the evaluation map *non-analytic in a way that is
visible in the asymptotics*: an expression whose germ is eventually negative is annihilated by the
`L` above it. Concretely, `⟨0, B⟩` denotes the constant germ `1` whenever `⟦B⟧` is eventually
non-positive, however fast `⟦B⟧` diverges. This is why a "sub-expressions are asymptotically
smaller" intuition is simply false here, and §7 develops the consequence.

Throughout, *eventually* means "for all sufficiently large `x`", and rays start at `x ≥ 1`.

---

## 2. The conjecture

> **Conjecture (uniform approach envelope).** For every `j ∈ ℕ` there exists `k ∈ ℕ` with the
> following property. Let `A` and `C` be expressions with `d(A) ≤ j` and `d(C) ≤ j`, let `X₀ ≥ 1`,
> and suppose
>
> &nbsp;&nbsp;&nbsp;&nbsp;`⟦C⟧(x) < exp(⟦A⟧(x))` for all `x ≥ X₀`.
>
> Then there is `X₁ ≥ X₀` such that
>
> &nbsp;&nbsp;&nbsp;&nbsp;`exp(−T_k(x)) ≤ exp(⟦A⟧(x)) − ⟦C⟧(x)` for all `x ≥ X₁`.

In words: an expression germ that stays strictly below `exp ∘ A` on a ray stays below it *by an
effective envelope*, and the tower height of that envelope depends on the depth bound alone.

**The quantifier position is the entire content.** Read it as `∀j ∃k ∀(A,C)`. The variant with the
quantifiers exchanged —

> for every pair `(A, C)` satisfying the hypothesis there exist `k` and `X₁` such that the same
> bound holds

— is a corollary of classical facts, by the following three lines. The gap germ `exp∘A − C` lies in
`𝓛`; by hypothesis it is positive on a ray, so it is not the zero germ; `𝓛` is a field, so its
reciprocal lies in `𝓛`; and every `𝓛`-germ is eventually dominated by some finite iterate of `exp`.
Applying that to the reciprocal and using `1/u ≥ exp(−u)` for `u ≥ 1` gives the floor, with `k`
depending on the pair. (Amusingly, the expression `⟨⟨0,G⟩,1⟩` for the reciprocal of the gap `G` is
exactly the two-edge reciprocal noted in §1; the syntactic cost `+2` is the shadow of closure under
division.)

**So what is open is the uniformity, and only the uniformity.** Nothing we have found in the
literature supplies it, and §7 records the two nearest misses and why they are misses. If you read
only one paragraph of this note, read this one: we are not asking whether bounded-complexity
exp–log germs can be separated — they can, pairwise, since 1912 — but whether the *rate* of
separation can be bounded in terms of the defining complexity alone.

**It is not "bounded away from zero".** That reading is false on ordinary members of the class:
`exp(1 − x)` and `e/x` are positive on the ray with infimum `0`, and both satisfy the conjecture at
`k = 0`. The conclusion is an envelope, not a positive constant lower bound.

**The strict hypothesis cannot be dropped.** Two expression germs can meet exactly: for any `A`, the
germ of `⟨A,1⟩` is `exp ∘ A` on the nose, so the gap is identically zero. The hypothesis boundary
sits precisely there.

---

## 3. Two equivalent forms, and a warning

Two apparently different statements are provably equivalent to the conjecture. All the reductions
below are machine-checked in both directions.

**Decay floor.** For every `j` there is `k` such that every expression `t` with `d(t) ≤ j` whose
germ is positive on a ray satisfies `exp(−T_k(x)) ≤ ⟦t⟧(x)` eventually. *(One expression, not a
pair — this is the cheapest form to search, since the search space is `|S_j|` rather than
`|S_j|²`.)*

**Growth envelope.** For every `j` there is `k` such that every expression `t` with `d(t) ≤ j`
satisfies `⟦t⟧(x) ≤ T_k(x)` eventually. *(No positivity hypothesis is needed for a ceiling; the
asymmetry with the floor is real.)*

The reductions are cheap because the statements are quantified over all depth bounds: the approach
form follows from the decay form at `j+2` and conversely; the decay form follows from the growth
form at `j+2` at the same tower height, via the two-edge reciprocal; and the growth form follows
from the decay form at `j+3` at height `k+1`. So all three are one debt.

**Warning, and it has cost us a retraction once.** Any "reduction" of the conjecture that lands
inside this cycle is circular. Before believing a simplification is progress, check whether it has a
converse. Several natural-looking reformulations turned out to be two-way re-indexings of the same
statement; one is recorded in §6.

---

## 4. What is known, and it is sharp

**Small depth, proved.** The decay form holds unconditionally for `d(t) ≤ 2` at `k = 0`, and for
`d(t) ≤ 3` at `k = 2`. These are theorems, not measurements.

**A lower bound on `k`, proved, and it grows with depth.** Let `D_m` be the expression denoting
`exp(1 − T_{m+1}(x))`. Its depth is exactly `m + 4`, its germ is positive everywhere, and for every
`x ≥ 1` it lies strictly *below* `exp(−T_m(x))`. So no tower height below `m + 1` serves depth
`m + 4`: at depth `j` the conjecture's `k` must be at least `j − 3`. In particular no single `k`
serves all depths, so the `∃k` genuinely has to be inside the `∀j`.

**An upper bound, numerically, to depth 7.** Over the constant alphabet `{0,1}` the decay
form has been swept **exhaustively** at depth 2 (147 expressions) and depth 3 (21 612 expressions),
maximum required height `0` in both. Depths 4-7 are a beam search over 16 constants and the
variable — 288 910 nodes formed, 78 369 distinct germs — returning maximum heights `1, 2, 3, 4`,
i.e. `j − 3` at every depth. The extremal expression the sweep returns at depth 4 unfolds to
`e·exp(−exp x)` and at depth 5 to `exp(1 − exp(exp x))`: the family `D_m` above, rediscovered by the
search rather than supplied to it. Three controls: `D_0 … D_5` at depths 4-9 must report heights
1-6 and all six fire; the exhaustive depth-≤2 and depth-≤3 rows are reproduced tree for tree by an
instrument sharing no arithmetic with the earlier one; and with the seed families removed the beam
reaches the same heights through entirely different expressions, so the reading is not an artifact
of the seeds. A separate sweep of *pairs* — the form of §2 itself — measured 287 346 pairs and
returned maximum heights `0, 1, 2` at depth bounds 2, 3, 4.

**Two metrics run close together here, they differ by exactly one rung, and the difference is the
whole of what a proof attempt must get right.** The search scores an expression by applying `log`
to `−log ⟦t⟧(x)` until it falls to `x`. In the tail an *additive constant* in the exponent is below
working precision beside `T_{j−3}(x)`, so what the tables above actually measure is the
constant-tolerant reading `−log ⟦t⟧(x) ≤ C + T_k(x)`, and under that reading the value is exactly
`j − 3`. The envelope of §2 carries **no** additive constant. One rung more is needed for it:
`⟨T_{n−1}, e^{−M}⟩` denotes `T_n(x) + M` at depth `n`, so `exp(1 − T_{j−3}(x) − M)` is an expression
of depth `j` whose `−log` is `T_{j−3}(x) + M − 1`, above `T_{j−3}(x)` at **every** `x` and below
`C + T_{j−3}(x)` with `C = M − 1`. Measured with `M` running `0, 1, 5, 50, 10⁶, 10⁴⁰`: the
constant-tolerant height stays at `j − 3` and the strict height is `j − 2`. The pair sweep, which
measures §2's form directly, agrees — `0, 1, 2` at depth bounds 2, 3, 4 is `max(j − 2, 0)`.

**So aim a proof at `k = max(j − 2, 0)` for the conjecture as stated in §2, and do not carry
`j − 3` across the equivalences of §3.** Traversing the cycle costs a rung, which is the same fact
§5 item 6 records from the other side. Neither reading is in doubt as a *value*: `j − 3` is pinned
from below by proof (`D_m`) and from above by measurement wherever measurement reaches, and the
strict form's `j − 2` rests on the separating family and the pair sweep, both numerical. What is
open is not which function of `j` the height is, but that it is a function of `j` at all.

**Why the earlier sweeps could not see this.** Every constant alphabet used before 2026-09-23 lay
inside `{0, 1, 5, 50, 1000}`, on all of which `L(c) ≥ 0` — so no leaf could ever *add* to a germ.
The constants that move the strict reading are exactly those in `(0,1)`, where `L(c) < 0`, and none
was ever present. The instrument's own controls had used `exp(−1)` for years.

**And the measurements' limits, stated because they matter.** The instrument does not represent
values — it represents the iterated-log spine, on which `exp` is a push and `log` a pop, both
exact — so reach is no longer a function of depth: one ray serves every depth, scoring on
`x ∈ [6.18, 2.85 × 10⁶⁴]` and confirming to `x ≈ 4.11 × 10¹²⁹⁴`, with the extremal specimens
re-verified at 40, 200 and 1 000 digits on a ray reaching `x ≈ 3.22 × 10⁷⁰⁶⁸³`. Its error bias is
one-way and a reader should know which way: when a term is absorbed the computed gap is too
*large* and the computed height too *small*, so the search can **miss** a counterexample and cannot
**invent** one. "Exhaustive" above means exhaustive over a two-element constant alphabet, and the
deeper rows are a beam search over sixteen constants; the class allows an arbitrary real constant at
every leaf, and a counterexample requiring a particular transcendental constant is invisible to any
of this. A finite ray cannot certify an asymptotic claim; it can only fail to contradict one. What
the data supports is narrow and we state it narrowly: nothing found so far pushes the required
height up at fixed depth.

---

## 5. What is ruled out — the part that should save you time

Eight families of argument have been closed, each by proof. They are listed not to discourage but
because each is the obvious next idea, and because the residue they leave is sharper than the
conjecture as stated.

The intended proof shape throughout was an induction on the syntax tree: bound the germ of
`⟨A,B⟩` from the bounds on `A` and `B`. Such an induction needs a parameter that strictly decreases
along constructor edges.

1. **No integer-valued measure that decreases into both children can run the argument.** The
   induction step spends one constructor edge; the reciprocal, which is how a ceiling is converted
   into a floor, spends two. The step therefore consumes the envelope one full level above what it
   delivers. Sharp: depth pays `+2` for the reciprocal and size pays `+4`, both with equality.

2. **A measure read off the germ's growth rate fails on the right child, unboundedly.** Let `K_n`
   denote `1 − T_n(x)`, which is an expression of depth `n + 2` whose right child denotes the
   `(n+1)`-fold tower. The node is eventually negative while its right child is astronomically
   large. Totalised `L` is what permits this. So growth does not descend to the right.

3. **Peeling one exponential exposes a precursor gap but raises complexity.** Where `0 < C < exp A`
   one has, pointwise, `C·(A − log C) ≤ exp A − C`: exponentiation cannot manufacture approach, only
   inherit it, up to the factor `C`. But `A − log C` is a difference of expressions one level
   *above* `A` and `C`, since the logarithm costs an edge. The reduction travels up the complexity
   ladder, not down.

4. **Widen the codomain: nothing is gained.** Let `μ` map expressions into *any* set carried by
   *any* well-founded relation, and suppose `μ` decreases strictly into both children. Then `μ`
   cannot also price the two-edge reciprocal at or below its argument — the reciprocal is two
   strict steps *up* (one logarithm edge in, one exponential edge out), and the four-edge
   re-embedding of item 5 is four. The proofs use well-foundedness alone, no arithmetic, so
   lexicographic orders, vectors and ordinal ranks are all covered, as is the variant carrying a
   polarity bit that the logarithm edge flips. Note the precise content: such measures *exist* (the
   pair (exponential height, logarithmic depth) is one); what does not exist is one that also makes
   the reciprocal cheap, and cheapness is what the transfer needs.

5. **Every parameter that factors through the germ is useless, and this is the strongest of the
   six: the class is empty, not merely inadequate.** For any expression `t`, form `exp ⟦t⟧`, then
   cap it as `1 − log(·) = 1 − ⟦t⟧`, then exponentiate again to `exp(1 − ⟦t⟧)`, then cap again to
   `1 − (1 − ⟦t⟧)`. Four constructor edges — two left, two right — and the value has returned to
   `⟦t⟧` *at every real point*, not merely eventually. So if `μ` assigns
   equal values to expressions with equal germs, those four edges close a cycle, and no well-founded
   relation admits it. Consequently: a Hardy-field valuation or comparability class cannot be the
   induction parameter; neither can a well-founded relation on germs (which is a measure, at
   `μ = ⟦·⟧`); nor does restricting the demand to edges where the germs actually differ repair it
   (the four germs around the cycle are pairwise distinct); nor does one-sided descent, guarded or
   not. Unguarded, it dies on a single edge: `⟨0, e⟩` has germ `0`, which is its left child's germ,
   and `⟨0, 1⟩` has germ `1`, which is its right child's, so irreflexivity alone suffices. Guarded,
   it dies on two-edge cycles with a distinct intermediate germ, which the grammar makes easy
   because a node's other child is unconstrained. **The induction parameter, if there is one, must
   read the syntax.**

   Separately, and independently of well-foundedness: the comparability order on this class of
   germs is *not* well-founded. The family `D_m` of §4 is an infinite strictly descending chain of
   comparability classes — an `ω*` — and the index of the descent is exactly the tower height the
   floor needs.

6. **A one-sided syntactic recursion whose step is the peel of item 3 terminates — and its base
   case is the conjecture.** Measure an expression by the length of its leftmost spine. This
   decreases strictly on the left, reads no right child at all, is therefore outside items 4 and 5,
   and is bounded by the depth, so the recursion performs at most `j + 1` peels. It also separates
   the meeting boundary that the measures of item 4 are blind at. It dies twice over. First, its
   parameter is *anti-correlated* with the height the floor needs: `D_m` has leftmost spine 2 for
   every `m` while forcing height `m + 1`, whereas the constant-gap family of §7 — two germs at
   tower height `n+1` whose difference is a constant — has spine `n + 1` while needing height 0.
   So no function of the peel count can produce `k`, which must therefore come
   from the terminal cell. Second, there are exactly two terminal cells and each is provably
   *equivalent* to the conjecture: "no cancellation left" (the target eventually non-positive) is
   equivalent to the growth-envelope form, and "nothing left to peel" (the left germ a single leaf)
   is equivalent to the approach form. **A recursion that stops at either cell has reduced the
   problem to itself.**

7. **Enlarging the class of right-hand germs buys nothing, whatever the class.** Item 6 leaves one
   price unpaid: its merge step multiplies two germs, and the grammar of §1 has no product
   constructor. It *is* payable — the class denoted by these expressions is already closed under
   `+`, `−`, `×`, `exp` and totalised `L` with no hypotheses, being exactly the `exp`/`log` closure
   of `ℝ`, so "the smallest class containing these germs and closed under products" names the class
   we are already in. The merge costs 115 depth levels, one per peel, so a depth-`j` run's
   accumulated right-hand germ is an expression of depth `≤ 116·j` — bounded, hence back inside
   item 6, with a converse. At the right width this is not about products at all: for **any**
   carrier with **any** complexity measure into which these expressions embed with bounded
   complexity, the height-`0` terminal cell implies the conjecture. **The cell quantifies over the
   class, so it grows with the class.** Transseries, Hardy-field completions and valuation rings
   are all covered. Refuse to stop instead, and the parameter that survives the closure is
   germ-invariant — which is item 5.

8. **A well-founded relation on *pairs* `(A, C)` is item 6 in new clothes.** Every earlier mechanism
   measures one expression while the conjecture is about a pair, so this is the most natural
   remaining move. The peel step itself is a well-founded relation on pairs, sending
   `(⟨A₁,A₂⟩, C)` to `(A₁, A₂·C)`; the class of pair measures it decreases is inhabited, and
   item 4 genuinely does *not* transport (the reciprocal is cheap here and nothing follows, because
   the peel never asks for descent into a right child). But its **minimal elements** are exactly
   the pairs whose left expression is a single leaf — item 6's second cell, verbatim — and no sound
   base case can omit them, since
   the peel carries every pair there. The accumulator cannot carry the descent either: the merge
   iterates, so `C, A₂·C, A₂·(A₂·C), …` would be an infinite descending chain. The sharpest reading
   in the programme falls out of this: the standard reduction of the decay form to the approach
   form instantiates the left expression at the single leaf `0` and at nothing else, so **the pair
   measure is zero on the entire obligation** — if a candidate parameter is constant at that leaf,
   it is constant on everything the conjecture reduces to.

**What remains, precisely.** Items 1–4 close measures that descend into both children. Item 5
closes everything germ-invariant, on either side or both. Item 6 closes any recursion whatever
whose terminal cell is one of those two; item 7 closes every enlargement of the germ class, because
the cell grows with the class; item 8 closes every well-founded relation on pairs that the peel
decreases, because its minimal elements are item 6's cell. Untouched: a mutual induction over
(expression, polarity) pairs with *different* relations at the two polarities; a one-sided
syntactic descent whose terminal cell is neither of item 6's — item 6 closes the base case, not the
measure, and the leftmost-spine length survives as a measure; and any argument that is not a
structural recursion on constructor edges, which is where an external theorem would land. Two
further facts bracket the search from both sides: a syntactic parameter and a germ parameter are
not refinements of one another in *either* direction. There are two expressions with the same
four-component syntactic measure and different germs, and two expressions with the same germ and
different measures. So nothing is to be had by making either kind of parameter finer.

---

## 6. Two traps worth naming

**An equivalence is not progress.** Re-indexing depth by the pair (exponential height, logarithmic
depth) looked like a refinement: it descends into both children, and it passes the family of item 2
that kills growth measures. But depth is bounded by the sum of the two components and each is
bounded by depth, so "`k` from the depth bound alone" and "`k` from that pair alone" are the same
statement. Likewise, "there is a tower floor at depth `j`" and "every eventually positive depth-`j`
germ has comparability class bounded below by a tower reciprocal, uniformly in `j`" are the same
statement — the multiplicative constant in the comparability relation is absorbed by one tower rung.

**Closure axioms carry no content.** If one axiomatises an abstract "height" function with the
obvious closure clauses (leaves 0, exponentiation `+1`, logarithm `+0`, subtraction at most the
maximum), then height is bounded by depth in four lines — and the identically-zero height satisfies
every clause while refuting the floor outright. The closure half is free. What is wanted is the
*coarsest germ-invariant height for which a floor still holds*, and that is what a transseries
account would have to supply. It is not the closure.

---

## 7. The obstacles, as mathematics

**Subtraction collapses asymptotic scale arbitrarily.** Fix `n` and a real `c`, and let `P` be the
depth-`n` expression for the `n`-fold tower. The germ of `⟨P, e^c⟩` is `exp(T_n(x)) − c`, and the
germ of `exp ∘ P` is `exp(T_n(x))`: both of tower height `n+1`, with difference *exactly the
constant* `c`, at every point and for every `n`. So the scale of the gap is not a
function of the scale of the operands, and the floor required by a pair is not controlled by the
growth rate of either. Conversely the gap can be identically zero (§2). Any invariant that reads
only the operands' magnitudes is blind here.

**Peeling exposes a precursor gap but raises defining complexity.** Item 3 above. The inequality is
in the right direction and the reduction is real; the cost is one level of complexity per peel, and
the complexity budget is exactly what the conjecture is about.

**Totalised `L` destroys parent-to-child descent.** Item 2 above, and worse: there is an expression
whose germ is `1 − exp(exp x)`, negative at *every* real, so the `L` above it annihilates it as a
function and not merely on a ray. An `⟨A,B⟩` node can therefore be arbitrarily flatter than either
child, at every point.

**Łojasiewicz has the wrong shape, and that is why the envelope is tower-scale.** The classical
separation tool is polynomially shaped, `|f| ≥ c·dist^α`, and that shape provably does not extend to
o-minimal expansions in which `exp` is definable. The tower-scale envelope in §2 was not a stylistic
choice; it is what is left when the polynomial shape is unavailable, and the lower bound of §4 shows
a tower is genuinely needed.

**Effective o-minimality gives the wrong quantity.** Berarducci–Servi's effective o-minimality for
`ℝ_exp` bounds the number of connected components of a definable set computably in the complexity of
a defining formula. That is exactly the right *kind* of syntactic uniformity and the wrong
*quantity*: a component count cannot produce a floor, because `exp(−x)` has no zeros at all and
still has infimum 0. We would be very glad to be told this is the wrong reading.

**What a counterexample is not.** The two ways of making a gap small that a first attempt reaches
for are both satisfied instances of the conjecture, not counterexamples: outrunning the target by
growth (the constant-gap family, which needs height 0 while its operands sit at height `n+1`), and
driving the gap to zero (`exp(1 − x)`, infimum 0, which meets the height-0 floor). A counterexample
would have to be a *family* at fixed depth whose required tower heights are unbounded.

---

## 8. The question

> Let `f`, `g` be distinct logarithmico-exponential germs represented by expressions of bounded
> complexity in the grammar of §1. Is there a complexity-dependent class of transmonomials `M_d`
> such that every nonzero `f − g` eventually satisfies `|f(x) − g(x)| ≥ c·m(x)` for some `c > 0` and
> some `m ∈ M_d`?
>
> Equivalently: **does bounded defining complexity uniformly bound the asymptotic complexity of the
> leading surviving term after arbitrary cancellation?**

Transseries carries the right vocabulary for one half of this — exponential and logarithmic depth of
a term, exponential height of a germ, height rising by one per exponential of an unbounded argument
— *for a transmonomial*. Differences break the correspondence, and that break is precisely this
conjecture. If the answer is known in the transseries or asymptotic-differential-algebra literature
under a formulation we have not recognised, a pointer is worth more to us than a proof.

Three things already learned, offered so that a reader does not spend time rediscovering them:
subtraction may collapse height arbitrarily; peeling an exponential exposes a precursor gap but
raises the defining complexity; and the totalised logarithm destroys ordinary parent-to-child
growth descent.

---

## 9. What an answer is worth, honestly

We would rather you decline for the right reason than engage for the wrong one, so here is the full
accounting.

**If it is proved**, it closes exactly one open obligation in our formal corpus — the three
statements of §3, which are one debt under three names — and with it a per-depth induction that
currently stalls. That is the whole direct payoff. The result it was *intended* to unlock, a lower
bound establishing that the `n`-fold tower has depth exactly `n`, does **not** provably follow: our
own notes record that the reduction from that lower bound to the growth/decay pair is not
established and is not a formality. So there is no proved implication from this conjecture to any
headline result of ours.

**Nothing downstream in software changes if it is proved.** The compiler this corpus serves has no
consumer for the growth envelope — the kernels it compiles are bounded or slow-growing. This was
pre-registered before the relevant machinery was built, and it held. There is no product waiting on
this, no deadline, and no dependency.

**A refutation is worth at least as much as a proof to us**, and possibly more: it would kill all
three forms at once and force a redesign rather than a patch. §7's last paragraph says what shape a
counterexample would have to have.

**And we have not assumed it.** The corpus's standing policy is that this may be adopted as an
explicit axiom only when three conditions hold: it has survived a deliberate falsification attempt,
an external theory supports it or supplies a nearby established theorem, and what it unlocks
justifies the cost in assumed material. By our own assessment the third condition currently fails.
Should we ever assume it, the assumption would be spent on the uniformity alone and never on the
whole statement, for the reason given in §2: the rest is a theorem of 1912.

What we are asking for, in order of usefulness: a theorem, a counterexample, a citation, or a
reason the question is malformed.

---

## Appendix A. Where to check any of this

The formal development is a Lean 4 corpus, `machlib`, branch `poly-euclid-spine`, at commit
`e2de4482`. It is deliberately free of any mathematical library: the reals are an axiomatised
ordered field with exponential and logarithm, which is why the classical per-pair result of §2 is
*not* available inside it even though it is a theorem over the standard reals. Every theorem named
below is machine-checked in that setting, and none of the files named below contains a `sorry`. The
running research note is `EmlGermApproachResearch.md` in the repository root; Lean paths below are
relative to `foundations/`.

The grammar of §1 (the type, its evaluation and its depth) is in `MachLib/SinNotInEML.lean`; the
totalised logarithm is in `MachLib/Log.lean`.

The conjecture and its per-pair weakening are `EmlGermApproach` and `EmlGermApproachPerPair` in
`MachLib/EMLGermApproach.lean`, together with the equivalence `emlGermApproach_iff_decayFloor`, the
non-cancellation lemma `approach_gap_ge_exp_of_nonpos`, the peeling inequality
`gap_ge_target_mul_log_gap`, the exact-meeting witness `exact_meeting_gap_zero`, the constant-gap
family `gapTarget` with `gapTarget_gap` and `gapTarget_meets_floor`, and the decaying-gap witness
`decaying_gap_meets_floor`. The decay and growth forms of §3 are `DecayFloor`
(`MachLib/EMLDecayFloor.lean`) and `GrowthEnvelope` (`MachLib/EMLDecayFloorIsGrowth.lean`), whose
reductions are `decayFloor_of_growthEnvelope`, `growthEnvelope_of_decayFloor` and the two theorems
in `EMLGermApproach.lean`; the two-edge reciprocal is `recipTree`.

For §4: the proved small-depth cases are `decayFloorUpTo_three` (`MachLib/EMLDepth3Rung.lean`) —
height 0 for depth ≤ 2 and height 2 for depth 3. The extremal family is `deepDecay`
(`MachLib/EMLHeightInterface.lean`) with `deepDecay_depth`, `deepDecay_below_floor` and
`floorHeight_of_deepDecay`. The numerical sweeps are `foundations/tools/germ_approach_search.py`
(2026-09-05) and `foundations/tools/germ_tower{,_eml,_search}.py` (2026-09-23, the iterated-log
representation whose reach is not a function of depth); they are **not** machine-checked, and
`EmlGermApproachResearch.md` §6 records seven instrument defects found in building them, each of
which had produced a confident wrong answer first — the seventh being the alphabet hole that hid
the `j − 3` / `j − 2` distinction. One naming caution for anyone reading §4 against the corpus:
`DecayFloor` and `DecayFloorUpTo` as formalised carry **no** additive constant
(`exp (-(towerFn k x)) ≤ t.eval x`), so both named propositions take the `j − 2` number; the
constant-tolerant `j − 3` is the shape of the ladder inputs (`LowerEnvBound`,
`MachLib/EMLDecayLadderStep.lean`, and `Depth3ApproachBelow`, `MachLib/EMLDepth2Form.lean`) and of
what the instrument measures in the tail.

For §5: item 1 is `LadderMeasure` and `recip_not_at_one_step` with
`no_structural_induction_of_cheap_recip` (`MachLib/EMLLadderMeasure.lean`); item 2 is `capNode` and
`tower_height_does_not_descend_right` in the same file; item 3 is `gap_ge_target_mul_log_gap`; item
4 is `WfDescent`, `recip_not_below`, `posEmbed_not_below` and `no_wf_descent_of_cheap_recip`, with
`wfDescent_inhabited` showing the class is non-empty (`MachLib/EMLPolarityMeasure.lean`); item 5 is
`GermInvariant`, `no_germInvariant_wfDescent`, `no_germDescent`, `no_germDescentNe`,
`no_germDescentLeft/Right` and their guarded forms (`MachLib/EMLGermInvariance.lean`), with the
four-edge germ identity `posEmbed_eval` in `MachLib/EMLDecayFloor.lean`, and the non-well-foundedness
of the comparability order is `compLt_deepDecay` and `compLt_not_wf`
(`MachLib/EMLComparability.lean`); item 6 is `lspTree`, `peel_terminates`,
`peel_measure_anticorrelated`, `peelCount_cannot_carry_floor`,
`peelTerminalNoCancel_iff_growthEnvelope` and `peelTerminalConstZero_iff_emlGermApproach`
(`MachLib/EMLPeelRecursion.lean`); item 7 is `mulGen_eval` (`MachLib/EMLRingClosure.lean`),
`eml_eq_expLogClosure` (`MachLib/EMLCharacterisation.lean`) and, in
`MachLib/EMLProductMerge.lean`, `prodClosure_iff_inEML`, `mergeTree_depth_le`,
`peelAccum_depth_le`, `peel_accumulator_bounded`, `peelTerminalAccum_iff_emlGermApproach`,
`terminalCell_of_class_is_the_conjecture` and `no_germInvariant_peel_bound`; item 8 is
`PeelRel`, `peelRel_wf`, `pairDescent_inhabited`, `mechanism_four_does_not_transport`,
`pairMinimal_iff`, `pairDescent_eml_not_minimal`, `pairTerminalCell_iff_emlGermApproach`,
`base_must_contain_constZero`, `pair_peel_induction`, `no_accumulator_descent`,
`no_germInvariant_pair_bound`, `decayFloor_reduction_is_minimal` and
`pairCount_cannot_carry_floor` (`MachLib/EMLPairDescent.lean`). The two bracketing facts at the end
of §5 are `measure_blind_at_meeting` and `polMeasure_not_germInvariant`.

For §6: the two-way re-indexing is `reindexing_is_two_way`; the comparability restatement is
`compLe_floor_of_floor`; the content-free closure axioms are `HeightModel` and `zeroModel`
(`MachLib/EMLHeightInterface.lean`).

**Not machine-checked, and marked as such:** everything in §4 drawn from the numerical sweeps; the
attributions to Hardy, to Berarducci–Servi and to the non-extension of Łojasiewicz, which are
readings of the literature rather than theorems of ours; and the claim in §1 that every expression
germ lies in `𝓛`, which is a routine induction we have argued in prose but not formalised. Where
our internal notes say "every Hardy-field germ is dominated by a finite iterate of `exp`", we have
narrowed the statement here to Hardy's class `𝓛`, where it is correct; it is false for general
Hardy fields, which may contain transexponential germs.
