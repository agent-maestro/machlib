# The EML depth problems — a self-contained statement for a reader from outside

**Who this is for.** A mathematician who does not know this project and has twenty minutes. It
defines one small object, states what is proved about it, and states four things that are not.
Every proved claim names a Lean theorem you can check; every open one is stated so that a negative
answer is as interesting as a positive one.

**What this is not.** Not a survey, not a research programme, and not an argument that the object
matters. It is a problem statement. If the questions look uninteresting, that is a useful answer
and cheaply obtained.

---

## 1. The object

Fix the following grammar of expressions in one real variable.

```
t  ::=  const c   (c ∈ ℝ)   |   var   |   eml t t
```

with the evaluation

```
⟦const c⟧(x) = c        ⟦var⟧(x) = x        ⟦eml A B⟧(x) = exp(⟦A⟧(x)) − log₀(⟦B⟧(x))
```

where **log₀ is the totalised logarithm**: `log₀ y = log y` for `y > 0` and `log₀ y = 0` for
`y ≤ 0`. Depth is the obvious thing: `depth(const c) = depth(var) = 0` and
`depth(eml A B) = 1 + max(depth A, depth B)`.

Two remarks, because both are load-bearing and neither is a convention you would guess.

* **The totalisation is not cosmetic.** It is what lets the grammar generate anything at all
  (`log₀ 0 = 0` turns a right child into a switch), and it is the source of most of the surprises
  below. A statement true for the partial `log` can be false here and vice versa.
* **`const` takes an arbitrary real.** So questions of the form "which constants are reachable"
  are vacuous, and the interesting parameter is the *shape*, not the constants. (This retired a
  whole direction of the project: every real sits at depth 0.)

The single node `exp(A) − log(B)` is a fused exponential-logarithmic gate; the project's interest
in it is that it is the primitive its compiler emits to hardware, and depth is the quantity that
survives compilation to a datapath. You do not need that motivation to read what follows.

---

## 2. What is proved

All of these are machine-checked in Lean 4 with no `sorry`, against an axiomatised ordered field
with `exp` and `log` — *not* a construction of ℝ, and not a real-closed field in the technical
sense; see the caveat in §5. There is no Mathlib in this development. Names are Lean identifiers.

**Exact depth costs.** The reciprocal is expressible and costs exactly four levels:
`inv_x_mem_EML` exhibits `R` with `⟦R⟧(x) = 1/x` for `x > 0`, and `invX4_depth_optimal` certifies
depth 4 as *optimal* — no tree of depth ≤ 3 computes `1/x` on the positives. Translation by a
negative constant costs exactly four as well (`x_plus_neg_c_depth_exact_four`: nothing at depth
≤ 3, something at depth exactly 4). Both are two-sided: a construction and a lower bound.

**Non-representability, at every depth.** `sin` is not in the class at any depth, and the
statement is unconditional — `sin_not_in_eml_any_depth_unconditional`, whose depth argument is
literally unused because the underlying barrier covers all depths at once. Same for `cos`. The
mechanism is a barrier argument, not a zero count; an attempt to route it through zero-counting
was tried and is a recorded dead end.

**A Khovanskii-type zero bound, unconditional at depth 2.** For a polynomial in the chain
`(x, eˣ, e^{eˣ})`, the number of zeros in an interval is bounded by an explicit function of the
degrees: `chain2_khovanskii_bound_explicit` gives `#zeros ≤ invPhi (D_x + 2) (D_y)`. The point of
interest is that the *reducibility witness Khovanskii's argument needs is constructed here rather
than assumed*, so this instance carries no citation of the classical theorem. At general chain
depth the classical bound is still cited as an axiom and is confined to a development nothing
featured uses.

**A refutation, and its replacement.** It is natural to guess that a depth-≤3 expression which
stays below a constant `k` must stay below it by a fixed margin. That is **false**
(`depth_le_three_gap_below_refuted`); the witness is

```
t = eml var (eml (eml var (const 1)) (const e⁻¹))
⟦t⟧(x) = exp(x) − log(e^{eˣ} + 1) = −log(1 + e^{−eˣ})
```

which is negative everywhere and tends to `0`. The correct statement replaces the constant margin
by a decaying floor, and *that* is provable: `depth3ApproachBelow_holds` — a depth-≤3 tree that
dips below `k` on a ray does so by at least `exp(−C − e^{eˣ})`.

**Query complexity of the sign function.** In the associated query model,
`sign_query_cost_bounds_tight` pins `1 ≤ q(sign) ≤ 12`, the upper bound by an explicit term.

---

## 3. What is open

Four questions. The first is the one I would point a visitor at.

### 3.1 Uniform effective approach (the main one)

> **Question.** Fix a depth bound `j`. Is there a single tower height `k = k(j)` such that for
> *every* pair of trees `A, C` of depth ≤ `j` with `⟦C⟧(x) < exp(⟦A⟧(x))` on a ray, the gap
> satisfies `exp(⟦A⟧(x)) − ⟦C⟧(x) ≥ exp(−tower_k(x))` eventually?
>
> Here `tower_0(x) = x` and `tower_{k+1}(x) = exp(tower_k(x))`.

**The whole content is the position of the quantifier.** With `k` chosen *after* the pair, the
statement is a corollary of Hardy's 1912 work on the ordered field of germs of
exponential-logarithmic functions, and this project has proved that version. The open question is
whether `k` can be chosen from the *depth bound alone* — that is, whether the class at each depth
has a uniform effective approach rate.

**Why it is not the obvious thing.** Two natural attacks are already known to be satisfied
instances rather than counterexamples: outrunning the target by growth, and driving the gap to
zero. Both occur in the class and both meet the floor comfortably. A counterexample would be a
*family* at fixed depth whose required height is unbounded, and it is not of either shape.

**Status of the evidence, and what it is worth.** A falsification search was run (2026-09-05;
script, controls and full limitations in the repository). It is best stated in the *equivalent
decay form* — every eventually-positive tree of depth ≤ `j` is bounded below by
`exp(−(C + tower_k(x)))` — because that is a question about one tree rather than a pair, and can
therefore be swept exhaustively rather than sampled:

| depth | coverage | largest height found | `j − 3` |
|---|---|---|---|
| 2 | exhaustive, 147 trees; 905 with wider constants | 0 | 0 |
| 3 | **exhaustive, 21 612 trees** | 0 | 0 |
| 4 | 20 000 random trees, every nonzero reading re-checked on a longer ray | 1 | 1 |
| 5 | 8 000 random trees | 1 | 2 — under-resolved, see below |

**No counterexample, and something slightly better: the extremal family is identified.** A known
construction gives a lower bound of `j − 3` on the height any valid floor must allow. At every
depth this search resolves, `j − 3` is also an *upper* bound, and the tree the sweep returns as
extremal at depth 4 unfolds to exactly that known family — rediscovered rather than supplied. So
the *value* of `k` is not in doubt; an attempt should aim at `j − 3` and not hunt for the constant.

**What it cannot do.** It cannot see far: the ray reaches `x ≈ 13` at depth 3 and `x ≈ 2.2` at
depth 5, because the tower passes 120-digit arithmetic there. At depth 5 that is why the table
under-reports — the instrument runs out, and the row says so rather than being read as evidence.
Positive controls constructed to need a nonzero height do report one, so the search is capable of
failing. **It is weak evidence for the conjecture and no evidence at all against it.**

**Why an answer either way is worth having.** The statement is equivalent, inside this
development, to two others that look different — a decay floor by depth, and a growth envelope by
depth — and the three form a reduction cycle, so a proof or refutation of any one settles all
three. A refutation would be more interesting than a proof: it would exhibit a class of
elementary functions where approach rate is not controlled by syntactic depth, which is the kind
of thing that ought to be false.

### 3.2 A tower lower bound

Whether the depth-`k` tower function requires depth `k` to express, in a form strong enough to be
consumed by the certified-synthesis layer. Equivalent (inside the development) to a statement
about a reduction to sign, which is why it is one obligation rather than two.

### 3.3 Bounded-germ transcendence

Whether a germ of the class that is bounded, and whose reciprocal is also bounded, must be
algebraic over a suitable subfield. The unbounded rates are theorems; a constant is a
counterexample to the naive form; the residue is the bounded case.

### 3.4 A level-set question

Whether a certain one-query class has finite level sets, the level-1 analogue of a proved
level-0 statement. The obstruction is that the natural argument goes through zeros of a function
the development can only bound on an interval, not globally.

---

## 4. What you would need to know to attack any of this

**The obstacles are not analysis, they are representation.** Repeatedly in this project the thing
that unblocked a proof was a normal form or a change of the object, not a heavier estimate. Three
recorded instances: a cancellation problem that fell to a normal form rather than an inequality; a
depth-3 residue whose difficulty was a *representation* of the gap; and the reciprocal question,
settled by noticing that the grammar's totalised `log` restores `+log x` inside a child that
already carries `−log x`.

**Refutations are cheap here and worth trying first.** Two of the statements this development
needed turned out to be false, and in both cases the witness came from first proving a
*trichotomy* — "what is the only shape that can resist?" — and then building the counterexample
out of that shape. That recipe has worked twice and is the first thing I would try on 3.1.

**Numerics will lie to you.** Double precision cannot decide any of these: a 528-configuration
search reached machine epsilon and every one of its ten candidate near-misses was refuted only at
80 digits. A grid will step over singularities. Work in iterated-log coordinates, at 100+ digits,
and evaluate at solved crossing points rather than on a grid.

---

## 5. How to check the proved claims

```bash
git clone https://github.com/agent-maestro/machlib
cd machlib/foundations
lake build                                    # about a minute
lake env lean AxiomLedger.lean                # what the development assumes, listed
tools/check_all.sh                            # every gate, exits nonzero if any fails
```

For a single theorem, `#print axioms MachLib.<name>` prints its exact footprint. The claim
inventory at `foundations/docs/what_is_proven.md` pairs each headline with the command that
checks it, and names what is *not* claimed. The falsification search of §3.1 is
`foundations/tools/germ_approach_search.py`; run it with `controls` first, which is the mode that
proves it can report a nonzero height.

**A caveat worth stating plainly.** This is a Mathlib-free development: the real field, the
exponential and the logarithm are axioms here, not constructions. That base is listed, and every
axiom in it is separately checked to be inhabited by a Mathlib term in a sibling project — so the
axioms are known to be *satisfiable*, not merely disclosed. But if you want a development whose
foundations are constructed rather than assumed, this is not one, and no amount of gate-passing
changes that.
