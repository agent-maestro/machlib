# Changelog

All notable changes to MachLib are recorded here. Format roughly follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). Versions are
release-snapshot identifiers; see the release manifests for the authoritative
per-release status.

## [Unreleased] — 2026-08-13

### A depth-2 `eml` node cannot approximate the identity

`depth_two_eml_not_near_identity`: no `eml A' B'` with `A'`, `B'` of depth ≤ 1 satisfies
`x ≤ ⟦A⟧(x) ≤ x + c` on a ray.

This is the second branch of a depth-3 exclusion, and it needed **no case analysis over shapes**. The
squeeze that arises there — the depth-2 log ceiling forcing `exp x ≤ exp(A x) ≤ exp x + f x + K` —
pins `A x` to within an additive constant of `x`. And that is self-defeating:

* `A x ≤ x + c` plus the right child's log being at most linear forces
  `exp (A' x) ≤ 2x + c + D`, which is **sub**-exponential;
* so `depth_le_one_exp_bounded_or_grows` puts `exp (A' x)` in its **bounded** class;
* so `A x ≤ K − Cl`, a *constant* — contradicting `A x ≥ x`.

The 5×5 shape enumeration I had sketched is unnecessary. The exp gap does the work, because being
near the identity is already too *small* for the growing class and too *large* for the bounded one.

**`var` is the honest boundary.** It approximates the identity because it *is* the identity, which is
why the statement is about `eml` nodes. So for `x²` at depth ≤ 3 the remaining hole is exactly
`A = var`, i.e. ruling out `log (B x) = exp x − x²` for `B` of depth ≤ 2 — a single sub-case rather
than a branch.

Threshold note: the growing branch's ray must be built from `exp T`, not `T`. `T` comes from the exp
gap and may be arbitrarily negative, and `0 ≤ T + exp T` is **false** there — the first draft assumed
it and did not compile.

### First depth-3 exclusion — and `V₂` turns out to be a lower-bound tool

The scale table says the floor/ceiling argument cannot lift the band to depth 3. That is a statement
about **one architecture**. `depth_three_bounded_left_not_superlog` goes around it on the branch
where the floor does not apply at all:

> **No depth-3 node whose left child has a bounded exponential computes a superlogarithmic `f`.**

The idea is that a bounded left child forces the node's size to come entirely from the right child's
log going to `−∞` — that is, from `B` **decaying**. And `V₂` caps how fast a positive depth-≤2 tree
may decay: `−log (B x) ≤ C + log x`. So the node cannot outrun `K + C + log x`, and anything
superlogarithmic is excluded.

**This is the first use of `V₂` for a lower bound.** Every previous consumer used it to build an
upper envelope — `U₃` in particular. That it also excludes was not anticipated when it was proved.

Both branches of the totalisation are handled: where `B x ≤ 0` its log is `0` and the node is just
`exp (A x) ≤ K`, which a superlogarithmic `f` also outruns. The `exp (−C)` term in the evaluation
point is load-bearing there — it is what forces `C + log x ≥ 0` so the `≤ K` cap actually bites.

**Scope: this is one branch of a depth-3 exclusion, not the whole thing.** For `x²` at depth ≤ 3 it
settles the case where the left child's exponential is bounded. The other branch — left child
dominating `exp x` — remains open, and the sketch there is a *squeeze*: the log ceiling forces
`exp x ≤ exp (A x) ≤ exp x + x² + K`, which pins `A x → x` to within `o(1)`. Whether any depth-≤2
tree can approximate the identity that closely is the next question, and it is a finite classification
problem rather than a cancellation one.

### The log ceiling one level up — and it measures why the band stops

`depth_le_two_log_le_exp`: for `B` of depth ≤ 2, `log (B x) ≤ exp x + K` on a ray.

`depth_le_one_log_le_linear` caps a depth-≤1 tree's log at `x + C`, **linear**. One level of nesting
moves the ceiling to **exponential**. That single change is the reason the growth band does not lift
to depth 3, and it is now a theorem rather than an observation:

| | left child's exp floor | right child's log ceiling | can cancel? |
| --- | --- | --- | --- |
| band at depth 2 | `exp x` | `x + C` (linear) | **no — different scales** |
| depth 3 | `exp x` | `exp x + K` (exponential) | **yes** |

Both floors come from the exp-gap dichotomy (`depth_le_one_…` and `depth_le_two_exp_bounded_or_grows`
respectively), so the *floor* lifts cleanly. It is the ceiling that moves, and it moves exactly onto
the floor. The depth-2 band argument works because a node cannot cancel across scales; at depth 3
that protection is gone.

This does not say the band is false at depth 3 — only that this proof architecture cannot reach it,
and precisely where it fails.

### The exp gap holds one level up

`depth_le_two_exp_bounded_or_grows`: for `A` of depth ≤ **2**, `exp (A x)` is either bounded above
on a ray, or eventually dominates `exp x`. The same dichotomy `depth_le_one_exp_bounded_or_grows`
gives at depth 1 — **nothing in between, one level higher**.

It falls out of pieces already present, one per branch. If `exp (A' x)` is bounded by `K` then
`A x ≤ K − Cl` via the log floor, so `exp (A x) ≤ exp (K − Cl)`. If `exp (A' x)` dominates `exp x`
then `A x ≥ exp x − x − C` via the linear log ceiling, and that clears `x` — so `exp (A x) ≥ exp x`.

The second branch needed a **ray**, not a point, so `exp_beats_linear_past` was the wrong tool.
`two_mul_add_le_exp` supplies `x + x + C ≤ exp x` on a ray for any `C`, through
`exp x = exp 1 · exp (x−1) ≥ 4(x−1)` — `exp 1 ≥ 2` and `two_mul_le_exp` on `x−1`, no division.

**This is the left-child brick a depth-3 band argument needs.** It is not the whole argument: the
depth-3 *growing* branch also needs the right child's log bounded, and at depth ≤ 2 that log can
reach `≈ exp x` rather than staying linear, so the two can cancel. That is the genuine obstruction
to lifting the band, and it is a cancellation problem — the first place in the growth front where
the sign/cancellation front's difficulty appears.

### A hand-built `x²` witness at depth 8, against the library's 24

The bottleneck was the constructor library, so this bypasses it. The identity:

```
x² = exp(2·log x),      2·log x = exp(log log x) − log(1/x)
```

works because `log(1/x) = −log x`, so an `eml` node's subtraction **doubles** the logarithm rather
than cancelling it. One node turns `log log x` and `1/x` into `2 log x`; one more exponentiates.
`sqTree_depth : sqTree.depth = 8`, closed `by rfl`.

**Domain, stated up front and not folded into the bracket.** This witness needs `x > 1`, not
`x > 0`, because `exp (log (log x))` recovers `log x` only where `log x > 0`. That is a genuinely
different specification from `x_sq_mem_EML`'s, so the honest statement is:

| specification | lower | upper |
| --- | --- | --- |
| `x²` on `(0,∞)` | 3 | 24 (`mulPos var var`) |
| `x²` on `(1,∞)` | 3 | **8** (`sqTree`) |

The lower bound transfers to the restricted domain — the band's hypotheses are all about arbitrarily
large `x` — but the *witnesses* are not interchangeable, and quoting `3 ≤ d(x²) ≤ 8` without the
domain would be wrong.

**What this says about the library.** A three-fold improvement from one hand construction suggests
the generic combinators are nowhere near depth-optimal, which the `1/x` case already hinted at
(library 6, optimal 4). Whether 8 is optimal for `x²` on `(1,∞)` is open; the gap is now 3 to 8
rather than 3 to 24.

### First depth bracket for an algebraic target — and the constructor library is the bottleneck

`x_sq_not_depth_le_two` instantiates the band at `k = 0`: **no depth-≤2 tree computes `x²`.**
Against the existing witness `mulPos var var`, whose depth is machine-checked at **24**
(`EMLDepthCost.mulPos_var_var_depth`), that gives

```
3  ≤  d(x²)  ≤  24
```

**The gap is the constructor library's, not the lower bound's.** The same combinators build `1/x` at
depth 6 (`invXTree_depth`) where the optimal witness is `invX4` at depth **4** — so they are known to
overshoot by 2 even on the one target whose answer is settled. The measured costs are:

| construction | depth |
| --- | --- |
| `subTree var var` | 4 |
| `addTree var var` | 8 |
| `subGen var var` | 15 |
| `invPos var` | 16 |
| **`mulPos var var`** | **24** |
| `addGen var var` | 34 |
| `mulGen var var` | 54 |

Each generic combinator is built from `logTree`/`expOf`/`negOffset` layers costing `3 + depth` apiece,
and they compose multiplicatively in the worst way.

**So T4 does not get a family of cheap certificates from the band yet, and the reason is precise.**
The lower-bound side is now degree-uniform and free; the *witness* side is where the work moved.
Closing `d(x²)` means finding a witness far below 24, not improving the exclusion. That is a
different kind of problem — construction rather than obstruction — and it is the first time in this
programme the binding constraint has been on the upper bound.

### `exp` beats every fixed power — **one** theorem, not a degree ladder

The obvious route to `x²` at depth ≤ 2 is `exp_beats_quadratic_past`, then `_cubic_`, then
`_quartic_` — the per-example pattern the band theorem exists to escape.

It is avoidable, and the reason is the band theorem's *weak* third hypothesis. It asks only for the
inequality **somewhere large**, so the witness can be **chosen**, and choosing `x = exp w` collapses
the problem: `(exp w)ⁿ = exp (n·w)`, so `xⁿ < exp x` becomes `n·w < exp w` — beating a **linear**
function, which `exp_beats_linear_past` already does for arbitrary real slope.

> `exp_beats_powNat (k C X) : ∃ x ≥ X, 1 ≤ x ∧ x^(k+2) + x + C < exp x`

`n·w` is built additively (`natMul`) instead of by a `Nat → Real` cast, and the witness is never
halved, so **no division enters anywhere** — the corpus's division lemmas are thin and this route
sidesteps them entirely.

`powNat_not_depth_le_two` then excludes `x^(k+2)` at depth ≤ 2 for **every** `k`, as an instance of
the band theorem. The exponent is never inspected in the proof. `x²`, `x³`, … are one theorem.

### Wording corrected: the third hypothesis is *not* "sub-exponential"

Flagged in review, and the correction matters because it makes the theorem **stronger**. The
condition is: for every `C`, there are **arbitrarily large** `x` with `f x < exp x − x − C`. That is
not `f = o(exp x)` — it demands nothing *eventually*, only *infinitely often*, and is strictly
weaker than the usual asymptotic statement. Likewise "unbounded" means unbounded above on every ray,
and "superlinear" means above the identity at arbitrarily large points, not eventually. The module
header now says so, and the headline is stated as **depth-2 intermediate-growth exclusion**, with
`M·x` and `xⁿ` as applications beneath it.

### A depth-2 barrier for a whole growth band, not one example

`mx_not_in_eml_depth_le_2` excludes `M·x`. Reading its proof, **nothing in it is about
multiplication** — it uses only that `M·x` is unbounded, grows faster than `x`, and grows slower
than `exp x`. `superlinear_subexp_not_depth_le_two` states that argument for the band:

> **No `f : ℝ → ℝ` that is unbounded above, eventually above `x`, and below `exp x − x − C` at
> arbitrarily large points is computed by any EML tree of depth ≤ 2.**

Nothing is assumed about continuity, monotonicity, or `f` being given by a formula. Each of the three
hypotheses is consumed by exactly one branch and **each is necessary**:

* unboundedness kills `const`, and the branch where the left child's exponential is bounded — there
  the node is trapped between a constant ceiling and the right child's log floor
  (`depth_le_one_log_lower_at_infinity`);
* "eventually above `x`" kills `var` — without it `f = x` satisfies everything else and sits at
  depth 0;
* sub-exponentiality kills the branch where the left child dominates `exp x`, since the right
  child's log is at most linear (`depth_le_one_log_le_linear`).

`mx_not_depth_le_two_via_band` re-derives the `M·x` case from it with **no reasoning about
multiplication**: the three hypotheses come from `exp t ≥ 1 + t`, `1 < M`, and
`exp_beats_linear_past`. Same pattern as the netlist theorems — the bespoke proof was doing no work
the general argument does not do.

**`x²` does not follow yet, and the reason is a missing lemma rather than a missing idea.** Its
sub-exponentiality hypothesis is `x² + x + C < exp x`, i.e. `exp` beating a *quadratic*, and the
corpus has only `exp_beats_linear_past`. The route that avoids division: prove
`exp (u+u) ≥ (u+u)·(u+u)` from `exp_add` and `two_mul_le_exp`, then choose the witness of the form
`u+u+u+u` so no halving is ever needed.

### `d(T₄) = 4` — `U₃` instantiated, and it needed no changes

`depth_le_three_growth_envelope` was built and then never used. A green build says an abstraction is
*true*, not that it is the one anyone needs, so this spends it: `tower4_not_depth_le_three` is its
first consumer.

**It compiled without touching `U₃`.** That is the result worth reporting — the envelope's shape
(constants `K`, `M`, `N` in those positions, ray `XA + XB + exp (−(K+M))`) turned out to be usable
as stated, including the ray, which had to be met by an explicit evaluation point built from
`exp (K+1) + exp (M−K) + exp (N−K−M)`.

`d(Tₙ) = n` now holds for **n ≤ 4** (`tower_certified_upto_four`), and the proof of the top level
consumes only theorems — `U₂`, `V₂`, `U₃` — with no hand-built input anywhere in the chain.

The tail of `tower3_core` is extracted as `exp_gap_absurd`: a quantity that doubles cannot also be
capped by itself plus a constant. `self_le_exp` and `exp_add_one_doubles` are published from
`private` (visibility only, no new proofs).

### The remaining obstruction is isolated to **one** proposition

`V₂` consumed finiteness of sign changes, discharged at depth 2 by a hand check over five closed
forms. `evSign_of_hard` reduces the general case to a single named statement:

> **`SignHardCase`** — for `A`, `B` and a ray on which `B` is *positive*,
> `exp (A x) − log (B x)` is eventually of constant sign.

> **`evSign_of_hard : SignHardCase → ∀ t : EMLTree, EvSign t.eval`**

So the blocker is now a proposition rather than a vague requirement, and it is exactly the statement
Hardy-field / o-minimality machinery addresses — a difference of log-exp functions is eventually of
constant sign. **That is the question to put to an outside mathematician.**

**Two things fell out of the proof that were not expected.**

* **Totalisation helps rather than hurts.** Where the right child is eventually non-positive its log
  is identically `0`, so the node is `exp (A x)` — *positive*, sign-definite for free. The convention
  that has forced thresholds into statements all through this corpus is what makes this branch
  trivial, and `SignHardCase` needs `B` positive precisely because that is the only branch where the
  totalisation stops helping.
* **The left child is never inspected.** The induction uses its hypothesis only on `B`. Whatever `A`
  does, the node's sign is decided by whether the right child's log is real or totalised away.

`EvSign` is stated as *positive* or *non-positive* rather than positive/negative, because the
totalisation makes `0` an ordinary value: a subtree sitting at exactly `0` behaves like a negative
one.

### `U₃` — the growth/decay pair **iterates**

`depth_le_three_growth_envelope`:

> for `t.depth ≤ 3`, `∃ K M N X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, t x ≤ exp (exp (exp x + K) + M) + N`.

**This is the result the whole Q2 question was about.** `d(T₃) = 3` did *not* show the construction
iterates: its depth-≤2 envelope consumed a **hand-built** depth-≤1 decay bound. `U₃` consumes only
theorems — `depth_le_two_growth_envelope` (`U₂`) for the left child and
`depth_le_two_decay_on_ray` (`V₂`) for the right. One level of nesting still buys exactly one
exponential, and the step is now mechanical rather than bespoke.

The right child needs **both branches of the totalisation**: where `B x ≤ 0` the log is `0` and
contributes nothing; where `B x > 0`, `V₂` caps `−log (B x)` at `C + log x`.

**A trap worth recording, because the first draft got it wrong.** The `log x` term is absorbed into
the exponent via `exp a + exp a ≤ exp (a+1)`, which needs `log x ≤ exp (exp (exp x + K) + M)`. That
is **false** on `[1,∞)` for very negative `M` — the right-hand side can be arbitrarily small. It
becomes true only once `x ≥ exp (−(K+M))`, so that term is carried in the ray and is not padding.
The envelope's ray is now `XA + XB + exp (−(K+M))`.

With `U₃` in hand, `d(T₄) = 4` is reachable by the same argument that gave `d(T₃) = 3`.

### `V₂` is proved — the decay half of the pair now exists at depth 2

`depth_le_two_decay_on_ray`:

> for `t.depth ≤ 2`, `∃ C X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, 0 < t x → −log t(x) ≤ C + log x`.

The twenty-five-cell table analysed in
`monogate-research/exploration/eml_depth_induction_2026_08_13/` is now discharged in Lean, and it
came out as the paper analysis predicted: **one cell decays** (`depth_le_two_V2_log_nonpos`, the
`e^c/x` case), **one is a positive constant** (`A = const α`, `B = const β`), and **the remaining
twenty-three are vacuous on a far enough ray**, each killed by one of the three eventual-largeness
helpers.

**The ray is load-bearing, not a convenience.** Near a point where `t` crosses zero from above,
`t(x) → 0⁺` and `−log t(x) → +∞`, so no fixed `C` survives. The statement holds only because `X₀` is
existentially quantified and can be pushed past the last sign change. That is a **finiteness of sign
changes** requirement — at depth 2 discharged by hand, since each depth-≤1 form crosses zero at most
once at an explicitly computable point. It is what this proof consumes, and it is *not* cancellation
stratification. The module docstring says so at the theorem.

Both halves of the growth/decay pair now exist at depth 2: `depth_le_two_growth_envelope` (`U₂`) and
`depth_le_two_decay_on_ray` (`V₂`). That is the input the depth-3 envelope needs.

Corpus notes: the `A = c − log x` against `log β > 0` cell is the one that needs real work — it dies
because `exp (c − log x) < log β` past `exp (c − log (log β))`, obtained by feeding
`eventually_log_gt (c − log (log β))` through `exp_lt` and `exp_log`. Two identities there
(`c − (c − log (log β)) + …`) need `mach_mpoly`, not `mach_ring`.

### Eventual-largeness helpers — the analytic half of the remaining `V₂` cells

Three lemmas supplying "past an explicit point" for the three unbounded shapes of `log (B x)`:
`eventually_log_gt`, `eventually_log_exp_sub_gt`, `eventually_log_exp_sub_log_gt`. Each returns an
`X₀ ≥ 1` past which `log (B x)` clears a given `K`.

These are what the twenty-three vacuous cells of the decay table need. In each, the left child's
exponential is bounded by some `K` while the right child's log grows without bound, so past `X₀` the
node is negative and the positivity hypothesis cannot fire. They are stated for arbitrary `K` so the
same three serve every cell.

Two details worth keeping. `eventually_log_exp_sub_gt`'s threshold carries **`exp d`, not `d`** —
with `d` in the threshold it fails for arbitrarily negative `d`, which is exactly the case the naive
choice gets wrong. And `exp x − log x ≥ x` (needed for the third) comes from `two_mul_le_exp`
together with `log x ≤ x`, not from any bound on `log` alone.

**This is the analytic half of `V₂`, not `V₂`.** The case assembly — classification on `B`, then the
constant-vs-constant cell — is still to come, so `V₂` as a single theorem still does not exist.

Corpus notes: numerals beyond `0` and `1` have **no `OfNat`** here, so `3` must be written
`1 + 1 + 1` or, better, restructured away — the thresholds above were rewritten to avoid it.
`log_le_id_at_one` exists but sits in `MachLib.EMLTree` and is not in this module's import closure;
`log x ≤ x` is re-derived locally in three lines from `one_add_le_exp` and `log_le_log`.

### `V₂` is not blocked — the decay half survives depth 2, and the worst cell is proved

The question left by `d(T₃) = 3` was whether the **decay** half of the pair can be built at depth 2,
or whether near-cancellation blocks it. Settled on paper first
(`monogate-research/exploration/eml_depth_induction_2026_08_13/`):

> **`V₂` exists and is logarithmic, `V₂(x) = C + log x`.** Cancellation needs two functions that
> approach each other *asymptotically*, and at depth 2 the two sides are too sparse for that:
> `exp (A x)` takes only `{const, eˣ, e^c/x, e^{eˣ−d}, e^{eˣ−log x}}` and `log (B x)` only
> `{log β, log x, 0, ≈x, ≈x}`. The only pair that can agree asymptotically is constant against
> constant, where the difference is itself a constant.

Two theorems land the load-bearing part:

* `depth_le_one_lower_on_ray` — a depth-≤1 tree satisfies `A x ≥ −C − log x` on `[1,∞)`. The
  existing `depth_le_one_lower_bound` covers `(0,1]`; this is the other end, and `−log x` is the
  right comparison because `c − log x` attains it with **equality**.
* `depth_le_two_decay_log_nonpos` / `depth_le_two_V2_log_nonpos` — **the only decaying cell of the
  25**, `log (B x) ≤ 0`, where the value is `≥ e^{−C}/x` and so `−log t(x) ≤ C + log x`. It needs no
  hypothesis on `B` beyond that sign: the decay is entirely the left child's.

**What is proved and what is not.** The worst cell is closed. The remaining cells (`log (B x) > 0`)
are argued on paper — each either grows or is bounded below by a positive constant — but are **not
yet formalised**, so `V₂` as a single theorem does not exist yet.

**A different failure mode surfaced, and it is not the one we were hunting.** `C` is
tree-dependent and **unbounded over trees**: constant-against-constant cancellation is exact on the
locus `exp α = log β`, and near it `C` blows up. The *form* of the bound survives; its
**uniformity** does not. If `C_j` degrades with `j` the envelope weakens even though every `V_j`
exists. That, rather than cancellation per se, is now the thing to watch.

Worth recording how that was found: the locus has measure zero and the numerical probe
(`v2_shape_probe.py`, exhaustive over the 25 *shapes*, a grid over parameters) does not land on it.
It came from reasoning about the table. The probe's own first run reported six "shrinking" cases,
all of which were transients **before** the ray starts — `B = c′ − log x` with `c′ = 3` has not yet
been totalised at `x = 10`.

### `d(T₃) = 3` — the growth/decay pair earns a theorem that was not reachable before

**The V-bound was already proved.** The slate named "an eventual upper bound on `−log(B x)`" as the
missing piece for depth 3. It is `depth_le_one_log_lower_at_infinity`, built during the reciprocal
arm: `∃ Cl X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, Cl ≤ log (B.eval x)`. Both halves of the pair existed; what had
never happened was **using them together**.

`depth_le_two_growth_envelope` (in `EMLDepthTameness`) does that:

> for `t.depth ≤ 2`, `∃ K M X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀, t.eval x ≤ exp (exp x + K) + M`.

At `eml A B` the two children consume *different* halves — the left bounded above by
`depth_le_one_le_exp_shift`, the right bounded **below** by `depth_le_one_log_lower_at_infinity`.
Neither alone suffices: a single upper envelope cannot control `−log (B x)`, which is exactly the
obstruction `LogSafe` ran into. Both constants are earned (`K` is the left child's exponential
shift, `M` the negated decay floor) and the ray is unavoidable, since `c − log x` crosses zero at
`x = exp c`.

`tower3_not_depth_le_two` then gives **`d(T₃) = 3`** — the first tower level beyond what the shallow
classifications already covered, and the first depth in this corpus proved by the pair rather than
by a bespoke case analysis. The argument is short once the envelope exists: a depth-≤2 tree is
capped one exponential above `exp x`, `T₃` sits two above, and the gap closes because
`exp (exp x) ≥ exp x + exp x` puts the tower's outer exponent a full unit clear — and one unit of
exponent is a factor of `e ≥ 2`, which the additive slack `M` cannot absorb.

`d(Tₙ) = n` is now proved for **n ≤ 3** (`tower_certified_upto_three`) and open for `n ≥ 4`.

**This is the first evidence bearing on the all-depth question.** The pair did not merely restate
depth-2 facts — it produced a depth-3 result unreachable from the classifications alone. What it does
*not* yet show is that the construction iterates: the depth-3 case still consumed a hand-built
depth-≤1 decay bound, and a genuine induction needs `V_j` for every `j`, which is where cancellation
stratification (T3) is expected to be required.

Lean notes: this corpus has **no `set` tactic** — the core is stated over a free evaluation point
instead, which also keeps a large repeated term away from the elaborator. `mach_ring` failed on
`M + 1 + 1 = 1 + (1 + (M − K)) + K`; `mach_mpoly [M, K]` closed it.

### The iterated-exponential tower — the infinite family, and the exact price of it

`T₀ x = x`, `T_{n+1} x = exp (T_n x)`. The two depth-2 certificates added earlier today were not
isolated examples: **they are `T₁` and `T₂`.** Seeing that is what makes the family the right object
rather than a generalisation invented afterwards.

The **upper** half is now proved for every `n`. Totalised `log 0 = 0` makes `eml t (const 0)`
exactly `exp ⟦t⟧`, so one `eml` node buys one exponential: `towerTree_depth` gives depth `n` **on the
nose**, and `towerTree_accepted n : Accepted (towerSpec n) (towerTree n) n` holds for all `n`.

The **lower** half is the open problem, and it is now named rather than gestured at.
`TowerLowerBound` is the proposition that no tree shallower than `n` computes `Tₙ`, and
`tower_depth_optimal_of_lower_bound` shows the entire infinite certified family is a **function of
that one input** — witness, depth, acceptance and the hardware transfer are already in place for
every `n`.

**That makes "T4 consumes T2" a theorem rather than a reading.** T4's supply of certified targets is
bounded below by T2's supply of lower bounds, and no amount of checker engineering moves it.

`tower_lower_bound_upto_two : TowerLowerBoundUpTo 2` is discharged from work already done — `T₀`
vacuously, `T₁` by `exp_not_depth_zero`, `T₂` by `expExp_not_depth_le_one`. So `d(Tₙ) = n` is proved
for `n ≤ 2` and open for `n ≥ 3`.

### Two more claims tightened

* **"area destroyed" at the DAG→schedule row was conceptually wrong.** A schedule does not destroy
  area. The precise statement is that **area is not a path invariant** — it accumulates over the
  DAG rather than along the critical dependency chain, which is why the longest-path algebra was
  the wrong tool for it from the start.
* **The `#eval` claim is now scoped to this formal layer.** Numerical checks of EML expressions can
  and do exist elsewhere in the project, in Python and in simulation, and they are useful. The
  narrow virtue is that such a computation **cannot inhabit `Meets`**: within this layer, semantic
  obligations cannot be discharged by executable evaluation.

### Two depth-2 certificates with T2-native lower bounds — the calibration ladder closes

`exp (exp x)` and `exp (exp x) − x` are certified **minimum-depth at 2**. Both lower bounds are one
application of `depth_le_one_le_exp_shift` — the depth-≤1 growth envelope — so for the first time a
certificate is fed by the shallow-tameness kit *as a kit*, with no reciprocal machinery anywhere.

They also exercise the grammar in two ways. `exp (exp x)` uses **totalised log as a construction
tool** rather than a hazard: `log 0 = 0`, so `eml t (const 0)` is exactly `exp ⟦t⟧` and iterated
exponentials cost one level each. `exp (exp x) − x` instead loads *both* children, using
`log (exp x) = x` so the right child does real work.

The pipeline now consumes four different kinds of lower bound:

| target | `d` | lower bound from |
| --- | --- | --- |
| `exp x` | 1 | two-point evaluation on depth-0 trees |
| `exp (exp x)` | 2 | depth-≤1 growth envelope (T2-native) |
| `exp (exp x) − x` | 2 | same envelope, both children loaded |
| `1/x` | 4 | full structural case analysis |

`two_mul_le_exp` was published from `private` in `EMLDepthTameness` (visibility change only, no new
proof); `EMLCertifiedSynthesis` now imports that module directly, which is the dependency direction
the T4-consumes-T2 reading predicts.

**Tactic gotcha, and it is a sharp one: `mach_linarith` is not linarith.** It is a small
`repeat (first | … | apply le_trans | assumption)` combinator. On a `≤` goal carrying an opaque atom
the `apply le_trans` branch spawns a metavariable for the midpoint and diverges — a goal as trivial
as `1 ≤ 1 + exp D` burned the full 200,000-heartbeat budget in `whnf`. It also cannot do linear
arithmetic over hypotheses at all. Both depth-2 lower bounds therefore route their arithmetic
through `private` helper lemmas stated over **plain variables** (`envelope_absurd`,
`envelope_absurd_sub`), proved by explicit `add_le_add_left` / `lt_of_lt_of_le` chains.

### Three claims tightened after outside review

* **"Depth transfers to silicon" was too strong** — and the ×3.55 measurement is why. What is proved
  is that *EML tree depth survives DAG sharing exactly and induces a serial EML-block dependency
  floor on any valid schedule*; tree size does not survive. That is a statement about the
  straight-line EML datapath. `EMLCertifiedSynthesis` now carries a stage table marking tree→DAG and
  DAG→schedule **proved**, and schedule→RTL→mapped **measured**, with the ×1.00 / ×3.55 pair as the
  evidence that the source-level path model stops being exact further down.
* **"Certified-optimal" narrowed to "certified minimum-depth"** wherever it stood alone. Nothing here
  claims a globally optimal FPGA implementation among arbitrary circuits.
* **"Axiomatised reals buy trust" replaced.** Axiomatising the reals *enlarges* the trusted base. The
  real property is structural: axiomatised reals prevent semantic evaluation from masquerading as
  proof — syntactic costs compute, semantic claims must pass through kernel-checked propositions.

### T4 opens: certified EML synthesis, and `1/x` becomes the first certified minimum-depth target

New module `MachLib/EMLCertifiedSynthesis.lean`. The premise of T4 is that the **search is untrusted
and the checker is not** — nothing about how a tree was found appears anywhere in the module, which
is why the programme needs no convergence theorem.

**The trust boundary was already drawn by Lean, not by me.** `EMLTree.depth` is a plain `def` and
`invX4.depth = 4` closes `by rfl` even though `invX4` carries the opaque real `log (log (1 + exp 1))`
— `depth` never inspects the constant. `EMLTree.eval` is `noncomputable` because `MachLib.Real` is
axiomatised, so `#eval` fails on every tree. Both were probed, not assumed. Hence `Accepted` has
exactly two fields: `cost` (kernel-decided) and `meets` (a proof obligation that cannot be omitted,
because acceptance *is* the structure). Note the direction: `rfl` is checked by the trusted kernel,
where `#eval` would run compiled code outside it. The property this buys is *not* "axioms are
trustworthy" — axiomatising the reals enlarges the trusted base. It is narrower and structural:
**axiomatised reals prevent semantic evaluation from masquerading as proof.** Syntactic costs
compute; semantic claims must pass through kernel-checked propositions.

**The acceptance bookkeeping is trivial and is labelled as such.** The content is `DepthOptimal`,
which pairs a witness with a *lower-bound theorem* and so certifies a **minimum-depth** solution
rather than merely a working one. `depth_optimal_value_unique` makes "the minimum depth of `P`" well
defined regardless of which witness a search returned.

`invX4_depth_optimal : DepthOptimal invSpec invX4 4` is the first certified minimum-depth synthesis result
in the corpus. It assembles in three lines because the reciprocal arm already paid for both halves.

**The bespoke hardware theorems turn out to be instances.** `depth_optimal_netDepth_floor` and
`depth_optimal_schedule_floor` are stated for an arbitrary certified spec, and
`inv_x_netlist_depth_ge_four` / `inv_x_schedule_ge_four_L` are re-derived from the certificate with
no mention of reciprocals in either proof. The hand specialisation was doing no work the generic
pipeline does not do.

Scope is in the module header and deliberately narrow: certificates are relative to their exact
spec (an ε-tolerant spec is a different `SemSpec` and inherits none of these bounds), optimality is
in depth only, and the hardware floors are in units of `L` — schedule positions, not nanoseconds.

**A second target, because one instantiation proves nothing.** `exp` is certified depth-optimal at
depth 1 (`expTree_depth_optimal`), chosen to differ from `1/x` on the two axes where a design flaw
in §3 would hide: its lower bound (`exp_not_depth_zero`, a two-point argument on depth-0 trees)
shares no lemma with the reciprocal arm, and `expSpec` is **total** where `invSpec` is restricted to
`0 < x`. `exp_netDepth_floor` then comes out of the generic transfer with no new reasoning. The
certificate is cheap — `exp` is shallow — and that is the point rather than a boast: what was under
test is the pipeline, not the target.

Gotcha re-learned the hard way: **this corpus has no `by_contra` tactic.** `EMLReciprocalDepth2`
records it; I used it anyway and the build caught it. Replaced with a `Nat.lt_or_ge` split.

### The socket caveat gets its second side measured

`EMLNetlistDepth`'s header lists three instantiations of the weighted-cost socket and says only
`we` = cycles is correct. The middle entry — combinational logic levels — was justified by a
**one-sided** measurement: a pipelined 4-chain has path ratio ×1.00, so `4 × 90 = 360` is not the
physical critical path.

forge `3643edf` measures the other side. The identical arithmetic with the pipeline registers
removed gives path ratio **×3.55**. So combinational depth *is* path-additive when nothing breaks the
path, and stops being so the moment a register is inserted.

**That makes it the one contingent instantiation of the three, and the contingency is now measured
rather than argued.** Latency is path-additive unconditionally; area never was; combinational depth
is path-additive exactly when the lowering leaves the path unbroken. The header says this, with the
`×3.55`-not-`×4` gap attributed to cross-boundary optimisation rather than smoothed away.

Prose only — no theorem changed, and none needed to. `netWDepth_eq_wdepth` was always true for
arbitrary weights; what was under-specified was the *side condition on the artifact* under which a
particular weight means what you want.

### Step 2: `MachLib.EMLDepthTameness` — the dependency arrow inverts

The generic theory that fell out of the reciprocal work now lives in its own module, and
`EMLSizeNineShape` imports it as **one application**. Before, the dependency graph said *the generic
theory exists because of the reciprocal problem*; it now says *the reciprocal problem is one
consumer of the shallow-depth theory*.

| | before | after |
|---|---|---|
| `EMLSizeNineShape` | 3,874 | **2,064** |
| `EMLDepthTameness` | — | **1,865** |

53 declarations moved, 36 stayed. Organisation: depth-≤1 classification · growth at `∞` · behaviour
at `0⁺` · the exponential gap · the logarithmic dichotomy · pole obstruction · decay floors ·
exclusions for named functions.

**Two findings from doing it.**

- **It needed a visibility change, not glue lemmas.** Nine helpers were `private`, which is
  module-scoped in Lean 4, so they were invisible across the new boundary. Publishing them was
  correct — each is a general analytic fact — and **no new lemma had to be invented** to keep the
  9-node proofs typechecking. That was the test of whether the abstraction was real.
- **The consumer shrank by 47%, not 90%.** The remainder is genuine reciprocal case analysis. The
  generic layer was about 45% of the file; the case work was always the bulk.

**The claim registry is load-bearing for refactors too.** 16 claims carried
`module: MachLib.EMLSizeNineShape` for theorems that had moved; repointed. A module rename silently
breaks provenance otherwise, and nothing else would have noticed.

`rung2_positive_floor`, `depth_le_one_lower_bound`, `depth_le_one_trichotomy` and
`depth_le_one_right_tetrachotomy` stay in `EMLDepth2InvX` and are **referenced, not restated** — the
module header says so, since one of them was duplicated by accident earlier in this arc.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Split-A right-branching, `ℓ₂ = var`: **dead** — step 1 complete

**`split_a_right_var_absurd`.** The leaf cases fall to the sandwich's lower bound (`exp(exp x − exp K)`
outruns both `q` and `x`); `eml A B` splits by the five-form classification into the slow forms — one
lemma, `right_var_A_slow_absurd` — and the two fast ones, whose brackets take four branches:

| `A` | branch | bracket | finisher |
|---|---|---|---|
| `exp x − d` | `d > exp K` | negative constant | `log_le_neg_double_exp_absurd` |
| `exp x − d` | `d = exp K` | negative, `~ρ/x` | `log_le_neg_double_exp_absurd` |
| `exp x − d` | `d < exp K` | positive constant | `log_ge_double_exp_const_absurd` |
| `exp x − log x` | — | → negative constant | `log_le_neg_double_exp_absurd` |

The `d < exp K` ray start avoids splitting on the sign of `d`: `one_sub_exp_neg_le` gives
`exp K − exp(K − 1/S) ≤ exp K·(1/S)`, so `S = 1 + exp K·(1/(exp K − d))` already forces
`d < exp(K − 1/S)`.

**Honest note on the estimate.** I described this sub-case as "literally instantiation into existing
finishers". It took ~700 lines: each branch needed its own threshold construction, and the assembly
needed the slow-form bound restated three times. The finishers *were* built and did their job — but
"instantiation" undersold it, and the plan was agreed on that description.

`sorryAx` 0; ledger 242 unchanged.

### Instantiating the finishers: shared conversion + two branches

`right_var_value` (`R₂` in closed form on the ray, from the sandwich's positivity) and
`right_var_logB` (`log (B x) = exp (A x) − exp(exp x)·exp(−exp(K − 1/x))`) factor out what all four
fast branches need, so each branch supplies only its bracket bound.

- **`right_var_exp_sub_const_gt`** (`d > exp K`) — bracket is a negative constant
  `exp(−d) − exp(−exp K)`; `ρ·(1/x) ≤ ρ` on `[1,∞)` bridges to the `ρ/x` finisher.
- **`right_var_exp_sub_log`** (`A = exp x − log x`) — bracket `1/x − exp(−exp(K − 1/x))` settles
  negative once `1/x` drops below `exp(−exp K)`; ray start `1 + exp K + 2·exp(exp K)`, and the
  needed `(1/x) + (1/x) ≤ exp(−exp K)` comes from multiplying `x ≥ 2·exp(exp K)` by
  `(1/x)·exp(−exp K)` — no product-inverse identity required.

Also `one_sub_exp_neg_le` (`1 − exp(−u) ≤ u`), the companion to `one_sub_exp_neg_ge`, which will
place the ray start for the `d < exp K` branch **without splitting on the sign of `d`**:
`exp K − exp(K − 1/S) ≤ exp K·(1/S)`, so `S = 1 + exp K·(1/(exp K − d))` suffices.

Two branches remain: `d < exp K` (positive constant bracket, mirror finisher) and `d = exp K`
(boundary, `~ρ/x` via `one_sub_exp_neg_ge`).

`sorryAx` 0; ledger 242 unchanged.

### The mirror: `log (B x)` cannot blow up positive either

**`log_ge_double_exp_const_absurd`.** The `ρ/x` finisher handles the branches where the bracket is
negative. When `d < exp K` the bracket is a **positive constant** instead, so `log (B x)` runs to
`+∞` double-exponentially and the contradiction is with `depth_le_one_log_le_linear`'s *upper* bound
rather than the lower one.

**Because the bracket is constant here — no `1/x` — the argument stays linear**: `exp(exp x) ≥ exp x`
turns `exp(exp x)·ε ≤ x + C` into `exp x ≤ (1/ε)·x + C·(1/ε)`, which `exp_beats_linear_past` refuses.
Reaching for the `ρ/x` shape here would have forced a quadratic comparison for nothing — the
weakest-hypothesis rule cuts both ways, and using a *stronger* shape than the branch needs is its own
mistake.

With this the fast `A`-forms have all three brackets covered: `d > exp K` negative constant and
`d = exp K` negative `~ρ/x` both go to the first finisher, `d < exp K` positive constant to this one.

`sorryAx` 0; ledger 242 unchanged.

### The finisher for both fast `A`-forms

**`log_le_neg_double_exp_absurd`.** With `A` fast, both `exp (A x)` and `R₂ x` are `exp(exp x)` times
a factor, so `log (B x) = exp(exp x)·(γ(x) − δ(x))`. In every surviving branch that bracket is
**negative and at least `ρ/x` in magnitude** — a constant when `d ≠ exp K`, and `~ρ/x` at the
boundary `d = exp K`, where `one_sub_exp_neg_ge` supplies the rate. Either way
`log (B x) ≤ −exp(exp x)·ρ/x`, while `depth_le_one_log_lower_at_infinity` bounds `log (B x)` from
**below**. `exp(exp x)/x` outruns any constant.

**Stating it with the `ρ/x` shape rather than a constant `ρ` is the whole point** — a constant would
handle `d ≠ exp K` and leave the boundary needing its own theorem. The weaker hypothesis costs
nothing in the proof (`exp x ≤ exp(exp x)` absorbs the extra `1/x`) and covers both.

`sorryAx` 0; ledger 242 unchanged.

### …and the three slow `A`-forms cannot reach the sandwich

**`right_var_A_slow_absurd`.** The sandwich says `R₂` is double-exponential. All three slow forms
satisfy **one** bound — `exp (A x) ≤ exp x + K_A`: `const α` and `c − log x` because their
exponentials are bounded, `var` because its exponential *is* `exp x`. A single exponential plus a
constant cannot exceed `exp(exp x − exp K)`, and one lemma covers all three.

The fast forms fail that hypothesis, which is exactly the separation wanted — the lemma's shape does
the case split for free.

The witness clears both requirements at once: `exp_beats_linear_past` at slope 1 with intercept
`1 + exp K + exp(K_A − Cl)` gives `exp x − exp K ≥ x + 1` (so `exp(exp x − exp K) ≥ 2·exp x` by
`exp_succ_ge_two_mul`) **and** `exp x > K_A − Cl`. Folding both thresholds into one intercept is
what keeps it to a single point.

`sorryAx` 0; ledger 242 unchanged.

### Split-A right-branching, `ℓ₂ = var`: `R₂` is double-exponential

**`right_var_sandwich`.** Here `exp x − log (R₂ x) = exp(K − 1/x)`, so
`log (R₂ x) = exp x − exp(K − 1/x)` — and since `exp(K − 1/x)` lives strictly inside `(0, exp K)`,
the log is **sandwiched between `exp x − exp K` and `exp x`**. Exponentiating:
`exp(exp x − exp K) < R₂ x < exp(exp x)`. A double exponential, up to a bounded factor.

**The threshold `1 + exp K` is not cosmetic.** Past it the log is strictly positive, which is what
rules out the totalised branch — below it, `R₂ x ≤ 0` is *not* excluded, because `log (R₂ x) = 0` is
then consistent with the equation. Stating the sandwich at all requires the ray.

This is the structural input for the rest of the sub-case: `exp (A x)` must then match `exp(exp x)`
to within a bounded factor, which the five-form classification allows only for `exp x − d` and
`exp x − log x`, and the surviving branch is pinned by comparing `log (B x)` — at most linear —
against a double-exponentially growing bracket.

`sorryAx` 0; ledger 242 unchanged.

### Split-A right-branching, `ℓ₂ = const p`: **dead**

**`split_a_right_const_absurd`.** `log (R₂ x) = exp p − exp(K − 1/x)` is strictly decreasing, so `R₂`
is **injective**; and once `R₂` is bounded below on a ray, `log (B x) = exp α − R₂ x` is bounded
above there, so `B`'s shape is pinned and `log (B x)` is eventually **constant** — making `R₂`
eventually constant. Injective and eventually constant cannot both hold, and two points show it.

**The lower bound was the only delicate part**, and `right_const_lower` isolates it. `R₂ x > 0` can
fail only where `log (R₂ x) = 0`, i.e. at the single `x` with `1/x = K − p`. Three cases on
`K − p`: positive puts the ray past `1/(K − p)`; zero and negative leave the log strictly *positive*
everywhere, so `R₂ x > 1` on all of `(0,∞)`. In every case the totalised `log` cannot be `0`, so
`R₂ x > 0` and `log (R₂ x) > exp p − exp K` gives the bound.

That single exceptional point is exactly what the ray generalisation was built for last commit, and
it is the first cell where the ray had to start anywhere other than `1`.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The ray generalisation lands whole (3 of 3)

**`depth_le_one_log_bounded_forms_from`** — the forms lemma on an arbitrary ray `[S,∞)`. Split-A
right-branching needs it because `R₂`'s lower bound holds *off a single point*, so the ray has to
start past that point rather than at `1`.

All three unbounded-form witnesses now take an `S`: each adds `exp S` to its construction, which
clears `S` because `S < exp S`. The `[1,∞)` version survives as the `S = 0` instance, so nothing
downstream moved.

**A simplification fell out.** `log_exp_sub_log_unbounded_from` no longer carries its own proof — it
asks `log_exp_sub_const_unbounded_from` for a point past `Λ + 1` at `d = 0`, then uses
`log x ≤ x − 1 < exp(x−1)` and the shared `exp_sub_pred_ge`. Two near-identical proofs became one
plus four lines. Asking the neighbouring lemma for a *stronger* point is what made it work; asking
for the same point does not.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Split-A right-branching: the shape step

**`split_a_right_const_shape`** — with `ℓ₂ = const p` the equation gives
`log (R₂ x) = exp p − exp(K − 1/x)`: bounded above by `exp p` and strictly decreasing. Bounded above
transfers to `R₂` itself — `R₂ x < exp(exp p)` where `R₂ x > 0`, and trivially where it isn't — which
is exactly what `depth_le_two_bounded_left_is_const` consumes. Conclusion: **`R₂` must evaluate to
`exp α − log (B x)` with `α` constant.**

The two leaf cases fall first, and to **different** halves of the setup: `var` to the *bound*
(`x ≤ exp(exp p)` fails at `x = exp(exp p) + 1`), `const q` to the *strict decrease* (a constant `log`
forces `exp(K − 1) = exp(K − 1/2)`). Neither could have used the other's argument, which is a small
reminder that "leaf case" is not one case.

What remains for this sub-case: `R₂ x = exp α − log (B x)` is now **injective** (its log is strictly
decreasing), while `log (B x)` is eventually constant once `B`'s shape is pinned — and eventually
constant contradicts injective. Pinning `B` needs `R₂` bounded *below*, which holds off a single
point where `exp(K − 1/x) = exp p`.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### A `0⁺` tool at last: bounded above ⟹ constant left child

Every lemma in the kit so far works at `∞`. Split-A right-branching needs the other end, and
**`depth_le_two_bounded_left_is_const`** is it: *a depth-2 tree bounded above on `(0,∞)` has a
constant left child.*

Two steps. At `∞`, `exp (A x)` sits under a line, so the exp gap plus
`depth_le_one_exp_bounded_forms` leaves `A ∈ {const α, c − log x}`. At `0⁺` the second dies:
`exp (c − log x) = exp c · (1/x)` blows up while `log (B x)` can only reach `E − log x − 1`, and a
**reciprocal beats a logarithm**. Substituting `x = 1/t`, the contradiction is
`t·(exp c − 1) ≤ M + E − 2`, refuted at `t = 1 + (1 + exp(M+E))·(1/(exp c − 1))`.

**`c_sub_log_blowup_at` separates the point construction from the evaluation** — the first draft
interleaved them and became unreadable. With `t` as a parameter and its two properties as
hypotheses, each half is checkable on its own.

This is reusable across **all four** `(ℓ, ℓ₂)` combinations of split-A right-branching, because each
supplies exactly the hypothesis it wants: `R₂` bounded above.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### `A = var` closes the cell — the limit argument, done without a limit

**`var_family_qpos_A_var_absurd`.** Writing `W := exp(exp x)`, the equation is
`W·(exp(−L) − exp(−1/x)) = λ` once `log (B x)` settles to a constant `L`. The natural reading is a
limit — `exp(−1/x) → 1` forces `L = 0`, then `1 − exp(−1/x) ≈ 1/x` loses to `W`. **Neither step
needs one:**

- **`L > 0` dies at a single point.** `log (B x) < 1/x` holds throughout (add `λ > 0` to the
  right-hand side and reflect through `exp`), so `L < 1/x`, false as soon as `x ≥ 1/L`.
- **`L ≤ 0` dies by an explicit inequality.** **`one_sub_exp_neg_ge`**: `u·exp(−u) ≤ 1 − exp(−u)`,
  straight from `1 + u ≤ exp u` multiplied by `exp(−u)`. At `u = 1/x` that gives
  `1 − exp(−1/x) ≥ exp(−1)/x` on `[1,∞)`; with `exp(exp x) ≥ exp x` the product beats `λ`, and
  `exp_beats_linear_past` at slope `λ·e` finishes.

`log (B x) < 1/x ≤ 1` is also what bounds the log in the first place, so the same inequality that
kills `L > 0` is what lets `depth_le_one_log_bounded_forms` name `B` at all.

**The `ℓ = var`, `q > 1` cell is closed**, and with the earlier `ℓ = const` result **both split-A
left-branching families are complete at 4-of-4**. Remaining in the 9-node map: split-A
right-branching, and split B's `κ > 0` and `leaf = var`.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### `ℓ = var` at `q > 1`: the fast `A`-forms die, `A = var` survives

Here `exp(R₂ x) = exp(exp x − 1/x) + λ` is **not bounded**, so the split-A argument does not port —
its whole engine was boundedness. What survives is an upper bound:
**`R₂ x ≤ exp x + λ`**, because `exp(exp x) + λ ≤ exp(exp x + λ)` (from `exp λ ≥ 1 + λ` and
`exp(exp x) ≥ 1`).

**`var_family_qpos_A_fast_absurd`** turns that into a kill for both fast forms at once, via the
hypothesis they share: `A x ≥ x + 1` past a threshold — true for `exp x − d` (as `exp x ≥ x + x`)
and for `exp x − log x` (as `log x ≤ x − 1`). Then `exp (A x) ≥ 2·exp x` by
`exp_succ_ge_two_mul`, while the cap gives `exp (A x) ≤ exp x + λ + x + C`. So `exp x ≤ λ + x + C`,
which `exp_beats_linear_past` refuses.

**`A = var` is the only survivor**, and it is genuinely different: there `exp (A x) = exp x` exactly,
so the cap is met with nothing to spare and no growth argument applies. Writing
`W := exp(exp x)`, the equation becomes `W·(exp(−log(B x)) − exp(−1/x)) = λ`, which forces
`B x → 1`; each of the five `B`-forms then fails for its own reason, and the `β = 1` case needs
`1 − exp(−1/x) ≳ 1/(2x)` against `W → ∞`. That is a limit argument, not a bound argument, and it is
the piece still missing.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Split-A `q > 1` falls — the kit was the whole job

**`split_a_qpos_absurd`.** `exp(R₂ x) = exp(K − 1/x) + λ` with `λ > 0`, and the argument is pure
assembly over what the last four commits built:

1. `R₂` is **strictly increasing** (`K − 1/x` is; `exp` preserves and reflects order) and **bounded**
   — below by `log λ`, above by `log(exp K + λ)` since `K − 1/x < K`.
2. Bounded above puts `exp(A x)` under a **line**, so the **exp gap** forces the bounded branch, and
   `depth_le_one_exp_bounded_forms` names it: `A ∈ {const α, c − log x}`. Both are **non-increasing**
   — the second because `exp(c − log x) = exp c · (1/x)`.
3. Then `log (B x) = exp(A x) − R₂ x` is bounded above, so `depth_le_one_log_bounded_forms` gives
   `B ∈ {const β, c′ − log x}`, where `log (B x)` is **eventually constant**.
4. Non-increasing minus strictly-increasing is **strictly decreasing**. Two points at `T` and `T+1`
   contradict constancy.

The `2×2` never had to be enumerated: `A`'s two forms collapse to *non-increasing* and `B`'s two to
*eventually constant*, so the finish is one argument, not four. That the exp-bounded and log-bounded
classes coincide — flagged two commits ago — is what makes that collapse available.

**Both split-A left-branching families are now complete**, `ℓ = const` at 4-of-4. New helpers:
`one_div_antitone`, `exp_c_sub_log_eq`, `lt_of_exp_lt`, `qpos_strict_mono`.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The exp side had the same defect — fixed without the round trip

`depth_le_one_exp_bounded_or_grows` has exactly the flaw the log dichotomy had: its bounded branch
says *a bound exists*, not *which tree*. Last round that cost a round trip; this time I looked before
trying to use it.

**`depth_le_one_exp_bounded_forms`** — if `exp (A x) ≤ Kb` on `[1,∞)` then `A` is `const α` or
`c − log x`. Mirror of `depth_le_one_log_bounded_forms`, and — worth noting — **the same two forms
survive on both sides**, though for different reasons: they are the forms whose value is capped
*above*, which caps `exp` directly and caps `log` through monotonicity.

Domination steps extracted as `le_exp_sub_const` (`x ≤ exp x − d` past `1 + exp d`) and
`le_exp_sub_log` (`x ≤ exp x − log x` on `[1,∞)`), both resting on `two_mul_le_exp`. The
point-finder uses `exp_beats_linear_past` at **slope 0**, which is just "`exp x` eventually exceeds
any constant, past any threshold" — a degenerate instantiation, but the right one.

**The composable kit is complete.** Both sides now answer the structural question, not the
existential one:

| | existential | structural |
|---|---|---|
| exp | `depth_le_one_exp_bounded_or_grows` | **`depth_le_one_exp_bounded_forms`** |
| log | `depth_le_one_log_bounded_or_unbounded` | **`depth_le_one_log_bounded_forms`** |

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### A bounded log names the shape — the dichotomy made composable

`depth_le_one_log_bounded_or_unbounded` answers *whether* the log is bounded. The open cells need to
know *which tree that leaves*, and a disjunction over "∃ a bound" does not say. So:

**`depth_le_one_log_bounded_forms`** — if `log (B x) ≤ Λ` on `[1,∞)` then `B` is `const β` or
`c′ − log x`. Exactly two of the five forms, named.

**Refactor rather than a second copy.** The three unbounded forms each need a point past a
prescribed `Λ`, and both theorems need the same three. They are now private lemmas —
`log_var_unbounded`, `log_exp_sub_const_unbounded`, `log_exp_sub_log_unbounded`, plus the shared
`big_point` and the `c′ − log x` cap `log_c_sub_log_cap` — and the dichotomy is five short lines
over them instead of ~90 inline. Net **+28 lines** for a theorem that would have cost ~120 duplicated.

*A statement that answers "is it bounded?" and a statement that answers "then what is it?" are
different theorems, and the second is the one that composes.* Worth noticing one increment after
building only the first.

**Everything the open cells need now exists:** exp gap, log dichotomy, log-bounded-forms, the three
∞ bounds, and the five-form classification. Split-A `q > 1` is case analysis and two-point
evaluation over them. `sorryAx` 0; ledger 242 unchanged; seven gates green.

### The log-side dichotomy — and it is *not* the mirror of the exp gap

**`depth_le_one_log_bounded_or_unbounded`** — for a depth-≤1 `B`, `log (B x)` is either bounded above
on `[1,∞)` or unbounded above.

**Deliberately weaker than the exp gap, because the log side has three growth classes, not two:**
bounded (`const β`, `c′ − log x`), **logarithmic** (`var`), and **linear** (`exp x − d`,
`exp x − log x`). So there is no "bounded or dominates" statement to make — `var` is unbounded yet
dominates nothing. Writing the mirror would have been false, and the shape of the theorem is the
finding as much as its content.

Both unbounded branches share one step, **`exp_sub_pred_ge`**: `exp (x−1) ≤ exp x − exp (x−1)`,
because `exp 1 ≥ 2`. That gives `exp (x−1) ≤ B x` once the subtracted term is under `exp (x−1)` —
which holds for `d` past a threshold and for `log x` always, since `log x ≤ x − 1 < exp (x−1)`. Then
`log_le_log` delivers `x − 1 ≤ log (B x)`.

The `c′ − log x` bound needed care in the small-`c′` regime: `log c′ ≤ c′ + 1` holds for every
`c′ > 0` but by two different arguments either side of `1`, and the totalised branch contributes `0`,
so the cap must be non-negative as well as above `log c′`.

**The kit for the remaining cells is now complete.** Split-A left-branching `q > 1` reduces to `R₂`
bounded and strictly increasing; the exp gap forces `A` bounded, this forces
`B ∈ {const β, c′ − log x}`, and the four surviving combinations are eventually constant or
decreasing. `sorryAx` 0; ledger 242 unchanged; seven gates green.

### A gap theorem: depth-1 exponentials are bounded, or they dominate `exp x`

**`depth_le_one_exp_bounded_or_grows`** — for a depth-≤1 `A`, either `exp (A x)` is bounded on
`[1,∞)`, or it eventually dominates `exp x`. **Nothing sits in between.**

This is the structural fact behind every `M·x` case: the split into `mx_A_bounded_absurd` and
`mx_A_grows_absurd` *was* this dichotomy, discovered case by case and never stated. The two bounded
forms are `const α` and `c − log x`; the three growing ones are `x`, `exp x − d`, `exp x − log x`.
There is no depth-1 tree whose exponential grows, say, **linearly** — which is precisely why `M·x` is
unreachable at depth 2, and the reason is now a theorem rather than five separate arguments.

It belongs to **T2** as much as to the 9-node map: "how does behaviour vary with depth" is exactly
this kind of statement, and a gap is a stronger answer than a bound.

**What it unlocks, and what is still missing.** The next open cell (split-A left-branching, `q > 1`)
reduces to: `exp(R₂ x) = exp(K − 1/x) + λ` with `λ > 0`, so `R₂` is **bounded and strictly
increasing**. The gap theorem forces `A` into the bounded class; finishing needs the **log-side**
companion — *for depth-≤1 `B`, `log (B x)` is either bounded above on `[1,∞)` or unbounded above* —
which then forces `B` into `{const β, c′ − log x}`, and in all four surviving combinations `R₂` is
eventually constant or decreasing, contradicting strict increase. That companion is not built yet.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The `−log x` cell CLOSES — split B's `κ = 0` is dead

The last surviving case was right-branching with `ℓ = var`, where `log(L₂ x) = exp x + log x` forces
**`L₂ x = x·exp(exp x)`** — a double exponential *multiplied by `x`*, and that extra factor is the
whole obstruction.

- **`depth_le_one_le_exp_shift`** — a depth-≤1 tree is under `exp x + D` on `[1,∞)`. The
  value-level companion to `depth_le_one_log_le_linear`, which bounds its *logarithm*.
- **`x_mul_exp_exp_not_in_eml_depth_le_2`** — hence `exp(A x) ≤ exp D · exp(exp x)`: a **constant**
  multiple of `exp(exp x)`. The target needs an `x`-growing multiple, and `x` outruns any constant.

So **every branch of split B's `κ = 0` cell is now dead**, and with it the question *can a depth-3
tree compute `−log x`?* — **no**. That was the sharpest open cell in the 9-node map.

The three ∞-side lemmas turn out to be a complete kit for this family: `log(B x) ≤ x + C` caps a
logarithm from above, `Cl ≤ log(B x)` caps it from below, and `A x ≤ exp x + D` caps the value. Every
kill in the last two sessions used exactly one or two of them.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The κ-trichotomy is a comparison with Ω — and the locus taxonomy closes

`κ = 0` **is** the Ω point. `EMLDepth2InvX` splits the depth-2 cancellation analysis three ways on
`κ := G − exp(−G)` — `kappa_pos_floor`, `kappa_zero_floor`, `kappa_neg_absurd` — and as written that
is a case split on an **opaque inequality between transcendentals**, with nothing saying which branch
fires when.

- **`kappa_strict_mono`** — `κ` is strictly increasing in `G`: `G` rises while `exp(−G)` falls.
- **`kappa_sign_by_omega`** — so the trichotomy is a comparison with a **single explicit constant**:
  below Ω the negative branch, at Ω the degenerate one, above Ω the linear floor.

Since Ω is caged in `(e⁻¹, 1)`, every `G ≥ 1` sits in the `κ > 0` branch — which is exactly why
`A = var` (where `G = 1`) never reaches the hard cases. That was previously a remark in a docstring;
it is now a consequence.

**The taxonomy closes, and the answer is not always a curve:**

| locus | shape | solved by |
|---|---|---|
| `exp(exp c₀) − exp(exp c₁) = 1` | **transcendental graph** over one parameter | `invX4gen_locus_is_a_graph` |
| `exp(−G) = G` (κ = 0) | **single transcendental constant** | `omega_point_is_a_single_caged_value` |
| `exp c = log β` (γ = 0) | **elementary graph**, `β = exp(exp c)` | `gamma_zero_locus` |

All three accidental loci in the arm are now solved. `sorryAx` 0; ledger 242 unchanged.

## [Unreleased] — 2026-08-11

### The Ω point solved completely — the degeneracy is real and isolated

Second T3 locus. `depth_le_one_trichotomy`'s third branch carries a clause conditional on
`exp (−G) = G` — the **Ω point**, `G·exp G = 1` — and it is where the linear floor degenerates and
the quadratic one is needed. It had only ever appeared as a hypothesis nobody had solved: it was not
known whether the degenerate case **occurs**, nor whether it could occur more than once.

- **`omega_point_bracket`** — every positive solution lies strictly inside `(e⁻¹, 1)`.
- **`omega_point_unique`** — at most one, because `exp(−G)` decreases while `G` increases.
- **`omega_point_exists`** — at least one, by IVT on `G ↦ G − exp(−G)`, negative at `e⁻¹` and
  positive at `1`. Uses `intermediate_value_of_hasDerivAt`, which needs only *some* derivative to
  exist — so the derivative never has to be computed.

**So the degeneracy is real and isolated: exactly one parameter value in the whole positive line.**
That is why the quadratic floor could not be avoided — it is not defending against an empty case —
and why no perturbation argument reaches it.

`omega_point_is_a_single_caged_value` packages all three. `sorryAx` 0; ledger 242 unchanged.

### T3, first artifact: an exceptional locus solved for exactly

`MachLib.EMLExceptionalLocus`. The arm keeps producing exceptional sets **by accident**, and it has
cost something — a 12,208-sample grid reported non-existence and missed a witness living on one. The
repair is to solve for them deliberately, and the template is: **prove the behaviour is equivalent to
an equation, then solve the equation.**

`EMLDepth2InvX` already had the *sufficient* direction (`invX4gen_eval`) and *existence*
(`invX4gen_witness_for_any_c1`). Neither makes a locus — only a supply of witnesses. What was missing
is **necessity**:

- **`invX4gen_iff`** — the depth-4 family computes `1/x` **iff** `exp(exp c₀) − exp(exp c₁) = 1`.
  The forward direction needs a **single point**, `x = 1`, where `log 1 = 0` collapses every branch.
- **`invX4gen_locus_unique`** — at most one `c₀` per `c₁`: the locus is a **graph**, not a region.
- **`invX4gen_locus_solved`** — and exactly one, `c₀ = log (log (1 + exp (exp c₁)))`. The locus is
  that explicit transcendental curve, nothing more and nothing less.
- **`invX4gen_off_locus`** — every other pair fails. This is what makes the grid failure
  **inevitable rather than unlucky**: the good set is a graph over one parameter, so sweeping `c₀`
  independently misses it unless a sample lands on the curve exactly.

`invX4gen_locus_is_a_graph` packages existence + uniqueness + the explicit formula.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Constant generation is vacuous in EML — proved, not argued

A research direction was proposed twice on the grammar `S → 1 | eml(S,S)`: *which irrational
constants are EML-representable, and how compactly?* MachLib's grammar has
`const : Real → EMLTree`, so `π` is `EMLTree.const π` — **depth 0, size 1**.

**`const_generation_is_vacuous`** states it as a theorem rather than a remark, because the refutation
is one line of the definition and should be checkable rather than debated. Every real is
representable, all at the same minimal cost, so the question orders nothing. `i` is out of scope
entirely: `eval` is `Real`-valued.

**Where the question does have content:** `EMLTree.unitOnly` restricts constants to `0` and `1`.
Then `e` is depth 1 / size 3 (`e_mem_unitOnly`) and `e − 1` is depth 2 / size 5
(`e_sub_one_mem_unitOnly`) — both leaning on the **totalised** `log`, which is what makes the depth-1
leaves usable rather than undefined. A different language from the one the rest of the corpus
studies; a side laboratory, not the main programme.

Research slate reorganised and written up:
`monogate-research/exploration/inv_x_termination_route_2026_08_06/RESEARCH_SLATE_T1_T4.md` — T1
compilation invariants (producing), T2 quantitative tameness by depth, T3 exceptional-locus geometry,
T4 certified synthesis with an untrusted searcher. Every claim in it names a theorem or is marked
open. `sorryAx` 0; ledger 242 unchanged.

### `M·x ∉ EML₂` — the gap question closes, and with it a 9-node branch

**`mx_not_in_eml_depth_le_2`**: for every `M > 1`, no depth-≤2 tree computes `M·x`. All five
`A`-forms fall — `var` and the two fast forms (`exp x − d`, `exp x − log x`) to
`mx_A_grows_absurd`, `const` and `c − log x` to `mx_A_bounded_absurd`. **`M = 1` is genuinely
excluded**: `var` computes `1·x` at depth 0, so the strict inequality is not slack.

The two fast forms needed one growth fact, `two_mul_le_exp` (`x + x ≤ exp x` on `[0,∞)`, from
`exp x = exp 1 · exp(x−1) ≥ exp 1 · x ≥ 2x`) — no calculus, and it gives both `exp x − d ≥ x` past
`1 + exp d` and `exp x − log x ≥ x + 1` past `1`.

**Stated on `[1,∞)`, not `(0,∞)`** — a strictly stronger theorem, and the reason is not cosmetic: it
dodges the wrinkle the totalised `log` creates downstream, where `log(L₂ x) = exp p + log x` only
forces `L₂ x > 0` away from `x = exp(−exp p)`, which is `< 1`.

**`neg_log_right_const_absurd`** then kills the branch that motivated all of it: the `−log x` cell's
right-branching `ℓ = const p` case needs `L₂ x = M·x` with `M = exp(exp p) > 1`, which is now
impossible. `mx_mem_EML` builds `M·x` at depth 4 and this shows depth 2 does not suffice.

**What survives of the `−log x` cell is one case**: right-branching with `ℓ = var`, where
`log(L₂ x) = exp x + log x` forces `L₂ x = x·exp(exp x)` — not a linear function, so none of this
transfers to it.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### The mirror at `∞`, and the bounded-`A` half of `M·x`

**`depth_le_one_log_lower_at_infinity`** — a depth-≤1 tree's logarithm is bounded **below**
eventually. Each form carries its own threshold (`c − log x` only crosses into the totalised branch
past `exp c`; `exp x − d` only clears `1` past `exp d`), but past it the bound is uniform, and in
four of the five forms it is simply `0`.

**`mx_A_bounded_absurd`** covers both bounded `A`-forms in **one** statement — `const α` with
`K = exp α`, `c − log x` with `K = exp c` — because the only thing the argument uses is the bound:
`M·x` is unbounded and `K − Cl` is not. The witness point is `X₀ + (1 + exp(K−Cl))·(1/M)`, chosen so
that `M·x = M·X₀ + (1 + exp(K−Cl))` lands above `K − Cl` by `lt_one_add_exp`.

**`M·x ∈ EML₂?` now has three of five `A`-forms closed** — `var` (via the `∞` upper bound),
`const`, and `c − log x` (both via this) — plus the `B = exp x` shape. Remaining: the two
fast-growing forms `exp x − d` and `exp x − log x`, where `exp(A x)` must be bounded *below* by
`exp x` past a threshold and then run against the same linear cap.

`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Growth at `∞`: a shallow `log` cannot beat linear

Every bound in `EMLSizeNineShape` lived on `(0,1]`; the remaining `M·x` shapes need the other end.

**`depth_le_one_log_le_linear`** — for a depth-≤1 `B`, `log(B x) ≤ x + C` on `[1,∞)`. All five closed
forms, including the totalised branches where `B x ≤ 0` and the log is `0`. The `exp x − d` case
avoids needing `log_mul` via `exp_sub_le_exp_shift`: `exp x − d ≤ exp(x + exp(−d))` for `x ≥ 0`,
because `exp(e) ≥ 1 + e` and `exp x ≥ 1`.

That is what converts `exp(A x) − log(B x) = M·x` into `exp(A x) ≤ (M+1)·x + C`, where
`exp_beats_linear_past` finishes any `A` that grows. First application:
**`mx_A_is_var_absurd`** — `M·x` is out of reach when the left child is `var`, for **any** depth-≤1
`B` with no case analysis on `B` at all. That the `B` side needs no cases is the point of having the
`∞` bound rather than arguing shape by shape.

The `M·x` cell now has its `A = var` and `B = exp x` shapes closed. What remains there are the
`A`-forms that grow faster (`exp x − d`, `exp x − log x`) and the two that stay bounded
(`const`, `c − log x`) — the latter needing a *lower* bound on `log(B x)` at `∞`, which is the
mirror of what landed here and is not yet built.

`sorryAx` 0; ledger 242 unchanged.

### The splitter census: stop waiting for the next shape to bite

Two statement shapes broke the claim auditor's arrow-splitter today, and the second landed *after*
the "cover input shapes, not claim count" lesson was written down — because the first fix was patched
per-connective instead of generalised. Rather than add a third canary and wait, the shape question is
now **audited over the corpus on every run**.

**`hypothesis_scope_violations`** — an extracted hypothesis containing a **depth-0 binder** is always
a splitter bug and never a real hypothesis: the pretty-printer parenthesises higher-order
hypotheses, and telescope binders are stripped before hypotheses are collected. So a `∀`/`∃` still at
depth 0 inside a hypothesis means the antecedent chain was cut *inside* a binder body. Decidable from
the printed form.

It runs for **every registered claim**, not only those declaring `hypotheses_count` — `statement_of`
is now memoised, so the census is free. **0 violations across all 75 claims.**

**`canary 12`** proves the census would have caught both historic bugs rather than merely agreeing
with today's code: it restores each prior behaviour in turn — no guard at all, then the `∃`-only
patch that fixed the first bug and left the second — and requires violations to appear in each.
Specimens drawn from **historical faults, not invented ones**.

`sorryAx` 0; ledger 242 unchanged; seven gates green; 12 canaries; 75 claims.

### Depth-≤1 has exactly five closed forms — and `+log x` is not one of them

`depth_le_one_classification`: a depth-≤1 tree is **constant**, `x`, `c − log x` (`c > 0`),
`exp x − d`, or `exp x − log x`. Nothing else. The existing `depth_le_one_trichotomy` and
`depth_le_one_right_tetrachotomy` give *inequalities*; the remaining 9-node cells need to know what a
subtree **is**, not what it is bounded by.

**What the list does not contain is the useful part: `+log x`.** Only `c − log x` appears. Hence
`log_plus_const_not_depth_le_1` — **`k + log x` is unreachable at depth ≤ 1, for every `k`** — which
follows uniformly from `depth_le_one_lower_bound`: all five forms stay above a constant near `0⁺`,
and `k + log x` does not.

`mx_B_is_exp_absurd` applies it to the `M·x ∈ EML₂?` cell. When the right child is `exp x`,
`log(exp x) = x` **exactly**, so the equation forces `exp(A x) = (M+1)·x` — and `exp(A x) ≥ exp F` on
`(0,1]` while `(M+1)·x` can be driven below `exp F` (at `x = 1/(1 + (M+1)·exp(−F))`, where the
inequality reduces to `0 < exp F`).

**A duplicate caught and removed.** I rebuilt `depth_le_one_lower_bound` from scratch before
discovering it already exists in `EMLDepth2InvX`, with the same insight in its docstring. Reused
rather than kept. I had grepped before starting the `M·x` cell — for *results about linear
functions*, which is what I expected to need — and not for the lemma the proof actually turned out
to want. **Grep for the tool at the point you reach for it, not only when planning.**

**And the claim auditor's arrow-splitter broke again, on a new shape.** A five-way classification
ends in an unparenthesised `∀` disjunct; the splitter walked into it and reported 2 hypotheses
instead of 1. Same defect class as the existential-conclusion bug fixed earlier today, so the guard
is now general: **while scanning for a top-level `→`, abort on any depth-0 binder seen first** — the
leading telescope has already been stripped, so a binder still reachable at depth 0 is nested.
`canary 11` added.

Two shapes have now bitten in one day — existential conclusion, disjunctive conclusion — and both
were one specimen away. That is the "cover input SHAPES, not claim count" lesson arriving twice.

`sorryAx` 0; ledger 242 unchanged; seven gates green; 11 canaries; 75 claims.

### The `−log x` cell halves — and becomes a gap question about `M·x`

The sharpest open cell (split B, `κ = 0`) asks whether a depth-3 path computes `−log x`. Its
**left-branching half is free**, and one case is a one-liner. Writing `L = eml L₂ (leaf)`:

- `leaf = var` → `exp(L₂ x) − log x = −log x`, i.e. **`exp(L₂ x) = 0`**. Immediate
  (`neg_log_left_leaf_var_absurd`).
- `leaf = const q` → `exp(L₂ x) = λ − log x`, negative past `x = exp(λ+1)`
  (`neg_log_left_leaf_const_absurd`, every `λ`, so the totalised `log q = 0` case is included).

**`neg_log_path_is_right_branching`** assembles these: a depth-3 path computing `−log x` must carry
its *leaf on the left*. So the cell reduces to `log(L₂ x) = exp(ℓ x) + log x`, and for
`ℓ = const p` that is exactly **`L₂ x = M·x` with `M = exp(exp p) > 1`**.

**`mx_mem_EML` already builds `M·x` at depth 4.** So this cell is now a *gap* question about a named
function with no free structure left: **`M·x ∈ EML₄` — is it in `EML₂`?** That is a sharper and more
answerable question than the one it came from, and it connects the 9-node problem to `witT`, which
the arm already understands.

**Worth flagging as a correction of my own expectation.** I had classified this cell as
sign-consistent and therefore expensive. Half of it was free, and I only found that by checking
rather than trusting the triage rule's verdict. The rule predicts *where machinery is needed*; it
does not license skipping the cheap check. `sorryAx` 0; ledger 242 unchanged.

### Split B opens, and the 9-node map is now complete

`split_b_leaf_const_neg_absurd` — in split B (`t = eml L (leaf)`) the equation is
`exp(L x) = 1/x + κ`, so **the pole sits under an `exp` rather than a `log` and none of the split-A
arguments transfer**. The triage rule still finds the free cell instantly: `exp` is positive and
`1/x + κ` is not, once `1/x` drops below `−κ`. Dead by sign, any depth.

Full map written up: `monogate-research/exploration/inv_x_termination_route_2026_08_06/RESULT_NINE_NODE_MAP.md`.
**5 cells closed.** Both left-branching split-A families 3-of-4; split B 1-of-4; the right-branching
depth-3 paths untouched (and sign-consistent, so they will cost machinery).

**The sharpest open cell is split B with `κ = 0`**, which asks exactly: *can a depth-3 tree compute
`−log x`?* That is a clean membership question about a named function rather than a family with free
parameters, which makes it the right one to hand to someone.

Also recorded there: `1/x + log x > 0` for all `x > 0` (minimum `1` at `x = 1`), so split B's
`leaf = var` cell has **no** sign kill available — worth knowing before someone spends an hour
looking for one. `sorryAx` 0; ledger 242 unchanged.

### The triage rule predicts a family it wasn't derived from — `ℓ = var` closes 3 of 4 too

Generalised the pole obstruction and swept the second family. **`no_pole_at_depth_le_2`**: no
depth-≤2 tree can be *capped* by `C − 1/x` near `0` — stated as an upper bound rather than an
equation, so it applies wherever a pole appears however it is dressed.
`shifted_inv_not_in_eml_depth_le_2` is now a three-line corollary.

Two reusable primitives separate the trivial contradiction from the per-branch work of exhibiting a
point: **`exp_sub_log_absurd`** and **`exp_add_absurd`**. Worth noting the second does **not** need
the `0 < μ` one expects — `exp > 0` alone does it. With those, each branch is a few lines.

**`ℓ = var`, left-branching, reproduces the table exactly:**

| `leaf₂` | `log(leaf₂)` | status |
|---|---|---|
| `var` | `log x` | **dead** — `var_family_leaf_var_absurd`, sign |
| `const q`, `0 < q < 1` | `< 0` | **dead** — `var_family_leaf_const_neg_absurd`, sign |
| `const q`, `q = 1` or `q ≤ 0` | `= 0` | **dead** — `var_family_leaf_const_zero_absurd`, pole bound |
| `const q`, `q > 1` | `> 0` | **open** |

**The triage rule predicted which cell would cost anything, in a family it was not derived from.**
That is the reason to trust it for the rest: *check the sign first; buy a growth argument only where
the signs agree.* Both left-branching families are now 3-of-4 closed, by the same three arguments in
the same three positions.

Still open: the `> 0` cell in both families, the right-branching depth-3 paths, and all of split B.
`sorryAx` 0; ledger 242 unchanged; seven gates green.

### Two more 9-node branches, closed by sign alone — and why the third needed machinery

`split_a_leaf_var_absurd` and `split_a_leaf_const_neg_absurd`. **Neither takes a depth hypothesis**:
they hold for *any* subtree. With the earlier pole argument, the left-branching sub-family of split A
now stands at three of four cells dead:

| `leaf₂` | `log(leaf₂)` | status |
|---|---|---|
| `var` | `log x` | **dead** — sign, *any* depth |
| `const q`, `0 < q < 1` | `< 0` | **dead** — sign, *any* depth |
| `const q`, `q = 1` or `q ≤ 0` | `= 0` | **dead** — `shifted_inv_not_in_eml_depth_le_2`, needs depth 2 |
| `const q`, `q > 1` | `> 0` | **open** |

**The pattern is the finding.** Only one of the three needed machinery. The other two collapse
because their right-hand sides go negative near `0` while a left-hand `exp` cannot. The
`log(leaf₂) = 0` case is exactly the one whose right-hand side stays *positive* — no sign clash
exists, so the pole must be chased through the growth bound, which is why
`depth_le_two_log_decay_floor` had to be built at all. **A case needs machinery precisely when it is
sign-consistent**, and that is a usable triage rule for the remaining branches: check the sign first,
and only reach for a growth argument where the signs agree.

Still open: the `q > 1` cell, the right-branching depth-3 paths, `ℓ = var`, and all of split B —
where `exp(L x) = 1/x + κ` puts the pole inside an `exp` rather than a `log`, and none of these
arguments transfer. `sorryAx` 0; ledger 242 unchanged.

### `s(1/x) = 9?` becomes a finite question about PATHS — and one branch closes

`MachLib.EMLSizeNineShape`. The last open integer in the reciprocal arm is now known to be about the
*tree encoding* only, which makes it a clean self-contained problem. This makes "finite" concrete.

- **`minimal_size_isPath`** — a tree meeting `2·depth + 1 ≤ size` with equality is a **path**: every
  `eml` node has a leaf child. General, any depth.
- **`inv_x_size_nine_isPath`** — `d(1/x) = 4` forces `depth ≥ 4` and `9 = 2·4+1` forces `depth ≤ 4`,
  so **a 9-node solution is a depth-4 path**. `2⁴·2⁴·2 = 512` shapes with ≤ 5 real parameters.
- **`inv_x_size_nine_split`** — only two top-level splits survive: `(1,7)` and `(7,1)`. The
  intermediate `(3,5)` and `(5,3)` are impossible; neither child could reach depth 3.
- **`invX4_not_isPath`** — the known 11-node witness is *not* a path. It spends its extra 2 nodes
  branching, so the 9-node family is a genuinely different shape, not a tightening of the known one.

**A growth companion to rung 2, and the first branch closed:**

- **`depth_le_one_upper_log_bound`** — a depth-≤1 tree grows at most like `E − log x` on `(0,1]`.
  The *upper* companion to `depth_le_one_right_tetrachotomy`, which supplies lower bounds.
- **`depth_le_two_log_decay_floor`** — a depth-≤2 tree falls at most logarithmically at `0⁺`:
  `F + log x ≤ t.eval x`. **No positivity hypothesis** — `exp ≥ 0` caps the first term and the
  lemma above caps the second. Where `rung2_positive_floor` needs positivity and bounds by `C·x²`,
  this needs nothing and bounds the value itself.
- **`shifted_inv_not_in_eml_depth_le_2`** — **`K − 1/x` is out of reach at depth 2, for every `K`.**
  A pole cannot be manufactured two levels up, because `−1/x` falls faster than any logarithm.

That closes one named branch of split A: `t = eml (const c) (eml R₂ (leaf₂))` with `log(leaf₂) = 0`
requires `R₂ x = K − 1/x` at depth 2, which is now impossible.

**What is not closed, stated plainly:** every other branch — `log(leaf₂) ≠ 0`, `leaf₂ = var`, the
right-branching depth-3 paths, `ℓ = var`, and all of split B. The `leaf₂ = var` branch *looks* easy
(a sign clash near `0`), and looking easy is not a proof; it is not claimed. **No counting argument
can finish this**: 9 nodes genuinely permit depth 4, so every remaining refutation must be semantic.

`sorryAx` 0; ledger 242 unchanged.

### The second arrow: DAG → scheduled datapath. Depth survives, area dies.

`schedule_ge_wdepth` — for any schedule `s` in which an `eml` instruction's result is available no
earlier than `L` after both operands (`SchedValid`), **`L · depth ≤ s i`**. Hence
**`inv_x_schedule_ge_four_L`: no schedule computes `1/x` in fewer than `4·L`** — however many blocks
it allocates, *including one*. At the measured `L = 5` cycles that is **20 cycles**.

This is the arrow on which the measured **×4.00 area multiplier dies.** A time-multiplexed datapath
reuses one block across cycles (forge already does this — the shared-MAC matmul is ~4 DSPs constant
in size), so area becomes `O(1)` in depth while the latency floor is untouched. The forge report's
area row has been amended: ×4.00 is a property of the *unshared* lowering, not of the quantity.

**The invariant ledger, two arrows deep:**

| quantity | tree → DAG (sharing) | DAG → schedule (resource sharing) |
|---|---|---|
| **depth / latency** | preserved exactly (`netDepth_eq_depth`) | **floor survives** (`schedule_ge_wdepth`) |
| **size / area** | destroyed — exponential (`sqProg_size`) | destroyed — one block serves every node |
| critical path | preserved (per-stage) | preserved (per-stage) |

**Depth is the only quantity that survives both.** Twice today the *area* figure has been the
misleading one — first as the wrong instantiation of the weighted-cost socket, then as the ×4.00 a
scheduler erases. Area agrees with depth exactly when the lowering happens not to share, which is a
fact about the lowering.

`schedule_ge_wdepth` uses the weighted machinery directly (`wdepth 0 0 L`), so the socket earns its
keep rather than sitting unused. `sorryAx` 0; ledger 242 unchanged.

### The weighted socket has a trap, and measuring found it

`forge` now measures the block (`forge/reports/eml_block_cost_2026_08_11.md`, yosys 0.40 +
verilator 5.024, generic gate mapping, Taylor-scaffold kernels). One block at Q16.16: **37,853
cells, 90 logic levels, 5 cycles**, functionally verified before being costed. A 4-deep serial
chain: **area ×4.00, critical path ×1.00**.

That ×1.00 is the finding. `netWDepth_eq_wdepth` says any path-additive cost survives sharing for
arbitrary weights — true, and it invites plugging in any measured per-block number. Three natural
instantiations, **one correct**:

- `we` = **cycles per block** → total latency. **Correct**; `d(1/x) = 4` gives `≥ 20` cycles.
- `we` = **logic levels** → returns `4 × 90 = 360`, a true fact about a weighted tree that **is not
  the physical critical path** (measured: 90). The theorem does not know registers exist.
- **area** → not a critical-path quantity at all; it sums over *blocks*, not along the *longest
  path*. Wrong theorem — and the one whose measured ratio (×4.00) looks most like a confirmation.

**A weight that is not path-additive in the physical artifact makes the conclusion false while
leaving the theorem true.** Written into `EMLNetlistDepth`'s header, next to the socket it qualifies,
because the failure mode is using a sound theorem on the wrong quantity — which no gate in this
repo can catch.

### `MachLib.EMLNetlistDepth`: which tree bounds survive SHARING

The question that decides whether the reciprocal lower-bound programme means anything downstream:
hardware is a DAG, not a tree, and every real datapath shares subexpressions. **Which tree bounds
survive?** The answer is asymmetric, and it inverts the naive guess.

- **Depth survives exactly.** A straight-line EML program is modelled directly (`EMLInstr`,
  `ProgWf`: an instruction may only read strictly earlier results). `netDepth` is defined on the
  *program*, `EMLTree.depth` on the *unfolding*, and `netDepth_eq_depth` proves them equal with **no
  hypothesis at all** — which is exactly the statement that sharing is invisible to depth.
  Consequently `inv_x_not_in_eml_depth_le_3` transfers verbatim:
  **`inv_x_netlist_depth_ge_four`** — no straight-line EML datapath computes `1/x` with
  combinational block-depth `< 4`. And since each level drops the index by at least one
  (`unfold_depth_le_index`), **`inv_x_netlist_index_ge_four`**: the output cannot sit before index
  4, so at least **five instruction slots**.

- **Size survives only as a logarithmic shadow — CORRECTED.** An earlier draft of this entry said
  size "does not survive at all". That is overstated, and an outside reader caught it.
  `unfold_size_le` bounds the unfolding by `2^(i+1)`, so `s(1/x) ≥ 9` *does* force an output index
  `≥ 3` (**`inv_x_netlist_index_ge_three_from_size`**) — a true bound, which the depth route's `≥ 4`
  **strictly dominates**. The right statement is "carries a logarithmic shadow, strictly dominated",
  not "carries nothing". The exponential loss is concrete: `sqProg_gap_at_four` — **5 instructions,
  31 nodes**.

- **Unfolding preserves semantics, and it is now a named theorem.** `progEval` evaluates the program
  the way hardware does — reading earlier results, sharing them — and **`progEval_eq_unfold_eval`**
  proves it agrees with the unfolding. This is load-bearing: without it `unfoldAt` is a definition
  nobody had to accept and a tree lower bound constrains nothing. Every transfer theorem now takes
  its hypothesis on `progEvalAt`, i.e. on the *program*. `inv_x_netlist_depth_ge_four` consequently
  **dropped its `ProgWf` hypothesis** — well-formedness is needed for the index bound, not the depth
  bound. The claim auditor flagged the strength change on the next run.

- **Any path-additive cost survives sharing, not just unit depth.** **`netWDepth_eq_wdepth`**
  generalises the invariance to per-kind block weights `(wc, wv, we)`, with
  `wdepth_unit_eq_depth` recovering ordinary depth at `(0,0,1)`. `(+, max)` is blind to sharing
  while node-counting is not — that is the algebraic reason for the whole asymmetry, and it is the
  socket a measured per-block latency, LUT-depth or energy figure plugs into without re-proving the
  bridge.

- **Therefore `s(1/x) ∈ {9,11}` refines a tree-encoding quantity that no datapath bound depends on,
  while `d(1/x) = 4` is a resource bound.** That inverts what the two arms looked like from the inside:
  the depth arm cost 28 sessions and a refuted conjecture, the size arm looked like the sharper
  number. Neither was chosen for this reason. Recorded because the useful one was not the one that
  looked useful.

- **Scope, stated rather than implied.** "Datapath" means a straight-line program over the EML
  primitive `(a,b) ↦ exp a − log b`, the block Forge's hardware lane emits. Nothing here bounds gate
  depth *inside* a block, and nothing here is a lower bound against arbitrary circuits — that would
  be a circuit-complexity claim and this is not one.

- **The overclaim this must never become.** If a synthesised block measures 6 ns, `d(1/x) = 4` does
  *not* license "every reciprocal circuit needs 24 ns". Four serial *abstract* EML dependencies is
  what is proved; retiming, pipelining, a different internal implementation and a different
  technology are all untouched. A measurement licenses a statement about **one synthesised
  artifact**, reported alongside the structural bound and never fused with it. Written into the
  module header so it survives the next reader.

- `netDepth_eq_depth` needs only `[MachLib.Real, MachLib.Real.zeroR]`; the transfer theorems carry
  the ordinary `MachLib.Real` base. `sorryAx` 0; ledger 242 unchanged; seven gates green.

### Level 7 hardening: the relation vocabulary is now a pinned artifact

An outside reader found a real defect and named the pressure point correctly.

- **DEFECT, confirmed and fixed.** Canary 7 asserted `len(objections) == 3` — *cardinality*. A
  quietly weakened obligation list that swaps one obligation for a feebler one **at constant
  count** sailed straight through it. It now pins the obligation **names**. `canary 9` is the
  swap it previously certified: `proof_uses` (the composition obligation, the one that caught the
  flagship gap) → `statement_mentions`, count unchanged at 3.

- **`relations.lock.json`.** Once level 7 traded semantics for set membership, all remaining trust
  moved into the sentence templates and the obligation lists — and a template that renders prose
  stronger than its obligations warrant is the original overclaim one layer down, with a green
  checkmark. **No check can catch that**; it is the question level 7 deleted rather than solved.
  So it is not verified, it is made **expensive**: `RELATIONS` + `ENTAILS` are pinned by sha256,
  and any edit fails the **shipping path** until `--bless-relations` is run deliberately.
  Injection test (template strengthened to "*is fully verified … on real silicon*", obligations
  untouched): shipping-path exit **1**, naming the template. Reachability witness asserted first.

- **`ENTAILS`, deliberately empty.** `asymptotic_upper_bound` genuinely implies
  `pointwise_upper_bound`, and their obligation lists are *identical* — so a monotonicity check
  would admit it. The machinery still refuses, because the pair was never declared (`canary 10`).
  A specimen built on a **true** implication is the only kind that shows the refusal is about
  declaration rather than about correctness. Declared entailments are additionally checked for
  obligation-monotonicity.

- **A second independent renderer was suggested and is NOT being built.** Two renderers over the
  same table produce the same sentence from the same overclaiming template: agreement is
  guaranteed and says nothing about the concern that motivated it. The correlation lives in the
  *table*, not the rendering, so the answer is a pin and a ceremony.

- **Verbatim-only is permanent, not a tunable.** The cost is machine-stilted flagship sentences.
  Loosening to "paraphrase allowed if adjacent to the licensed form" is a one-way door.

- The phenomenon now has a name: **proof–claim drift** — `Valid(T)` does not give `Licensed(C,T)`.
  `tools/claim_audit/README.md` rewritten around it (the ladder is 7 levels, not 6, and level 3
  is documented as unable to certify absence).

- 10 canaries fire; seven gates green; ledger 242 unchanged; `sorryAx` 0.

### The `LogSafe` reduction: rung 2 replaces the tower-form requirement

- `depth_le_two_neg_log_bound` — a **positive depth-≤2 right child** satisfies
  `-log (b.eval x) ≤ N - log x - log x` near `0`. It follows from `rung2_positive_floor`'s quadratic
  floor `b x ≥ C·x²` by monotonicity of `log`.

- **Why this retires the quantitative half of the open item.** The corrected note on `LogSafe` said
  removing it needs a **tower-form** decay bound `b x ≥ exp(-E_j x)`. Rung 2 gives strictly more, and
  gave it already: a *polynomial* floor, whose `log` is a **log-scale** bound. A depth-≤3 tree has a
  depth-≤2 right child, so at depth ≤ 3 **nothing quantitative is missing**. The requirement was
  overstated by a whole scale, twice — first as a positive floor, then as a tower bound — and what
  fixed it was a theorem proved for an unrelated reason.

- `neg_log_bound_under_rung_one` — `N - log x - log x ≤ envelope 1 (log (exp N + 2)) x`, so the
  discarded term is bounded by **rung one regardless of `N`**. "Costs one extra level" is now a
  number, not a hand-wave.

- **What actually remains is sign stability, not a bound.** Rung 2 needs the right child positive on
  an *interval*; a pointwise sign fact gives that only if the child does not oscillate near `0`. That
  residue is a tameness statement — and it is where an o-minimality / Khovanskii citation **genuinely
  applies**, for *finiteness of sign changes*, which is what those theorems actually give. The
  original attribution asked them for a positive floor, which they cannot give. Same literature,
  different proposition, and this time the implication holds.


- **Typed claims** (relation `asymptotic_upper_bound` / `pointwise_upper_bound`, both new).
  These sentences are GENERATED from the claim objects, not written:

  > The negated log of a positive depth-≤2 EML tree is bounded above by N − 2·log x on a neighbourhood of 0 whose existence the theorem asserts rather than assumes.

  > The discarded −2·log x term is bounded above by rung one of the growth envelope on (0,1].
- `sorryAx` 0; ledger 242 unchanged; six gates green.

### Claim audit level 5: relation integrity — the prose is now GENERATED

- The rungs below are all string questions about a printed form. *"Does the statement assert this
  relation between these objects"* is not one, and pretending a substring search answers it would be
  the same error the ladder exists to catch. So the relation is **not verified — it is made
  binding.**

  A claim declares `subject / relation / object / bound / epistemic_type` from a **closed
  vocabulary**, and the relation names the structural obligations it entails. Declaring
  `end_to_end_tracking` obliges `conclusion_mentions`, `hypotheses_count` **and** `proof_uses`;
  omitting any of them is rejected. **Naming a stronger relation buys stronger obligations, not a
  stronger sentence.**

- **The prose is rendered from the record**, and the auditor requires the *generated* sentence to
  appear in the source document — not an author's paraphrase of it. That reverses the architecture:
  instead of *human prose → try to validate it*, it is *checked record → generate prose*. The two
  sentences the current records license:

  > The 3 ULP bound on fxpid's implementation error holds in the real domain.

  > The fixed-point affine datapath tracks the exact real trajectory to within one ULP per step, with the bound derived from the implementation rather than assumed.

- **Firing specimen**: `end_to_end_tracking` declared bare raises exactly three objections, one per
  shed obligation.

### Claim audit level 4: strength integrity

- **`hypotheses_count`** — the theorem's top-level antecedent count must be what the prose was
  written for. `hypotheses_of` keeps what `conclusion_of` discards, because the number and shape of
  a theorem's hypotheses **is** its strength.

  This catches the **mirror** of the flagship failure: not prose that outruns a theorem, but a
  theorem quietly *weakened* later — a hypothesis added — while the prose describing it stays put.
  Decidable both ways, since the antecedents are a syntactic prefix of the printed type.

- **Firing specimen** checks the counter *discriminates*: 1 hypothesis on `fxaffine_traj_tracks_exact`
  versus 6 on `pid_trajectory_from_bits`. A counter that always returned the same number would pass
  a strength check vacuously, so the specimen asserts a difference rather than a value.

- Registered: the end-to-end theorem at **1** hypothesis (`0 ≤ qval c`), and
  `fxpid_real_trunc_lt_3ulp` at **0** — mechanically confirming the "both are unconditional, the
  `Nat` premise is discharged inside rather than assumed" claim made when the bridge landed.

### Claim audit level 6: composition integrity

- **`proof_uses`** — the proof must actually go through the lemmas the prose credits. Extracted
  from the proof term (`#print thm`, everything after `:=`). A **third** question, distinct from the
  two the auditor already asked:

  | check | question |
  |---|---|
  | `#print axioms` | what could this rest on — the trust base |
  | `statement` / `conclusion` | what does this talk about — the subject |
  | `proof_uses` | what does this actually go through — the composition |

- **Asymmetry, opposite in direction to level 2.** A lemma *named* in a proof term was genuinely
  invoked, so presence is decisive for **direct** use. Absence is **not** decisive for non-use — the
  lemma could be reached transitively. So `proof_uses` is a positive obligation only; a passing
  `proof_uses` never means "nothing else was involved".

- **Firing specimen**: `pid_trajectory_from_bits`'s proof never invokes `fxpid_trunc_lt_3ulp`.
  **The flagship claim now fails independently at three levels** — subject, conclusion, and
  composition. One gate can be fooled; three agreeing is evidence the gap is real rather than an
  artifact of how any single check is written.

- Registered on the end-to-end claim: `fxaffine_traj_tracks_exact` must invoke both
  `affine_trajectory_bound` and `fxaffine_step_error`. It does — so the composition is now
  mechanically attested, not asserted.

### Claim audit level 3: conclusion integrity

- **`conclusion_mentions`** — the artifact must appear in what the theorem **concludes**, not merely
  somewhere in its statement. Strips top-level `∀ …,` binders and `→` antecedents (depth-tracked, so
  arrows inside a hypothesis's own type are ignored) and checks the consequent.

  This blocks the attack the outside reader named: *an unused hypothesis mentioning `fxpid` would
  pass the subject check while changing nothing.* It would not pass this one.

- **Firing specimen**: `depth3_bounded_left_absurd` mentions `t1` in its statement and concludes
  `False`. So a claim that it concludes something about `t1` is rejected — statement ✓, conclusion ✗.
  The specimen retires itself if `t1` ever reaches the conclusion.

- Registered on both bridge claims: `fxaffine_traj_tracks_exact` must conclude about `ulp` and
  `fxTraj`; `fxpid_real_trunc_lt_3ulp` must conclude about `fxpid`. Both do.

### ▸▸ Join 2 closed for the affine plant: the datapath's own error drives the trajectory bound

- **`MachLib.Real.fxaffine_traj_tracks_exact`** — for every bit-vector trajectory the netlist
  produces, its Q-value stays within `ulp · geom (qval c) n` of the exact real affine trajectory,
  and `(1 − qval c)·(ulp · geom …) ≤ ulp` makes that `n`-independent when the plant contracts.

  **The `ε` is `ulp`, produced by the netlist** — `fxaffine_step_error` derives it from
  `fxmul_real_trunc_lt_ulp`, and the theorem quantifies over `List Bool`, not over a free real.
  This is the composition the flagship sentence asserted and did not have.

- **The right subject was `fxaffine`, not `fxpid`.** The trajectory theorem's plant is the affine
  map `c·x + d`, and `FixedPointRTL` already documents `fxaffine` as "the PID plant / EMA / RC
  kernel"; `fxpid` is the *controller's* multiply-add. Part of why the chain never composed is that
  the two halves were about different datapaths.

- **Scope.** This closes the chain for the **affine plant kernel**. It does **not** close it for
  `fxpid`: `pid_trajectory_from_bits` still quantifies `ε` universally, and connecting the
  controller's output to the plant's state update needs a closed-loop model that does not exist
  here. The `--self-test` specimen therefore still fires, correctly.

- **Level 2: subject integrity modulo unfolding.** `statement_mentions_deep` walks the theorem's
  type and then the printed bodies of the constants it names, so it sees a subject that enters one
  δ-step away. `fxaffine` is **invisible** to the syntactic check and **visible** to this one —
  which is the specimen that validates it.

  **The two directions are not symmetric, and this is not an implementation limit.** Bounded
  unfolding can certify *presence* (stop the moment the target is found) but never *absence*
  (budget exhausted ≠ unreachable). So absence claims — including the flagship firing specimen —
  stay on the syntactic check, which is decisive for the statement as printed. Same lesson this
  corpus already learned from grid search: a bounded search cannot prove a negative. The auditor
  reports `truncated` explicitly rather than passing a search that found nothing.

## [Unreleased] — 2026-08-10

### Trust gates: the auditor now checks what a theorem SAYS, not only what it rests on

- **A seventh check, and the failure that forced it.** `pid_trajectory_from_bits` was documented as
  carrying the bit-level truncation into the closed-loop bound. Its statement mentions **no
  bit-level object at all** — it quantifies `ε` universally and takes the per-step bound as a
  hypothesis. `sorryAx`, the axiom ledger and the claim auditor all passed, because every one of
  them asks *what does this theorem depend on*, never *does the prose describe the theorem that
  exists*.

  `claim_audit.py` gains **`statement_mentions`**: a claim naming an artifact must be backed by a
  theorem whose **type** references it. `#check @thm`, not `#print axioms thm`. Had it existed, the
  flagship claim would have been rejected on the day it was written.

  Firing specimen in `--self-test` (house rule: a gate without one is unvalidated) — it asserts
  `pid_trajectory_from_bits`'s statement has no `fxpid` in it, and *fails loudly if that ever stops
  being true*, which is precisely the day the claim becomes legitimate.

- **`MachLib/FixedPointRealBridge.lean`** — join 1 of the flagship chain, closed.
  `fxmul_real_trunc_lt_ulp` / `fxpid_real_trunc_lt_3ulp` state the truncation
  bounds over `MachLib.Real`, derived from the `Nat` versions via `natCast_lt_mono`
  (proved here from `natCast_succ`; the corpus had monotonicity only as a file-local lemma and no
  strict version). Both unconditional — the `Nat` premise is discharged, not assumed. Join 2
  (controller error → closed-loop state-update error) needs a plant model and remains open.


### ▸▸ `d(1/x) = 4` — the depth question is SETTLED

- **`MachLib.inv_x_not_in_eml_depth_le_3`** — **no depth-≤3 tree is `1/x` on the positives.** With
  `invX4` a depth-4 reciprocal, `inv_x_depth_eq_four` closes the bracket the arm has carried since
  it began: 28 sessions trying to prove `1/x ∉ EML` at any depth (false — `inv_x_mem_EML` refuted it
  with a depth-6 witness), then `invX4` at depth 4, then `2 ≤ d`, `3 ≤ d`, and now `4 ≤ d`.

  The proof dispatches an arbitrary depth-≤2 left child into one of six behavioural classes, each
  closed separately and **none by enumerating configurations**:

  | left child | instrument |
  |---|---|
  | `const c`, `var` | leaf theorems |
  | `eml A B`, `A` grows at `∞` | `∞`-side rank mismatch |
  | `eml (const p) var`-headed | `0⁺`-side rank mismatch (a `1/x` pole) |
  | `eml a var` | leaf-var-right |
  | `eml A B`, `A` constant, `B` off `0` | bounded left child + **rung 2** |
  | `eml A (eml var (const q))`, `log q = 1` | log-scale pole |

- **`MachLib.inv_x_size_ge_nine`** / **`inv_x_size_nine_or_eleven`** — the size bracket sharpens to
  **`s(1/x) ∈ {9, 11}`**, since `2·depth + 1 ≤ size` turns `depth ≥ 4` into `size ≥ 9` and oddness
  kills 10. **Still not `s = 11`**: a 9-node depth-4 reciprocal would undercut `invX4`, and the depth
  arm cannot exclude it because 9 nodes permit depth 4. Flagged before the depth work began; it
  survives exactly as flagged.

- **`MachLib.rung2_positive_floor`** — the load-bearing input. *Every positive depth-≤2 tree is
  bounded below by `C·x²` near `0`*, so nothing at depth 2 can be positive and decay faster than
  quadratically — in particular nothing can imitate `exp(−1/x)`. A statement about the **grammar**,
  with the depth-3 case as a corollary rather than its motivation.

- **Three pole regimes, and they are genuinely distinct.** `exp (t1 x)` bounded; `t1 ≍ 1/x` (a
  *double* exponential); and `t1 ≍ −log x`, which sits between them and is fatal only because
  `exp c₀ > 1` **strictly** leaves a residue after the equation's own `1/x` is subtracted. The last
  shape of the arm fell through the first two for exactly that reason.


### ⚠ CORRECTION — the `LogSafe` removal was attributed to the wrong theorem

The growth envelope's header, and three frontier briefs, said that removing the `LogSafe` side
condition needs *"a shallow tree cannot be arbitrarily small while staying positive — i.e.
finiteness of sign changes, a Khovanskii/Pfaffian input"*. **Both halves were wrong.** Caught by an
outside reader, verified against the source, corrected in
`MachLib/EMLGrowthEnvelope.lean`'s header:

- **A zero count cannot give a positive floor.** `exp(−x)` is positive on `(0,∞)`, has no zeros at
  all, and still has infimum `0`. No Pfaffian zero-counting theorem discharges the condition — it
  was the wrong theorem, not merely an unproved one.
- **The induction does not need a positive floor.** `LogSafe` is consumed at exactly one step, and
  only to *discard* `−log(b x)`. What suffices is a lower bound on the right child of **tower form**
  (`b x ≥ exp(−E_j x)`), which costs one extra rung — a quantitative *decay-by-depth* bound, not a
  zero count. That is the exact restricted lemma to aim at, and it is Khovanskii-*adjacent* (effective
  bounds by Pfaffian format) with the caveat that **totalised `log` breaks Pfaffian-ness**: these
  terms are only piecewise Pfaffian and any citation applies per piece.

**No axiom was spent, and it is now unclear that one is needed** — `exp(−1/x)` is in EML and decays
faster than any polynomial, yet its `−log` is exactly `1/x`, which sits inside rung 1.

### MaxEnt: the uniform distribution maximises entropy

- **`MachLib.Real.maxent`** / **`maxent_log_perplexity`** (`MachLib/KLDivergence.lean`) — `H(p) ≤
  −log u = log(1/u)` for any unit-mass `p` against a uniform reference `q ≡ u`. **No new machinery:**
  `log n − H(p)` *is* `KL(p ‖ uniform)`, and `kl_nonneg` was already machine-checked, so the only
  work is `ncrossH_const` — one list induction collapsing `Σ pᵢ·log u` to `(Σ pᵢ)·log u`. Stated in
  the uniform weight `u` rather than a cardinality, so no `Nat` cast is needed; `log(1/u)` is the
  perplexity form and is literally `log n` on an `n`-point support. `sorryAx`-free, zero new axioms.
  The entropy cluster now carries all four classical facts: Legendre duality, Fenchel–Young,
  `KL ≥ 0`, cross-entropy ≥ entropy, and MaxEnt.

### EML depth 3: the last family, and the decay-by-depth ladder

- **Four of the six `A`-shapes of the last depth-3 family, closed by a RANK MISMATCH.** Read at
  either end, the equation is `exp(t1 x) = 1/x + log(t2 x)` — `exp` of a depth-2 tree against `log`
  of one, **two rungs apart**. `depth3_left_unbounded_absurd` closes the shapes where `A` grows at
  `∞`; `depth3_left_pole_at_zero_absurd` closes `A = eml (const p) var`, a pole at `0`. The
  substitution `x = exp(−t)` turns every `1/x` into `exp t`, so the pole problem *becomes* the growth
  problem and one instrument covers both ends, division-free. **No configuration enumeration and no
  parameter regimes** — neither argument asks what the constants are.

- **`MachLib.depth_le_one_positive_floor`** — **a positive depth-≤1 tree has a linear floor near
  `0`.** The base rung of the decay-by-depth ladder, and **sharp**: the only shape whose value
  actually reaches `0` is `eml var (const q)` at `log q = 1`, where `t x = exp x − 1 ≥ x` — linear,
  with no quadratic correction needed at this depth. Positivity is a *hypothesis*, not derived from
  a pin, which is what makes it reusable and is precisely what the leaf-`var` branch could not do:
  its floors were entangled with its own equation.

  > This is the theorem family **both** remaining open items point at. Removing `LogSafe` wants a
  > decay bound at all depths (weak); the last depth-3 case wants one at depth 2 (sharp). Two open
  > problems, one ladder.

- **The bounded-left core, generalised rather than re-derived.** `leaf_var_arith`,
  `leaf_var_floor_absurd`, `leaf_var_quad_arith` and `leaf_var_quad_floor_absurd` turn out to be the
  `W = exp 1` instances of `bounded_left_*` — every load-bearing lemma of that branch used only the
  bound `exp (t1 x) ≤ W`, never the shape `t1 = var`. Also `exp_beats_linear`/`_past` (`exp` outruns
  any line **at a point we can name**), `depth_le_one_neg_log_bound_at_infty`,
  `depth_le_two_bound_at_infty`, `log_le_of_le_exp_mul'`.

  **`d(1/x)` is UNCHANGED at `{3,4}`.** The remaining case is `A` constant-valued, where the
  arithmetic is now fully discharged and only `t2`'s shape analysis is left.

### EML depth 3: the `t1 = var` family is CLOSED

- **`MachLib.leaf_var_absurd`** — **no depth-≤2 right child lets `eml var t2` be `1/x`.** The first
  *complete family* of the depth-3 arm, closing the residue
  `t2 = eml A (eml var (const q))` that the previous two passes were left resting on. 28 new
  theorems, `sorryAx` 0, **zero new axioms** (ledger 242 unchanged).
  **This does not move `d(1/x)`**, which stays `{3,4}`: the other depth-3 family (`t1 = eml a b`,
  `b ≠ var`, unbounded left child) is untouched and could still hold a witness.

- **`MachLib.leaf_var_right_strict_mono`** — the reusable half. **The right child of a leaf-`var`
  reciprocal is strictly INCREASING below the cutoff**, for any `t2` at any depth: the equation
  gives `log (t2 x) = exp x − 1/x` pointwise and both terms rise. Every earlier closure in this arm
  read a *floor* off the tree; this reads a **direction**, which is what the shapes where the two
  terms cancel need — there the floor is `0` and carries no information. It kills both
  constant-valued `A` shapes outright, citing no floor dispatcher at all.

- **`MachLib.leaf_var_quad_floor_absurd`** + **`MachLib.exp_ge_three_mul`** — a **quadratic** floor
  on the right child is fatal too. Needed because the coincidence stratifies further than the
  constant-`B` case did: with a *moving* `log` the linear coefficient is `κ := G − exp(−G)`, whose
  sign is independent of `γ`, and at **`G·exp G = 1` (`G = Ω`, the omega constant) both `γ` and `κ`
  vanish** and the tree is second order, `≍ (G/4)·x²`. `leaf_var_arith` cannot take that floor —
  its last step is `exp t ≥ t + t`, which ties exactly against the `2t` a square contributes — so
  the peeling trick was applied at `k = 2` instead of `k = 1`: `exp t ≥ e²(t−1) > 4(t−1) ≥ 3t` for
  `t ≥ 4`, on the single numeric input `2 < e` squared.

  > The previous pass found that for **constant-valued** `B` the tangent bound supplies the linear
  > term for free, so the three-way `γ` split collapses to two. **That lesson does not survive a
  > moving `log`** — recorded because it was registered as a prediction and it failed in the
  > direction that mattered.

- **`MachLib.log_shift_ceiling`** / **`MachLib.log_shift_floor`** — two-sided linear bounds on
  `log (exp g + u)` around the cancellation point, both division-free (`exp(−g)` in place of `1/M`)
  and both from the same tangent bound applied to `v := log (exp g + u) − g`.

### EML complexity: the reciprocal in the metric that is priced

- **`MachLib.inv_x_size_ge_seven`** — **two `eml` gates can never compute a reciprocal.**
  `size ≤ 6` plus `size_odd` gives `size ≤ 5`; the bridge `2·depth + 1 ≤ size` then gives
  `depth ≤ 2`, which `inv_x_not_in_eml_depth_le_2` closes. With `invX4` as a witness at 11 nodes and
  oddness ruling out 8 and 10, a **minimal EML reciprocal has size 7, 9, or 11** —
  `inv_x_min_size_seven_nine_or_eleven`. First result of this arc stated natively in the axis
  `docs/cost_theory.md` T38-NNP actually prices. sorryAx-free, zero new axioms.
  **NOT proved: `s(1/x) = 11`.** Sizes 7 and 9 are open; a 528-configuration numerical search over
  all 3- and 4-gate shapes found no witness, but that is evidence, not proof.

- **`MachLib.two_mul_depth_succ_le_size`** — `2·depth + 1 ≤ size`, tight at every depth. Hence
  `size ≤ 10 ⟹ depth ≤ 4`: **the size question is finite in depth**, since any tree of depth ≥ 5
  already costs ≥ 11 nodes. Footprint is `propext, Real, Quot.sound` — pure tree combinatorics, no
  `Classical.choice` and no analysis.

- **`MachLib.growth_envelope`** — a depth-indexed growth ceiling
  `envelope 0 M x = M − log x`, `envelope (k+1) M x = exp (envelope k M x)`. One induction on the
  tree replaces the six ad-hoc shape cases and the cutoff of the earlier depth-1 and depth-2
  ceilings. `depth_gt_of_outgrows` is the contrapositive lower-bound tool, and `size_envelope`
  restates it in node count. Carries a **`LogSafe`** side condition (every `eml` right child `≥ 1`);
  removing it needs finiteness of sign changes for exp-log expressions, a Khovanskii/Pfaffian input.
  **⚠ That last sentence is WRONG and is corrected below (2026-08-10) — `exp(−x)` is positive with
  no zeros and infimum `0`, so a zero count cannot yield a positive floor, and the induction does
  not need a positive floor anyway.** See `MachLib/EMLGrowthEnvelope.lean`'s header.

- **`MachLib.inv_x_within_envelope_one`** — the honest limit: `1/x ≤ envelope 1 0 x`, so the
  reciprocal sits **inside the first rung** and **no growth argument at any rung can exclude it**.
  EML depth is gate complexity, not growth complexity; `d(1/x)` is frozen at `{3,4}`.

- **`MachLib.invX4gen_eval`** — the depth-4 witness is **not isolated**. With both `const 1` leaves
  making their `log`s vanish the tree collapses to `(exp(exp c0) − exp(exp c1))/x`, so the witness
  condition is one equation on two constants: a **curve** of size-11 depth-4 reciprocals.
  `invX4 = invX4gen (log (log (1+e))) 0`.

### Trust gates

- **`scripts/check_aggregator.sh` had two scope defects and now does a real transitive closure.**
  It iterated `find MachLib -maxdepth 1` (308 of 922 files invisible) and tested "imported by any
  `.lean`" rather than reachability, so an **island** of mutually-importing modules passed
  trivially. Found by an axiom count that would not reconcile. Reachable: **616 of 922**. Validated
  with two firing specimens — a subdirectory orphan and a two-module island — each of which the old
  gate passed and the new one fails.

- **`MachLib/Applications/` (12 modules) folded into the aggregator.** It was an unreachable island
  and five of its modules did not build: a bare `apply le_min` was ambiguous between
  `MachLib.Real.le_min` and the namespace-local `AerospaceActuatorGuardBandRate.le_min`. The two are
  the same theorem — identical statement and proof — so qualifying is semantically neutral. No
  hidden `sorry`: every match under those paths was prose in a docstring.

## [2026-07-26]

### New — 2×2 Joseph covariance update: structural PSD + full-width dot bound (`MachLib/Matrix2JosephPSD.lean`)

**`kalman2_joseph_psd`** + **`fxerr_dot2_fullwidth`**: the proof spine for the scheduled-linear-algebra /
Joseph arc (Forge `docs/scheduled_linear_algebra.md`), certifying two obligations *before* the datapath is
built. `kalman2_joseph_psd`: the Joseph-form posterior `P⁺ = (I−K) P (I−K)ᵀ + K R Kᵀ` stays symmetric
positive-semidefinite for any gain K — the numerical-robustness guarantee that makes a recursive covariance
update safe (no gain, and no round-off in the gain, can drive the covariance indefinite; this is *why* real
filters use the Joseph form). Scoped to 2×2 with a Mathlib-free PSD predicate — the quadratic form on entries
(`Psd2`): a congruence `G X Gᵀ` preserves PSD (`psd2_congruence`: its quadratic form at `v` is `X`'s at
`Gᵀv`) and a sum of PSD is PSD (`psd2_add`), so the Joseph update is `psd2_add` of two congruences (`G₁ =
I−K`, `G₂ = K`). `fxerr_dot2_fullwidth`: the full-width scheduled MAC (`seq_mac_fw`) keeps its products
exact and truncates ONCE per dot, so its forward error is a single rounding (≤ 2⁻ᶠ) — a factor-`K`
improvement on the per-product engine's `K·2⁻ᶠ`; it is exactly `fxerr_dot2` with the truncation moved off the
products onto the final add. `sorryAx`-free, ZERO new axioms (Real arithmetic + `mach_ring` + the existing
FxErr algebra; `Real` exposes `OfNat` only for 0/1, so the coefficient 2 is written `(1 + 1)`).

## [Unreleased] — 2026-07-25

### New — 2-D Kalman MMSE-optimality, trace loss (`MachLib/Matrix2KalmanMMSE.lean`)

**`matrix2_posterior_mean_mmse`** + **`matrix2_mmse_excess`**: the vector analogue of
`posterior_mean_mmse` — for a 2-D state the MMSE-optimal estimator is the posterior-mean vector,
minimizing `E[|X−c|²]` (the trace of the error covariance). The key that keeps it tractable in the
Mathlib-free base (no 2-D integration / Fubini): the trace loss **separates per component**,
`E[|X−c|²] = Σᵢ E[(Xᵢ−cᵢ)²]`, so the vector optimality is exactly the sum of the per-component scalar
conjugate MMSE — no new integral. `matrix2_posterior_mean_mmse`: the optimal total conditional MSE
`tr(Σ_post) = postVar₀+postVar₁` (attained by the posterior-mean vector) is `≤` any estimate's total
conditional MSE (`add_le_add_both` of two `posterior_mean_mmse`). `matrix2_mmse_excess`: the excess risk
of `(c₀,c₁)` over the optimum is *exactly* `|c−m|² = (c₀−m₀)²+(c₁−m₁)²` — a sum of squares, `≥ 0`
(`matrix2_mmse_excess_nonneg`) and `0` iff `c=m`, so the posterior-mean vector is the *unique* minimizer.
`sorryAx`-free, ZERO new axioms. (Trace/Euclidean loss, the standard MMSE criterion; the per-component
reduction is why the vector case needs no 2-D integration.)

### New — fixed-point stability of the 2×2 symmetric matrix inverse (`MachLib/Matrix2InverseFixedPoint.lean`)

**`matrix2_sym_inverse_fwd_error`** + **`matrix2_inverse_conditioning`**: the scoped-honest first step
of "scale the math to matrices" — a **fixed-size** inverse (no dynamic loops, no general Cholesky/LDLT),
at exactly the dimension the existing matrix Kalman uses (the EKF innovation covariance `S=H·P·Hᵀ+R` and
`kalman2d` covariance are 2×2, so the gain needs a 2×2 inverse). For symmetric `A=[[a,b],[b,d]]`,
`A⁻¹ = (1/det)·[[d,−b],[−b,a]]` — one reciprocal (of `det`) plus qmuls — so its fixed-point error composes
exactly like the scalar reciprocal forward-error (`kalman_update_1d_fwd_error`), `w:=1/det` carried
abstractly. `matrix2_inv_entry_fwd_error`: each entry `qmul(cofactor, recip)` is within `s + |cofactor|·Erec`
of the exact `cofactor/det`; `matrix2_sym_inverse_fwd_error` bundles all three distinct entries.
`matrix2_inverse_conditioning` is the **divergence bound**: `recip` really approximates `1/det_fx` (the
*computed* determinant), so as an approximation of the exact `1/det` its error is
`≤ Erec0 + Edet·|wf|·|w|` with `|wf|·|w| = 1/(|det_fx|·|det|)` — bounded exactly when the matrix is
well-conditioned (`det` away from 0), diverging as `det→0`. This is the precise sense in which fixed-point
rounding does not make the filter diverge — the numerical-stability companion to the existing
`kalman2d_joseph_psd` structural (PSD) stability. `sorryAx`-free, ZERO new axioms.

**Gain/update composition** (same file): the gain `K = P·Hᵀ·S⁻¹` is a matrix product, so each entry is a
dot product of a `P·Hᵀ` row with an `S⁻¹` column — and the inverse error just bounded flows into it,
boundedly. `fxerr_dot2` (reusable) folds two `fxerr_mul`s + one `fxerr_add` (the `FixedPointCertifier`
additive error algebra) into a perturbed-operand dot product; `matrix2_inv_entry_fxerr` repackages an
inverse entry as an `FxErr` (magnitude + the `s+|cofactor|·Erec` error); **`kalman2_gain_entry_via_inverse`**
plugs the two inverse-column entries (built from the shared reciprocal, carrying `Erec`) into the gain dot
product and bounds the gain entry's fixed-point error — with `Erec` appearing explicitly, so the inversion
error is shown to propagate into the gain with no hidden amplification. `sorryAx`-free, ZERO new axioms.

**State-update forward error** (same file): **`kalman2_state_update_fxerr`** closes the estimate path
`inverse → gain → x'`. One updated estimate component `x'_i = x_i + (K_i0·y0 + K_i1·y1)` — the prior plus
the gain row dotted with the innovation `y = z − H·x` — has bounded fixed-point error, folding `fxerr_dot2`
(the `K·y` dot) and `fxerr_add` (`+ x_i`) over the gain entries' `FxErr` (which carry the inversion error).
So for the 2-measurement 2×2 update the whole estimate path is now forward-error-bounded end to end. (The
covariance update is the same kind of fold; its PSD is the separate structural `kalman2d_joseph_psd`.)
`sorryAx`-free, ZERO new axioms.
(General n×n inversion-stability via Cholesky/LDLT remains the larger arc; at fixed 2×2 the closed form is
equivalent and lands on the current FPGA substrate. Next: matrix MMSE-optimality + a small-n unrolled RTL
kernel.)

### New — the AXI-Stream wrapper control FSM is deadlock-free + drop-free, proven (`MachLib/AxiStreamWrapper.lean`)

**`conservation`**, **`round_trip`**, **`validIn_pulse`**, **`no_stuck_state`** (+ the `*_leaves_on_*` /
`*_holds` lemmas): to feed the 100 MHz Kalman kernel live sensor data it needs a standard AXI4-Stream
`ready`/`valid` bus with backpressure — and the risk a hand-written wrapper carries is exactly that its
control FSM could **deadlock, drop a sample, or re-trigger the multi-cycle core mid-computation**. This
proves it can't. The wrapper is a 3-state Moore machine (`idle`/`busy`/`present`) around the multi-cycle
core; the proofs are **pure discrete reasoning over `Bool`/`Nat` — no `MachLib.Real`, zero MachLib axioms**
(`no_stuck_state` depends on no axioms at all; the rest only on Lean core). SAFETY: `validIn_pulse` — the
core's `valid_in` is a 1-cycle pulse, never re-asserted mid-run (timing contract respected);
`conservation` — `accepted n = emitted n + occ(state)` with `occ ∈ {0,1}`, so at most one sample in flight
and, since input is accepted only from `idle`, an in-flight sample is never overwritten (**no dropped
sample**, `no_drop`); `present_holds` — the output is held with `tvalid` asserted under downstream
backpressure (AXI no-retraction). LIVENESS: each waiting state `*_leaves_on_*` its enabling signal and
`*_holds` correctly meanwhile; `no_stuck_state` — no absorbing state; `round_trip` — from `idle`, once the
three signals arrive the wrapper accepts one input, runs the core, emits **exactly one** output, and
returns to `idle` in a bounded window, with `accepted`/`emitted` each advanced by one. The same FSM the
RTL wrapper implements — proof and circuit share one definition. `sorryAx`-free, ZERO new axioms.

### New — the Kalman **estimate recursion** fixed-point error, coupled (`MachLib/KalmanEstimateRecursion.lean`)

**`kalman_estimate_recursion_fixed_point`** and **`kalman_estimate_recursion_nonexpansive`**: the
coupled half of the recursive fixed-point error — the *estimate* `m`, not just the variance `P`. Unlike
the autonomous variance map, the estimate update `m_n = (1−K_n)·m_{n-1} + K_n·z_n` is a *time-varying*
affine map, and the computed and exact orbits follow *different* maps (computed gain `Kc_n` vs exact
`Ke_n`). Expanding the error gives `δm_n = (1−Kc_n)·δm_{n-1} + (Kc_n−Ke_n)(z_n−m⋆_{n-1}) + τ_n`, so two
forcings ride on the contraction: the gain error `Kc_n−Ke_n` (**where coupling to the variance error
enters** — `K` is a Lipschitz function of `P`) and the update round-off `τ_n`. Proven by a new general
backbone lemma **`nearby_maps_trajectory_bound`** (two orbits under nearby `L`-Lipschitz maps stay close:
`|xc n − xe n| ≤ (σ+ρ)·geom L n`), which generalizes `local_lipschitz_trajectory_bound` from same-map to
different-map — instantiated at `Ac n x = x + Kc n·(z n − x)`, `Ae n x = x + Ke n·(z n − x)`. The
gain-error×innovation bound `ρ` is the hypothesis carrying the coupling (the honest interface, exactly as
`kalman_update_1d_fwd_error` takes `E_recip` as a hypothesis); `σ` the estimate update's own round-off.
At gains in `[0,1]` the accumulation is additive `(σ+ρ)·n`; for a strict contraction it is bounded
uniformly at `(σ+ρ)/(1−L)`. Together with the variance bound this completes the recursion's fixed-point
error, both halves. `sorryAx`-free, ZERO new axioms.

The coupling is then made **numeric**, not a hypothesis: **`kalman_gain_map_lipschitz`** proves the gain
`K(P)=P/(P+r)` is `r/(b+r)²`-Lipschitz on `{P≥b}` (the variance map's `r²/(b+r)²` divided by `r`, since
`g=r·K`), so **`kalman_gain_error_bound`** derives `|Kc−Ke| ≤ γ + (r/(b+r)²)·|δP|` (gain round-off `γ`
plus the *variance* error propagated through the gain), and **`kalman_estimate_recursion_coupled`**
composes it with the estimate bound to give `|mc n − me n| ≤ (σ + (γ + (r/(b+r)²)·DP)·Z)·geom L n` — `ρ`
fully derived from the variance error `DP`, the innovation bound `Z`, and the two round-offs. The
variance → gain → estimate coupling is now machine-checked end to end. `sorryAx`-free, ZERO new axioms.

### New — the Kalman **variance recursion** has a bounded RECURSIVE fixed-point error (`MachLib/KalmanVarianceRecursion.lean`)

**`kalman_variance_recursion_fixed_point`** and **`kalman_variance_recursion_nonexpansive`**: the
*accumulated* fixed-point error over the recursion, not just one step — what a `filter` needs beyond a
`measurement update`. The posterior-variance map `g(P) = P·r/(P+r)` is autonomous (depends on neither the
estimate nor the measurement), so its recursion is a clean scalar contraction with no coupling. Writing
`w = 1/(P+r)` gives `g(P) = r − r²·w`, hence `g(P) − g(P⋆) = r²·(P−P⋆)·w·w⋆`, so `g` is
`r²/(b+r)²`-Lipschitz on `{P ≥ b}` (**`kalman_var_map_lipschitz`**): nonexpansive (`L=1`) at `b=0`,
strictly contracting (`L<1`) for `b>0`. This drops straight into the pre-existing contraction backbone
(`local_lipschitz_trajectory_bound` / `contraction_certificate`): the Q16.16 variance recursion stays
within `ε·geom L n` of the exact real recursion over `n` steps — `≤ ε·n` at `b=0` (additive `≈N·ulp`
growth, unconditional), and bounded UNIFORMLY for all `n` at `ε/(1−L)` when `b>0`. The estimate (`m`)
recursion is the coupled follow-on (its per-step error feeds on the variance error through the gain);
the variance bound here is its prerequisite. `sorryAx`-free, ZERO new axioms.

### New — the fixed-point Kalman kernel is near-MMSE-OPTIMAL, machine-checked (`MachLib/KalmanUpdateFixedPoint.lean`)

**`kalman_update_1d_fx_near_mmse`** and **`kalman_update_1d_conditional_mse_near_optimal`**: the
*composition* the flagship claim rests on, proved rather than asserted. Two prior results —
(1) the real posterior mean is MMSE-optimal (`posterior_mean_mmse`), and (2) the Q16.16 kernel output is
within `ε` of that real mean (`kalman_update_1d_fwd_error`) — do NOT by themselves give "the fixed-point
kernel is near-optimal". The join is proved: since the conditional MSE of any estimate `c` of `X | Y=y`
is exactly `τ² + (c − m(y))²` (parallel-axis, no cross term), the fixed-point output `kalman_hw`, being
within `ε` of the posterior mean `m`, has conditional MSE sandwiched
`τ² ≤ τ² + (kalman_hw − m)² ≤ τ² + ε²`. So the *implemented* estimator's excess risk over the *provably
optimal* one is `≤ ε²`, with `ε = s + |z−x|·(s + |p|·E_recip)` from the datapath forward-error. This
closes the "two rigorous things, join asserted" gap between MMSE optimality and finite precision.
`sorryAx`-free, ZERO new axioms.

### New — `∫₀^∞exp(-t²)dt = √π/2`, from scratch, zero new axioms (`MachLib/GaussianLaplaceRoute.lean`)

**`gaussianImproperIntegral_eq_sqrt_pi_div_two`**: `gaussianImproperIntegral = sqrt pi / (1 + 1)` —
the classical Gaussian integral, proven end to end in MachLib's Mathlib-free real-analysis base.
Built via a Laplace/Feynman parameter-differentiation trick: `F(t) := gaussianI(t)²`,
`G(t) := ∫₀¹exp(-t²(1+x²))/(1+x²)dx`, `F' = -G'` via a from-scratch Leibniz differentiation-
under-the-integral-sign theorem (`hasDerivAt_GFn`), hence `F+G` constant on `[0,∞)` (an
open-interval FTC-uniqueness argument extends it down through the boundary kink at `t=0`, where
`gaussianI` — hence `F` — has no two-sided derivative), hence
`gaussianImproperIntegral² = F(0)+G(0) = 0 + π/4`, hence the result via `sqrt_sq` +
`mul_left_cancel`. `π` enters ONLY as a bare trig fact (`cos(π/2)=0`/`sin(π/2)=1`) — `atan(1)=π/4`
is DERIVED, not axiomatized, via a double application of `ftc_riemann` to the same trivial
integral `∫₀^{π/4}1dθ`. `sorryAx`-free, ZERO new axioms anywhere in the arc that built this (300
pinned, unchanged from before this project started). ~2144 lines / 138 theorems/defs, built
across roughly 30 pushes. The earlier disk/square-sandwich route (`GaussianDiskSandwich.lean`,
`D(R)≤S(R)≤D(R√2)`) remains a complete, correct, standalone result — abandoned as the critical
path only because its own derivative needs genuine 2D polar coordinates this 1D-only codebase
doesn't have.

### New — the scalar Kalman/Gaussian update is MMSE-optimal, from scratch, zero new axioms (`MachLib/GaussianConjugacy.lean`)

On top of the √π result and a full from-scratch second-moment theory of the scalar Gaussian
(`MachLib/GaussianDensityIntegral.lean`: `∫dens=1`, mean `μ`, variance `σ²`, and the parallel-axis
decomposition `∫(x-c)²dens = σ²+(c-μ)²`), MachLib now proves the scalar Gaussian-conjugate Bayesian
(Kalman) update is the **minimum-mean-squared-error estimator** — with no measure theory, no 2-D
integration, and ZERO new axioms (300 pinned, unchanged).

- **`jointDensity_conjugacy`**: the Bayesian conjugacy factorization. For prior `X~N(μ,σ²)` and
  measurement `Y=X+N` with independent noise `N~N(0,r²)`, completing the square factors the joint
  density as marginal `Y~N(μ,σ²+r²)` times posterior `X|Y=y ~ N(m(y),τ²)`, where `m(y)=μ+K(y-μ)`,
  `K=σ²/(σ²+r²)` (Kalman gain), `τ²=σ²r²/(σ²+r²)`.
- **`jointDensity_marginal_tendsto`**: integrating `x` out leaves the marginal `Y~N(μ,σ²+r²)` — no
  new Gaussian-integral identity needed (validates the scalar-density scoping).
- **`posterior_mean_mmse`** / **`posteriorMSE_tendsto`**: the posterior/Kalman mean minimizes the
  conditional MSE `τ²+(c-m(y))²`, achieving the minimum posterior variance `τ²` (parallel-axis at
  the posterior).
- **`optimalMSE_tendsto`** / **`mse_lower_bound`**: the posterior-mean estimator's total
  (unconditional) MSE is exactly `τ²`, and no continuous estimator beats it — via the iterated-
  integral device (inner `x`-integral closed-form by parallel-axis, single 1-D outer `y`-integral).
- **`postMean_eq_kalman`**: cross-checks the optimal gain against the pre-existing purely-algebraic
  `kalman_gain`.

`sorryAx`-free. Honest scope: scalar state+measurement; "any estimator" = any continuous
`φ:Real→Real` (MachLib has no measurable-function type). Runtime witness:
`corpus/eml/lane5_open_problems/kalmanMMSE_witness.py` (quadrature confirms every closed form and
that the posterior mean is the numerically-verified MMSE estimator, min MSE = `τ²`).

## [Unreleased] — 2026-07-09

### New — absolute, cancellation-tolerant forward-error fold (`MachLib/AbsoluteError.lean`)

The certifier's `ForwardError.Renc` is a *relative* enclosure: it composes only on a cancellation-FREE
tree of non-negative quantities (`cosh`, `x²+y²`). General EML arithmetic cancels (`a − b` with `a ≈ b`),
where the relative bound is vacuous. This adds the honest general answer — the **absolute** running-error
bound (Higham, *Accuracy and Stability*, §3.4): **`MachLib.Real.AbsEnc E fl e := |fl − e| ≤ E`**, with
`sorryAx`-free node lemmas `absenc_exact` / `absenc_round` (leaves) and `absenc_add` / `absenc_sub` /
`absenc_mul` (arithmetic). The **`sub` node carries the SAME bound as `add`** — cancellation destroys
*relative* accuracy, never the *absolute* bound, which is exactly what makes this fold general.

Capstone **`absenc_sub_rounded`** reproduces the *exact* `u·(2+u)·(|xe|+|ye|)` bound that
`CompositeRuntimeError.eml_fwd_reduces_to_primitives` proves by hand for `eml = exp x − log y`, now a
two-line instance of the general `absenc_sub` fold (one ring identity). The bespoke composite-error proof
is thereby subsumed by a reusable per-node accumulation. `MachLib.Real`-only, no Mathlib.

**Wired through the emitted C (`MachLib/AbsoluteBridge.lean`).** `FloatRealBridge`'s `pipeline_*`
connected T1's emitted C to T3's *relative* forward error, but only for cancellation-free trees. The
absolute fold now closes that gap on the canonical CANCELLING kernel — the 2×2 determinant / cross-product
`x·y − z·w` (`detEML`). **`pipeline_det`**: the value the *emitted C* computes (`evalC ∘ emitC`), through
`toR`, is within `u·(2+u)·(|X·Y|+|Z·W|)` of the exact `X·Y − Z·W` — the same EML→emitC→evalC→toR span as
the relative pipeline, now VALID UNDER CANCELLATION (`X·Y ≈ Z·W`, where `Renc` is vacuous) and with NO
sign hypothesis on the inputs. `sorryAx`-free; assembled from two `br.mul` roundings + one `br.sub` via
`absenc_sub_rounded` + `emitC_correct`.

**Generalised to any arithmetic tree (`MachLib/AbsoluteFold.lean`).** `pipeline_det` was one kernel; this
folds the `absenc_*` nodes over an ARBITRARY literal/variable/`+`/`−`/`×` EML tree. Recursive `exactR`
(exact real interpretation) and `absErr` (accumulated absolute bound) — `noncomputable`, mutual with a
`List EML` companion like `evalEML` so the node equations reduce structurally — plus one structural
induction over the fragment `IsArith`. **`pipeline_arith`**: for any `IsArith e`, the value the emitted C
computes, through `toR`, is within `absErr … e` of the exact `exactR … e`; every node discharged by its
`absenc_*` lemma + the bridge rounding, leaves exact, cancellation handled by `absenc_sub`. `pipeline_det`
is now literally the `detEML` instance (`isArith_detEML`). `sorryAx`-free.

The `neg` node is included: `FPBridge` gains a `neg` field — an EQUALITY `toR (-a) = -(toR a)`, not a
`RoundsW`, because IEEE-754 negation is exact (sign-bit flip, no rounding) — and `absenc_neg` carries the
absolute error through unchanged (`|(-flx)−(-xe)| = |flx−xe|`). So `IsArith` / `pipeline_arith` now cover
literal / variable / `+` / `−` / `×` / **negation**.

**Transcendental node core — `absenc_lip` (`MachLib/AbsoluteError.lean`).** The forward-error rule for a
unary primitive `f`: if `f` is `L`-Lipschitz, the input is within `Ex`, and the primitive rounds within
`Eround`, then the output is within `Eround + L·Ex` — input error amplified by the Lipschitz sensitivity,
plus the primitive's own rounding. This is the reusable heart of the `tr1` (`exp`/`sin`/`tanh`/…) fold
node; instantiating it per primitive uses MachLib's existing Lipschitz lemmas (`TrigLipschitz`,
`HyperbolicLipschitz`) + the primitive's `RoundsW` spec. `sorryAx`-free.

**Transcendental over an arithmetic subtree, through the emitted C — `pipeline_tr1_of_arith`
(`MachLib/AbsoluteFold.lean`).** A unary primitive `t` (real semantics `f`, `L`-Lipschitz) applied to ANY
arithmetic `e`: the emitted C's value, through `toR`, is within `Eround + L·(absErr … e)` of the exact
`f (exactR … e)` — the arithmetic fold's absolute error amplified by the primitive's Lipschitz
sensitivity, plus its rounding. Composes `evalEML_absErr` (the whole arithmetic fold) with `absenc_lip`
across `emitC_correct`, so the absolute cancellation-tolerant certificate now reaches one transcendental
layer over any arithmetic tree (e.g. `sin(x·y − z·w)`). Honest scope: covers the GLOBALLY-Lipschitz
primitives (`sin`/`cos`/`tanh`/`arctan`/`abs`, `L = 1`); `exp`/`log`/`sinh`/`cosh`/`tan` need a
local-Lipschitz variant, and the binary `tr2` primitives (`eml`, `pow`) decompose into unary + arithmetic
nodes — the remaining follow-ons. `sorryAx`-free.

**Local-Lipschitz node + the `exp` instance (`MachLib/AbsoluteError.lean`, `MachLib/ExpLipschitz.lean`).**
`absenc_lip_local` — the same forward-error composition as `absenc_lip`, but `f` need only be `L`-Lipschitz
on `[lo,hi]` provided BOTH the input and the exact value lie there (the two range hypotheses are the honest
cost of leaving the globally-Lipschitz class). `ExpLipschitz` discharges the hypothesis for the canonical
unbounded-derivative primitive: `exp_lip_lt`/`exp_lip_local` prove `exp` is `exp hi`-Lipschitz on
`(−∞, hi]` (MVT slope `exp c ≤ exp hi`, via `mean_value_theorem_ct` + `HasDerivAt_exp` + `exp_monotone` —
the sound closed-interval MVT), and `absenc_exp_local` assembles the `exp` forward-error node: input within
`Ex`, both in `[lo,hi]` ⟹ output within `Eround + (exp hi)·Ex`. So the fold's transcendental layer now
reaches the unbounded-derivative primitives, not just the globally-Lipschitz ones. `sorryAx`-free.

**Remaining local-Lipschitz primitives — `log`/`sinh`/`cosh` (`MachLib/TransNodes.lean`).** Completes the
unbounded-derivative set. `log_lip_lt`/`log_lip_local`: `log` is `1/lo`-Lipschitz on `[lo, ∞)` (`lo > 0`) —
the MVT slope `1/c ≤ 1/lo` for `c ≥ lo`, via `mean_value_theorem_ct` + `HasDerivAt_log_pos` +
`div_le_div_pos`; `absenc_log_local` gives its forward-error node (`Eround + (1/lo)·Ex`). `sinh`/`cosh`
already have bounded-domain Lipschitz bounds in `HyperbolicLipschitz` (`cosh R`/`sinh R` on `|·| ≤ R`);
`absenc_sinh_local`/`absenc_cosh_local` wrap them into `absenc_lip_local` nodes. So all five
non-globally-Lipschitz primitives (`exp`, `log`, `sinh`, `cosh` — `tan` excluded, poles) now have absolute
forward-error nodes. `sorryAx`-free.

**Recursive nesting — arbitrary arithmetic + transcendental trees (`MachLib/AbsoluteFoldNest.lean`).** The
fold previously stopped at ONE transcendental layer; this closes the recursion. `IsFold` allows `tr1`
nodes ANYWHERE (transcendental-of-transcendental, arithmetic-of-transcendental, …) for the primitives a
`globLip` predicate marks globally-Lipschitz. **`nested_fold`/`pipeline_nested`**: for any `IsFold e`, the
emitted C's value, through `toR`, is within SOME absolute bound of the exact `exactRn … e` over the whole
nested tree. The move that makes recursion clean: the bound is EXISTENTIAL (`∃ E, AbsEnc E …`), so the
`tr1` step needs no weakening (the witnessed `E` may depend on the float eval) — each node just assembles
`E` from the sub-bounds via its `absenc_*` lemma. `exactRn` (exact interpretation with a `tr1` case) is the
only new recursive def (`noncomputable`, mutual-with-`List`). Non-vacuity: `sin(x·y − z·w)` — a
transcendental over the cancelling determinant — is in the fragment. Scope: globally-Lipschitz `tr1`
primitives (`sin`/`cos`/`tanh`/`arctan`/`abs`); the local-Lipschitz ones need per-node domain tracking
through the nesting, a further extension. `sorryAx`-free.

**Local-Lipschitz transcendental over an arithmetic subtree (`MachLib/AbsoluteFoldLocal.lean`).** The
local analog of `pipeline_tr1_of_arith`: an `exp`/`log`/… node over an arithmetic subtree, where the
primitive is Lipschitz only on `[lo,hi]` and both the computed and exact inputs are supplied to lie in
`[lo,hi]`. `pipeline_tr1_of_arith_local` composes `evalEML_absErr` with `absenc_lip_local`, and
`pipeline_exp_of_arith` (`L = exp hi`) / `pipeline_log_of_arith` (`L = 1/lo`) are the concrete instances
(from `ExpLipschitz`/`TransNodes`). So the emitted-C certificate now reaches `exp(x·y − z·w)`,
`log(…)`, etc. Honest scope: this is ONE local transcendental layer over arithmetic; FULL recursive
local-Lipschitz nesting is harder — the domain condition at each node depends on the accumulated absolute
error (existential), so range and error must propagate together (interval arithmetic with directed
rounding). That coupling is the remaining open piece. `sorryAx`-free.

**FULL local-Lipschitz nesting — via magnitude propagation (`MachLib/AbsoluteFoldNestMag.lean`).** Closes
the coupling above for the symmetric-domain locals. The move: propagate a MAGNITUDE bound `M ≥ |exactRn e|`
(clean — `|a+b| ≤ M_a+M_b`, `|a·b| ≤ M_a·M_b`, no interval sign-cases) alongside the existential error `E`;
the FLOAT-image magnitude is then DERIVED, not tracked (`|toR (evalEML e).toF| ≤ M + E` straight from
`AbsEnc`), so a local `tr1` node over a symmetric domain uses `R = M + E` (both inputs land in `[-R,R]`)
with per-primitive `LipOf t R` / `MagOf t M`. `nested_fold_mag`/`pipeline_nested_mag` carry `∃ E M,
AbsEnc E … ∧ |exactRn e| ≤ M` and reuse `exactRn`/`IsFold` unchanged. `pipeline_nested_exp` is the concrete
`exp` instance (Lipschitz `exp R` on `[-R,R]` from `exp_lip_local`; magnitude `exp M`), so `exp(exp(x·y −
z·w))` — a local primitive nested over itself over cancelling arithmetic — is covered end-to-end at
ARBITRARY depth (example: `exp(exp x)` ∈ the fragment). `log` stays out (one-sided domain). So both the
globally-Lipschitz (`AbsoluteFoldNest`) and the symmetric-local (`exp`/`sinh`/`cosh`) recursive nestings
are now done. `sorryAx`-free.

### Hardened — the unsound open `rolle` axiom is RETIRED; the library has no Rolle but the sound `rolle_ct` (`MachLib/Rolle.lean`)

Grounding MachLib.Real against Mathlib's ℝ surfaced that the old `rolle` axiom was **unsound as stated**: it
asked only for OPEN-interval differentiability (`a < c → c < b`) with **no** endpoint continuity, so it is not a
theorem of ℝ — counterexample `f x = x` on `(0,1)` with `f 0 = f 1 = 0` (differentiable on the open interval,
`f 0 = f 1`, yet `f' ≡ 1 ≠ 0`). This release completes the repair begun with `rolle_ct` (the sound
closed-interval form, witnessed verbatim against Mathlib ℝ by `MonogateEML.RealModel.rolle_witnessed`):

* **Every** consumer migrated to `rolle_ct` / `mean_value_theorem_ct`: the whole Khovanskii footprint
  (pure-exp explicit + unconditional bounds, the mixed exp/log barrier, the `…_le_47` and
  `eml_barrier_bounded_zeros` showcases) plus every utility (Sturm non-oscillation, Wronskian proportional,
  trig / hyperbolic Lipschitz — all differentiate entire functions or on strict subintervals, so closed diff
  is always available).
* The unsound `axiom rolle` **and** the open-hypothesis `theorem mean_value_theorem` (itself proved from
  `rolle`, hence unsound-as-stated) are **DELETED**. `rolle_ct` is now the library's only Rolle. Any future use
  of an open-interval Rolle is a compile error — it no longer exists.
* **Regression gate:** `tools/claim_audit/claim_audit.py` gains `forbid_axioms_exact` (whole-token axiom
  matching — a plain substring forbid can't tell `MachLib.Real.rolle` from the sound `MachLib.Real.rolle_ct`);
  the 8 Khovanskii flagship claims now forbid `MachLib.Real.rolle` exactly. `#print axioms` on all flagships:
  `rolle_ct` only, no bare `rolle`, no `sorryAx`. Claim-audit PASS (16/16), self-test PASS.

### Concrete showcase — `e^(e^x) − x·e^x` has at most 47 real zeros, machine-checked (`MachLib/KhovanskiiConcrete.lean`)

**`MachLib.KhovanskiiConcrete.eexp_barrier_zero_count_le_47`** — a named instance of the explicit Khovanskii
bound. The barrier `y₁ − x·y₀` is, along the depth-2 tower (`y₀ = eˣ`, `y₁ = e^(eˣ)`), exactly
`e^(e^x) − x·e^x`; it is a degree-1 chain-2 polynomial, so its zero count on any interval where it is
somewhere nonzero is `≤ Ndep 0 1`, and `Ndep 0 1` **computes to 47** (`Ndep` is a genuine kernel-reducible
`Nat` recurrence — the `= 47` is discharged by `decide`, not `native_decide`, so no `ofReduceBool` enters the
footprint). Non-vanishing is witnessed at `x = 0`, where the value is `e^(e^0) = e > 0` (`iterExp_pos`). This
turns the "at most 47 real zeros" figure from a hand-evaluated recurrence into a theorem, resting on `rolle`
alone — no `sorryAx`, no `zero_count_bound_classical`, and (being a pure-exp barrier) no analyticity, log, or
reciprocal.

The same file also exercises the **mixed** capstone on a genuinely exp+log function.
**`MachLib.KhovanskiiConcrete.eml_barrier_bounded_zeros`**: `e^x − log x` (the fundamental `eml` operation
applied to `x`) has finitely many zeros on any interval in the positive reals containing `1`, a machine-checked
instance of `eml_eval_boundedZeros_unconditional`. This one is qualitative (a finite ceiling exists) and carries
the honest *mixed* footprint — `rolle` plus the real-analyticity identity theorem
(`analytic_finite_zeros_compact`) and the logarithm — but is still `sorryAx`- and
`zero_count_bound_classical`-free. Together the two showcases pin the honest distinction concretely: the
pure-exp bound is Rolle-only with a literal ceiling; the mixed bound adds the identity theorem and gives
finiteness without an explicit constant.

### exp arm CLOSED — the full mixed exp/log/reciprocal EML barrier bound is unconditional (`MachLib/PfaffianExpHard.lean`)

**`MachLib.eml_eval_boundedZeros_unconditional`** — the Khovanskii-type finiteness bound for arbitrary-depth
**mixed** exp/log/reciprocal EML barriers, machine-checked. Both classical arms are discharged: the exp arm
(`exp_hard`) via the new `expEliminate` construction (B1–B4 in `PfaffianExpEliminate` / `PfaffianExpTrim` /
`PfaffianExpWronskian` / `PfaffianExpHard`), the log arm via `log_hard_proof`. `#print axioms` →
`propext` / `Classical.choice` / `Quot.sound`, the `Real` interface, `rolle`, plus the real-analyticity
package (`analytic_finite_zeros_compact` and the identity-theorem family) and the logarithm / reciprocal
derivative rules — with **no `sorryAx` and no `zero_count_bound_classical`**.

Honest scoping, held to on the public page too: the mixed bound is *qualitative* (a finite ceiling exists,
without an explicit constant), and its analytic footprint is genuinely **larger than Rolle** — the degenerate
"proportional" leaves are retired by the identity theorem (a real-analytic function has finitely many zeros
on a compact interval unless it vanishes identically). Rolle carries the descent; analyticity enters only for
those leaves.

By contrast the pure iterated-exponential bound stays Rolle-only, and is now *effective*.
**`MachLib.IterExpDepthN.chainN_khovanskii_bound_explicit`** gives the explicit ceiling `Ndep m D`; its
`#print axioms` footprint has **no analyticity, no logarithm, no reciprocal** — `rolle` is the sole analytic
input. `Ndep` is now a genuinely computable, `#eval`-able closed-form recurrence (a gratuitous
`noncomputable` on `budgetMax` was removed), though its values are a height-`m` tower of exponentials, so
evaluating beyond a small depth overflows the interpreter.

Both claims are pinned in `tools/claim_audit/claims.json` so the distinction (pure-exp = Rolle-only; mixed =
Rolle + identity theorem, still `sorryAx`- and `zero_count_bound_classical`-free) is a standing CI gate.

### Hardened — analytic base collapses to a single axiom: `zero_count_bound_by_deriv` is now a THEOREM (`MachLib/Rolle.lean`)

**`MachLib.Real.zero_count_bound_by_deriv`** — previously an `axiom`, now **derived from `rolle`**. The whole
iterated-exponential tower's analytic foundation therefore bottoms out at the SINGLE axiom `rolle` (plus the
field/order interface); the separate zero-count axiom is gone. `#print axioms zero_count_bound_by_deriv` →
`propext`, `Classical.choice`, `Quot.sound`, `rolle`, and the `Real` order / `HasDerivAt` primitives — **NO
`sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`**.

Construction (all supporting defs `private` to `Rolle.lean`): sort the `Nodup` zeros of `f` into strictly
increasing order via `List.mergeSort` with a classical `≤`-comparator (`leB`), then `interleave_from` applies
`rolle` between each consecutive pair to produce a zero of `f'` strictly between them. Those bracket points are
themselves strictly increasing (each lands in a disjoint sub-interval, enforced by the `> hd` recursion
invariant), hence `Nodup` and of length `zeros_f.length − 1`; feeding that list to `hf'_bound` gives
`zeros_f.length ≤ N + 1`. Uses Lean 4.14 core `List.mergeSort` / `List.Perm` / `List.Pairwise` (no Mathlib).
All 138 modules rebuild; every downstream consumer (`KhovanskiiReduction`, `SingleExpKhovanskii`,
`InnerKhovanskii`, `PolynomialRootCount`, …) picks up the theorem by name — signature unchanged.

### Added — Khovanskii ∀N: **ARC CLOSED** — the UNCONDITIONAL arbitrary-depth bound (`MachLib/IterExpDepthNBoundUncond.lean`)

**`MachLib.IterExpDepthN.chainN_khovanskii_bound_unconditional`** — for **every** depth and every chain-`N`
polynomial not identically zero on `(a,b)`, `chainNFn p` has finitely many zeros. NO hypothesis. `#print axioms`
→ `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real` analytic interface (`rolle`, `exp`,
`HasDerivAt` calculus): **NO `sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`** — the
forbidden-axiom grep is empty. (As of the hardening entry above, `zero_count_bound_by_deriv` is itself a
theorem derived from `rolle`, so it no longer appears in this footprint — `rolle` is now the sole analytic axiom.)

The reduce arm's `Reducing` precondition — previously the explicit hypothesis `hRD` of
`chainN_khovanskii_bound_of_reducing` — is now a **theorem**, `establish_hnz_or_trim` (for any `q ≢ 0`, either
`hnzTower m q` (the deepest true-degree is nonzero, so the absorbed reduce descent `chainNReduce_descends_hnz`
fires) OR an eval-equal `synMeasure`-smaller phantom-trim). The assembly runs on the augmented measure `M5⁺`
(`chainNMeasure5p` = `(chainNMeasureCanon, synMeasure(inner))`), since the eval-invariant `chainNMeasureCanon`
cannot be lowered by an eval-preserving trim — the deep phantom-trim (`liftInner`) ties it and drops `synMeasure`.
Double-, triple-, and arbitrary-depth: all unconditional, all clean.

### Added — Khovanskii ∀N: PHASE C CLOSED — the reduce-descent for every depth (`MachLib/IterExpDepthNDescentInduction.lean`)

**`chainNReduce_descends`** — for a reducing `q : MultiPoly (k+2)` at ANY depth `k`, the reduce with the
full graded multiplier strictly lowers the eval-invariant measure `chainNMeasureEI k` in `nestedOrder (k+2)`.
This is the ∀N analog of the deep depth-2 `chain2MeasureCanonEvalInv_descends`, now proven for **every depth**
by induction. `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real`
interface (incl. `rolle`): **NO `sorryAx`, NO `zero_count_bound_classical`, NO `analytic_finite_zeros`**.

The induction, assembled from the whole Phase C stack:
- **`fullMult k q`** — the recursive graded multiplier: depth-2 base at `k=0`; at `k+1`, `gradedTop` +
  `liftLastY` of the lower multiplier for the projected leading coefficient (`dropLastY_liftLastY` recovers
  it — the multiplier-threading resolved).
- **`Reducing k q`** — the recursive reducing predicate (depth-2 conditions at `k=0`; non-phantom + positive
  top degree + `Reducing` of the projected leading coefficient at `k+1`).
- Base = `chainNReduce_evalinv_descent_base` (the transported depth-2 descent, via `chainNReduce 0 =
  chain2Reduce` + `chainNMeasureEI 0 = chain2MeasureCanonEvalInv`); step = the D-step
  `chainNReduce_evalinv_descent` fed the IH through `dropLastY_liftLastY`.

The ∀N reduce-descent — the tower's well-founded step — is complete. Remaining for the full ∀N Khovanskii
bound: Phase D (generalise Rolle/vehicle + the outer WF induction into `chainN_khovanskii_bound_unconditional`).

### Added — `liftLastY`, a right inverse of `dropLastY` (`MachLib/MultiPolyLiftLastY.lean`)

The ∀N descent's D(k)-by-induction wiring needs to thread the graded multiplier down the recursion: the
D-step's inner reduce carries multiplier `dropLastY m_rest`, and for the inductive `D(M)` (a *graded* reduce)
to match, `m_rest` must be the lifted lower multiplier. That requires a `dropLastY` right inverse, which did
not exist — this supplies it.

- **`liftLastY : MultiPoly n → MultiPoly (n+1)`** — embed as a polynomial free of the new top variable
  (structural: `y_i ↦ y_i` at a lower `Fin (n+1)` index; `const`/`varX` kept).
- **`dropLastY_liftLastY`** (`dropLastY (liftLastY x) = x`) and **`degreeY_top_liftLastY`** (`liftLastY x` is
  top-free). Pure structural induction; `#print axioms` clean.

Next: the recursive full graded multiplier (`fullMult`), the recursive reducing predicate, the base
reconciliation (`chainNReduce 0 (gradedTop 0 + const c) p = chain2Reduce c p`, holds since `Ffac 0 = y₀`),
and the `D(k)`-by-induction — then Phase D.

### Added — Khovanskii ∀N Phase C (brick 3b, steps 2a+2b): the S(k) and D(k) descent assembly (`IterExpDepthNDescent.lean`, `IterExpDepthNDescentD.lean`)

The mechanical core of the reduce-descent, both steps, given the inner descent:

- **`chainNReduce_syntactic_descent`** (S(k)) — the *syntactic* measure `(degreeY_top, chainNMeasureEI M of
  dropLastY(leadingCoeffY_top ·))` strictly drops under the depth-`(M+3)` graded reduce, given `hInner`
  (the depth-`(M+2)` reduce lowers the inner measure). Top degree preserved (`chainNReduce_fst_preserved`),
  inner drops via the transport + `hInner`, via `nestedOrder_of_snd`.
- **`chainNReduce_evalinv_descent`** (D(k)) — the *eval-invariant* measure `chainNMeasureEI (M+1)` strictly
  drops, via the phantom / non-phantom split: non-phantom ⇒ both measures = syntactic (brick 2) ⇒ S(k);
  phantom ⇒ `cdegYAt` of the reduce drops below `degreeY_top p` (brick 1) ⇒ first-component descent. The
  literal top index is confined to two `rw [Fin.ext hi]` wrappers; the main proof runs at the abstract index.

Both compile clean (`#print axioms` free of `sorryAx` / classical-citation). This is the ∀N analog of
`chain2MeasureCanonEvalInv_descends`, parameterized on `hInner`. What remains of Phase C: wire the
`D(k)`-by-induction (base `D(0)` = `chain2MeasureCanonEvalInv_descends`; step feeds `D(k)` as `hInner` to
`chainNReduce_evalinv_descent`) — the remaining subtlety is threading the *graded multiplier* + reducing
hypotheses through the recursion so the inductive `D(k)` matches `hInner`'s inner reduce.

### Added — Khovanskii ∀N Phase C (brick 3b, step 1): the inner-descent transport (`MachLib/IterExpDepthNDescent.lean`)

**`chainNMeasureEI_reduce_inner_eq`** — the eval-invariant measure of the depth-`(M+3)` graded reduce's
dropped top coefficient equals the measure of the depth-`(M+2)` reduce of `dropLastY (lcY_top p)`. Immediate
from brick 3a (full-env recursion) + Phase B (`chainNMeasureEI_eq_of_eval_eq`). This is the exact bridge the
syntactic descent `S(k)`'s inner step needs — with it, `S(k)`'s inner descent is `rw [this]; exact D(k−1)`.
Compiled first try; `#print axioms` clean. Remaining Phase C: the `S(k)/D(k)` induction proper (the fst-preserved
outer + this transport + the phantom split + the reducing-hypothesis threading).

### Added — Khovanskii ∀N Phase C (brick 3a): the recursion brick, FULL-ENV (`MachLib/IterExpDepthNRecursionFull.lean`)

`chainNReduce_dropLastY_recursion` closes the depth-`(M+3)`→`(M+2)` recursion **only on the chain values**;
the measure descent needs it on **every** environment (the eval-invariant measure's eval-invariance
quantifies over all envs — exactly why depth-3 needed the separate `chain3Reduce_dropLastY_lcY2_eval_eq_full`).

- **`chainNReduce_dropLastY_recursion_full`** — the ∀N, full-env version: the depth-`(M+3)` graded reduce's
  dropped top coefficient, at *any* environment, equals a depth-`(M+2)` reduce of `dropLastY (lcY_top p)`
  with multiplier `dropLastY m_rest`. Re-derived by replacing the chain-values `dropLastY_eval_IterExp'` with
  the framework `MultiPoly.eval_dropLastY` (env-restriction bridge `extEnv`/`dropLastY_eval_full'`) +
  `dropLastY_cTD_commute`, keeping the abstract-index discipline (top index a variable `i`, `hi : i.val =
  M+2`; `[local irreducible]` on the stuck recursors). Compiled first try. `#print axioms` clean.
- This closes the sub-gap that stood between Phase B and the descent: the descent's inner step
  (`chainNMeasureEI k (dropLastY lcY_top(reduce)) = chainNMeasureEI k (reduce_{k+2} of dropLastY lcY_top)`)
  now has its full-env eval-equality. Remaining Phase C: brick 3b, the S(k)/D(k) mutual induction assembling
  3a + the phantom bridge + `chainNReduce_fst_preserved` + D(k−1).

### Added — Khovanskii ∀N Phase C (brick 2): eval-invariant measure = syntactic on non-phantom (`MachLib/IterExpDepthNMeasureSyn.lean`)

**`chainNMeasureEI_eq_syntactic_of_nonphantom`** — for `q : MultiPoly (j+3)` whose top `y`-coefficient is
non-phantom, the eval-invariant measure `chainNMeasureEI (j+1) q` equals the *syntactic* form `(degreeY_top q,
chainNMeasureEI j (dropLastY (leadingCoeffY_top q)))`. Depth-generic analog of the depth-2
`chain2MeasureCanonEvalInv_eq_chain2MeasureCanon_of_nonphantom`; assembled from Phase C brick 1
(`cdegYAt_eq_degreeYAt_of_top`, `canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`) + Phase B
(`chainNMeasureEI_eq_of_eval_eq`, `dropLastY_eval_eq_of_topfree`). This is the swap that lets the
eval-invariant descent `D(k)` fall through to the syntactic descent `S(k)` on the non-phantom branch.
Compiled first try; `#print axioms` clean. Remaining Phase C: the `S(k)/D(k)` induction (S(k) assembles the
reduce machinery around the recursion brick + D(k−1); D(k) from S(k) + the phantom drop).

### Added — Khovanskii ∀N Phase C (brick 1): the phantom / non-phantom bridge (`MachLib/IterExpDepthNCanonBridge.lean`)

The base descent `chain2MeasureCanonEvalInv_descends` works by a **phantom / non-phantom split**: when the
top `y_i`-coefficient is *non-phantom* the canonical measure equals the syntactic one (deep syntactic
descent applies); when *phantom* the canonical degree `cdegYAt` strictly drops (first-component descent
outright). This is the key that turns the canonical-outer descent D(k) into a well-defined induction. This
brick supplies both directions of the split, index/depth-generic (the depth-2 originals were `MultiPoly 2`,
index `⟨1⟩`):

- **`ytopAt i q`** — the syntactic top `y_i`-coefficient (`getLast` of `yCoeffsAt`).
- **`cdegYAt_eq_degreeYAt_of_top` / `canonLcYAt_eq_ytop`** — non-phantom ⇒ canonical = syntactic.
- **`cdegYAt_lt_degreeYAt_of_top`** — phantom (+ positive syntactic degree) ⇒ `cdegYAt` strictly drops.
- **`canonLcYAt_eval_eq_leadingCoeffY_of_nonphantom`** — non-phantom ⇒ canonical leading coeff eval-equals
  syntactic `leadingCoeffY` (what the measure-equality consumes next).
- `#print axioms` clean (no `sorryAx`, no classical-citation). Next: the syntactic top-level measure
  `chainNMeasureSyn` + `chainNMeasureEI = chainNMeasureSyn` on the non-phantom branch, then the S(k)/D(k)
  mutual induction (S(k) from the recursion brick + D(k−1); D(k) from S(k) + the phantom drop).

### Added — Khovanskii ∀N Phase B: the uniform eval-invariant measure by recursion on depth (`MachLib/IterExpDepthNMeasureEI.lean`)

The depth-3 descent used the fully eval-invariant depth-2 measure (`chain2MeasureCanonEvalInv`) as its
inner nested component. The tower needs that inner measure at every depth, uniformly — this builds it.

- **`chainNMeasureEI k : MultiPoly (k+2) → NestedNat (k+2)`** — the depth-`(k+2)` eval-invariant canonical
  measure. Base `k=0` is *literally* `chain2MeasureCanonEvalInv` (so every induction bottoms out in the
  existing, already-proven depth-2 machinery — nothing to reconcile); step `k+1` pairs the canonical
  top-degree `cdegYAt` (Phase A) with the measure of the canonical leading coefficient projected one
  variable down via `dropLastY`.
- **`chainNMeasureEI_eq_of_eval_eq`** — the measure is **eval-invariant at every depth**, by induction:
  base `chain2MeasureCanonEvalInv_eq_of_eval_eq`; step combines Phase A's `cdegYAt_eq_of_eval_eq` (outer),
  `canonLcYAt_eval_eq_of_eval_eq` + the new `dropLastY_eval_eq_of_topfree` (the projected coefficient stays
  eval-equal), and the inductive hypothesis (inner).
- `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + honest `MachLib.Real`; **no `sorryAx`**.
- **Next (Phase C, the hard frontier)**: the reduce-descent — that this measure strictly decreases under
  the graded reduce. The algebraic engine is already ∀N (`chainNReduce_dropLastY_recursion`) and the
  eval-invariance just landed transports it; the genuinely-uncertain step is the canonical-outer descent
  `D(k)→D(k+1)`, which generalizes depth-3's reduce/trim/inner-trim case analysis.

### Added — Khovanskii ∀N Phase A: the index-generic canonical `y`-degree + eval-invariance (`MachLib/IterExpDepthNCanonDegree.lean`)

The measure the ∀N descent will use is *eval-invariant* — it forgets phantom leading `y`-terms that only
cancel semantically. Depth-2/3 built that per index (`cdegY0` at `⟨0⟩`, `cdegY1` at `⟨1⟩`, both in
`MultiPoly 2`); the tower needs it at the **top index of any depth**, uniformly. This brick supplies it.

- **`canonZeroB c`** — the one index-specific ingredient (the coefficient canon-zero test) made generic
  by a single **classical** definition: `decide (c vanishes everywhere)`. This makes canon-zero congruent
  under eval-equality by construction, so eval-invariance is nearly free. Every list-level helper reused
  (`rdw_cons`, `dropWhile_all`, `rdw_zero_of_all`, `listSubN`, `yCoeffsAt_entry_eval_zero_of_eval_zero`,
  `eval_eq_of_env_agree_off`) was already index-generic.
- **`cdegYAt i q`** (canonical `y_i`-degree) + **`cdegYAt_eq_of_eval_eq`** — degree eval-invariance ∀
  index, ∀ depth. Generic analog of `cdegY1_eq_of_eval_eq`.
- **`canonLcYAt i q`** (canonical leading `y_i`-coefficient) + **`canonLcYAt_eval_eq_of_eval_eq`** — the
  leading coefficient is eval-invariant at EVERY point (the classical test gives everywhere-agreement
  directly, so — unlike the structural depth-2 `canonLcY1` proof — no `env0` restriction is needed).
- `#print axioms` → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real` interface;
  **no `sorryAx`**, no classical-citation axiom. Phase B (the uniform eval-invariant measure by recursion
  on depth) plugs `cdegYAt`/`canonLcYAt` in at the top index and recurses via `dropLastY`.

### Added — Khovanskii ∀N: the depth-generic well-founded measure backbone (`MachLib/IterExpDepthNMeasure.lean`)

Next brick of the depth-N tower, on the critical path to the WF capstone. The depth-2/3 capstones each
cite a hand-built well-foundedness keystone for their arity (`natTripleLex_wf`, `natQuadLex_wf`); the ∀N
induction needs that family *uniformly*. This supplies it:

- **`MachLib.IterExpDepthN.NestedNat n`** — the depth-`(n+2)` measure codomain (`(n+1)`-deep nested `Nat`
  product); **`nestedOrder n`** — its nested lexicographic order (definitionally `nestedOrder 2` is the
  depth-2 `nestedLT`); **`nestedOrder_wf n`** — **well-founded for every `n`** by induction on depth
  (base `Nat.lt`, step `lexProd_wf`). `natPairLex/​natTripleLex/​natQuadLex_wf` are its `n = 1,2,3` slices.
- **`nestedOrder_of_fst` / `nestedOrder_of_snd`** — the two generic descent-lifting lemmas the capstone's
  arms need (drop the top component / tie it and drop the tail).
- `#print axioms` → **depends on NO axioms** (pure order theory; not even `propext`). This is the
  well-founded skeleton the ∀N reduce-descent will hang on. The algebraic heart of that descent — "the
  dropped top coefficient of the reduce IS a depth-(N−1) reduce" — is already machine-checked ∀N
  (`chainNReduce_dropLastY_recursion`). Still ahead: the uniform *eval-invariant* measure and its descent
  by induction on depth (base = chain2), then the ∀N Rolle/vehicle step and the capstone assembly.

### Added — verified day-count & accrual: coupon periods compose exactly (`MachLib/FinanceDayCount.lean`)

The second finance kernel — the lane is not a one-off. Same discipline as amortization, aimed at the
property a bond desk and an auditor argue about: **splitting a coupon period at an intermediate date must
preserve accrued interest.** Uses the **30E/360 (Eurobond)** convention, where every date `(y,m,d)` has a
single serial `360·y + 30·m + min(d,30)` and the day-count is the serial difference.

- **`MachLib.Finance.days30E360_additive`** — the headline: `days(A,B) + days(B,C) = days(A,C)` for ANY
  intermediate date. The day-count analogue of amortization's telescoping reconciliation — interest can't
  be manufactured by moving the accrual boundary. **Honest domain point**: this holds for 30E/360 because
  each date has one serial; the US 30/360 "bond basis" is *not* additive (its end-of-month rule depends on
  the other endpoint), so picking 30E/360 is a deliberate correctness decision.
- **`MachLib.Finance.accrual_additive`** — the money corollary: accrued interest (`notional·rateNum·days`)
  composes exactly across a split, because it is linear in an additive day-count.
- **`MachLib.Finance.days30E360_months`** — regularity: same day-of-month, `m` whole months apart ⇒ exactly
  `30·m` days. Equal calendar spacing ⇒ equal day-count ⇒ equal accrual (fair level coupons).
- **`MachLib.Finance.days30E360_full_year`** (`= 360`) and **`days30E360_nonneg`** (forward periods aren't
  negative).
- `#print axioms` (all five) → `propext`, `Quot.sound` ONLY — pure `Int`, not even `Classical.choice`
  (same minimal footprint as `amortization_reconciles`; calendars and money are exact integer objects, no
  float). Registered in `tools/claim_audit`. Runtime witness: `forge/reproduce/sims/daycount_sim.py`.

### Added — verified amortization (the finance-assurance lane opens) (`MachLib/FinanceAmortization.lean`)

- **`MachLib.Finance.amortization_reconciles`** — a fixed-rate amortization schedule in **integer
  cents** reconciles to the penny **exactly**: with per-period principal `b k − b (k+1)`, starting at
  the loan `P` and closing at `b N = 0`, the principal payments sum to exactly `P`. Exact (`=`, not
  `≤ ε`) and **rounding-mode-independent** (the final payment absorbs the accumulated rounding — how
  real schedules are built). `#print axioms` → `propext`, `Quot.sound` only (pure Int; not even the
  axiomatized-Real base — money is decimal fixed-point, and this proof never touches a float).
- **`MachLib.Finance.roundHalfEven_half_ulp`** — round-half-to-even (banker's rounding) is correct to
  within half a cent per period: `−den ≤ 2·(den·round − num) ≤ den`. `#print axioms` → Lean's three
  only, no `sorryAx`.
- **Why this lane**: the finance-translatable core of the project is the fixed-point/decimal-rounding
  + contraction infrastructure (FPModel / FixedPointCertifier / ClosedLoopSafety) — *not* the
  Khovanskii frontier, which is pure symbolic math with no dollar attached. This is the first brick
  pointing that infrastructure at money: the runtime schedule (`forge/reproduce/sims/amortization_sim.py`),
  certified.

### Added — the accumulated rounding error stays inside a certified envelope (`MachLib/FinanceEnvelope.lean`)

Deepens the amortization kernel from *reconciles* + *½¢-per-period* to a **global** bound: how far the
rounded balance trajectory can drift from the exact-arithmetic one over the whole loan. The drift obeys
`e_{k+1} = g·e_k + ρ_k`, `e_0 = 0`, `|ρ_k| ≤ c` (`g = 1+r`, `c = ½` cent) — a linear recurrence with
bounded input.

- **`MachLib.Real.error_within_envelope`** — the abstract core, the **expansion dual** of
  `MachLib.Real.safe_envelope_invariant`: for `g ≥ 1`, `|e_k| ≤ errEnvelope g c k` for all `k`. The
  safety envelope is a *contraction* (`g<1`) settling into a fixed box `X=δ/(1−ρ)`; this is the *growth*
  regime (`g>1`) where the compounded error still lives inside a growing, explicit envelope
  `cap_k = c·(gᵏ−1)/(g−1)`. Same proof shape (triangle + `mul_le_mul_of_nonneg_left` + `add_le_add_both`
  under induction).
- **`MachLib.Real.errEnvelope_eq_geomSum` / `geomSum_closed`** — `cap_N = c·Σ_{j<N} gʲ` and
  `(g−1)·Σ_{j<N} gʲ = gᴺ−1`, i.e. the recognizable `c·(gᴺ−1)/(g−1)`, both proven **without division**.
- **`MachLib.Real.amortization_drift_within_envelope`** — the punchline: the rounded schedule `b`
  (`b_{k+1}=g·b_k−pmt+ρ_k`) never leaves `cap_k` around the exact schedule `B` (`B_{k+1}=g·B_k−pmt`),
  for ANY per-period rounding `|ρ_k| ≤ c`. With `c=½` cent this bounds how far per-period interest
  rounding can push the balance off the exact-arithmetic path — connecting the local ½¢ fact to a global
  guarantee. For the zoo's `$250k @ 6% / 360mo` loan the certified **worst-case** `cap_N ≈ $5.02` (every
  rounding adverse and fully compounding); the **measured** drift is only `~$0.05`, because real
  per-period roundings mostly cancel — the rounded trajectory sits well inside the envelope, exactly as
  the safety envelope's margin works. (That worst-case cap is a separate quantity from the ~$3.66
  final-payment adjustment, which is dominated by rounding the level payment, not the per-period interest.)
- `#print axioms` (all four) → `propext`, `Classical.choice`, `Quot.sound` + the honest `MachLib.Real`
  interface ONLY: **no `sorryAx`**, no classical-citation math axiom — same footprint class as the
  safety envelope. **Mechanization note**: `mach_mpoly` reifies its bracket atoms in the *outer*
  elaboration context, so it cannot see an `induction`-introduced local (`geomSum g n`); each ring
  identity is therefore proven once as a top-level lemma over plain variables and `exact`-ed at the use
  site. (`mach_ring` avoided per its known silent-`sorry` failure mode.)

## [Unreleased] — 2026-07-01

### Added — Frontier-1 lemma (1) proven for EVERY depth `N` (`33a819a`)

- **`MachLib.IterExpDepthN.leadingCoeffYtop_cTD_eval_IterExpN`** — the
  top-`leadingCoeffY`-under-`chainTotalDeriv` product-injection identity, now
  proven for **every** depth `N = M+2` (not just the closed depths 2 and 3):
  `eval(lcY_top(cTD p)) = eval(cTD(lcY_top p)) + (degreeY_top p)·eval(Ffac M · lcY_top p)`,
  top `⟨M+1⟩`, injection factor `Ffac M = y₀·…·y_M`. This is the first genuinely
  general-`N` brick of the depth-N tower and the step the frontier notes called
  "the one genuinely uncertain algebraic step". `#print axioms` → `propext` +
  `Quot.sound` + the honest `MachLib.Real` interface ONLY: **NO `sorryAx`, NO
  `zero_count_bound_classical`, NO `analytic_finite_zeros`** — and not even
  `Classical.choice` (the identity is purely algebraic). Verified by `tools/claim_audit`.
- **Why it was blocked, and the actual fix** (`MachLib/IterExpDepthNTopIdentity.lean`):
  the earlier `∀M` attempt diverged; the cause was **not** `whnf` of `prodVarYUpTo M`
  (marking the factor `irreducible` does not help) but `rw`'s `kabstract` re-`whnf`ing
  the *stuck* `leadingCoeffY`/`degreeY` recursors at the **literal symbolic index**
  `⟨M+1, by omega⟩`. Fix: keep the top index an **abstract variable** `i` with
  `hi : i.val = M+1`, confining the one unavoidable literal to three one-equation
  wrapper lemmas. Worst step: divergent → 0.5 s; whole file 0.8 s. Reusable for the
  rest of the tower.
- **The reduce operator, `∀N`** (`MachLib/IterExpDepthNReduce.lean`, also clean —
  `propext`/`Quot.sound`/`MachLib.Real.*` only): `chainNReduce M m p = cTD p − m·p`, with
  `chainNReduce_fst_preserved` (preserves the top y-degree) and `chainNReduce_lcY_top_eval`
  (its top leading coefficient, evaluated, `= eval(cTD(lcY_top p)) + degreeY_top p·eval(Ffac M)·
  eval(lcY_top p) − eval(m)·eval(lcY_top p)`) — the depth-N → depth-(N-1) recursion seam, for any
  top-free multiplier `m`, driven by lemma (1). When `m`'s top term is `degreeY_top p·Ffac M` the
  injection cancels, leaving a depth-(N-1) reduce of `lcY_top p`.
- **The graded-multiplier cancellation, `∀N`** (`MachLib/IterExpDepthNGraded.lean`, clean —
  `sorryAx`-free, no classical-citation axiom): `chainNReduce_graded_cancels` — with the top graded
  term `gradedTop = (degreeY_top p)·Ffac M`, lemma (1)'s injection cancels *exactly* and the reduce's
  top coefficient collapses to `eval(cTD(lcY_top p)) − eval(m_rest)·eval(lcY_top p)` — an honest
  reduce of `lcY_top p` by the remainder `m_rest`, for ANY top-free `m_rest`. This is the depth-`N` →
  depth-`(N-1)` step (the recursion's heart), the generic-`N` analog of chain-2's
  `chain2Reduce_lcY1_eval` and depth-3's `chain3Reduce_lcY2_eval`. The specific nested-degree
  `m_rest` plugs in later without redoing the cancellation.
- **The `dropLastY` bridge, `∀N`** (`MachLib/IterExpDepthNBridge.lean`, clean — `sorryAx`-free, no
  classical-citation axiom): the ∀M analog of `IterExpDepth3Bridge`, so the depth-`(M+2)` reduce's
  dropped top coefficient can be read as a depth-`(M+1)` object and fed to the induction hypothesis.
  `chainValues_restrict_eq` (the `(M+2)`-chain restricted to `M+1` slots IS the `(M+1)`-chain),
  `dropLastY_eval_IterExp` (top-free `q`: `eval q [IExp(M+2)] = eval (dropLastY q) [IExp(M+1)]`),
  `dropLastY_prodVarYUpTo` (the relation polys `y₀·…·y_{k-1}` match under the drop), and
  `dropLastY_cTD_commute` (top-free `q`: `dropLastY (cTD_{M+2} q) = cTD_{M+1} (dropLastY q)`).
- **The recursion closes, `∀N`** (`MachLib/IterExpDepthNRecursion.lean`, clean — `sorryAx`-free, no
  classical-citation axiom): `chainNReduce_dropLastY_recursion` — the depth-`(M+3)` graded reduce's
  dropped top coefficient, evaluated one chain down, **IS a depth-`(M+2)` reduce** of
  `dropLastY (lcY_top p)`, with multiplier just `dropLastY (m_rest)`. So the recursion is carried by
  `dropLastY`; no separate closed-form nested multiplier is needed. Assembled term-mode from bricks
  3+4 + `degreeYtop_cTD_eq'`. The generic-`N` analog of depth-3's `chain3Reduce_dropLastY_lcY2_eval_eq`,
  and the depth-induction's actual step. **Mechanization note**: the top index MUST be an abstract
  variable (`i` with `hi : i.val = M+2`), not the literal `⟨M+2,…⟩` — the literal makes `whnf` diverge
  on the stuck recursors at a symbolic index (rw / conv / term-mode / irreducible all diverge); two
  one-line wrappers confine the literal. This is the lemma-(1) fix, one level deeper.

### Added — depth-3 (triple-exponential) Khovanskii bound, unconditional and dirty-axiom-free (`ab77c5b`)

- **`MachLib.IterExpDepth3Bound.chain3_khovanskii_bound_unconditional`** — the
  finite-zero bound for the **depth-3 triple-exponential** Pfaffian chain
  (`y₀ = eˣ, y₁ = e^{eˣ}, y₂ = e^{e^{eˣ}}`), **proven, not cited**. For a chain-3
  polynomial nonzero at *some* interior point of `(a,b)`, the number of zeros on
  `(a,b)` is finitely bounded — NO `terminal_nonzero` hypothesis. `#print axioms`
  → only the honest `MachLib.Real` interface (`rolle`, `zero_count_bound_by_deriv`,
  the ring/order/field axioms, `natCast`) plus Lean's `propext`/`Classical.choice`/
  `Quot.sound`: **NO `sorryAx`, NO `zero_count_bound_classical`, NO
  `analytic_finite_zeros`**. Verified by `tools/claim_audit`.
- **How the climb works** (the `IterExpDepth3*` files): `WellFounded.induction` on
  an augmented measure `chain3Order5` (`(chain3MeasureCanon, degreeY₁ q)`), four
  arms — base (`degreeY₂ = 0` → the depth-2 bound above) / `degreeY₂`-trim /
  inner-trim (drop the phantom leading `y₁`-term of `lcY₂ p`; the crux — its own
  `reconstructY`/`leadingCoeffY` toolkit) / reduce (graded multiplier, then the
  integrating-factor vehicle for `reduct ≡ 0` or Rolle `+1`). The depth-2/single-exp
  frameworks are untouched.
- **Meaning + honest scope.** Frontier 1 (the depth-N iterated-exponential tower) is
  closed at **depth 3** — the depth-2 closure provably extends one level up by depth
  induction, entirely from honest Rolle. This does **not** discharge the
  arbitrary-depth axiom: `PfaffianFunction.zero_bound` still cites
  `zero_count_bound_classical` for general depth; only depths 1–3 are counted, not
  quoted.

### Added — depth-2 Khovanskii bound, unconditional and dirty-axiom-free (`dda2a58`)

- **`MachLib.ChainExp2NoZeros.chain2_khovanskii_bound_unconditional`** — the
  finite-zero bound for the **depth-2 double-exponential** Pfaffian chain
  (`x, eˣ, e^{eˣ}`), **proven, not cited**. For a chain-2 polynomial nonzero at
  *some* interior point of `(a,b)`, the number of zeros on `(a,b)` is finitely
  bounded. `#print axioms` → `propext, Classical.choice, Quot.sound`, the `Real`
  base, and the honest Rolle corollary `zero_count_bound_by_deriv`; **no
  `zero_count_bound_classical`, no `sorryAx`**. This is the first depth beyond the
  single-exponential case where the reducibility witness is *constructed* rather than
  supplied/assumed.
- **How the witness is built** (the `ChainExp2*` files): a *chain-aware nested
  descent measure* (`chain2MeasureCanon`, canonical y₀-degree so the reduce cannot
  inflate it), a *polynomial-multiplier Rolle transfer*
  (`zero_count_polyMultReduce_transfer`, the reduce `P' − ((degreeY₁ P)·y₀ + c)·P`),
  and — for the terminal `reduct ≡ 0` case that pure exponentials hit — an
  *integrating-factor vehicle argument*: `V = f·exp(−(d·eˣ+c·x))` has `V' = E·(reduct)`,
  so `reduct ≡ 0 ⇒ V` constant (MVT) ⇒ `f` nonzero everywhere once nonzero at one point.
  The single-exponential framework (`SingleExpKhovanskii`, `KhovanskiiReduction`) is
  untouched.
- **Honest scope.** This does **not** discharge the arbitrary-depth axiom. The legacy
  `zero_count_bound_classical` (Khovanskii 1991) still stands for the general
  `PfaffianFunction` bound; depth-3+ would mirror the depth-2 arc with a deeper nested
  measure. Tier summary now reads: *single-exp proven, depth-2 proven, arbitrary-depth
  cited.* See [`what_is_proven.md` §7](foundations/docs/what_is_proven.md).

## [Unreleased] — 2026-06-26

### Added — `MachLib.FPModel`: verified f64 forward-error (cross-target equivalence, leg 2)

- **`MachLib.FPModel`** — the first proof (not regression test) relating a
  kernel's IEEE-754 `f64` evaluation to its exact `Real` semantics. Adopts the
  standard model of FP arithmetic (Higham §2.2) as three Mathlib-free axioms
  (`u`, `0 ≤ u`, `u ≤ 1`; `u = 2⁻⁵³` for binary64). `length_sq2_fwd_error` and
  `length_sq3_fwd_error` (the `vec3_length_sq` kernel) prove the `f64` result is
  within the tight relative bound `(1+u)ⁿ − 1 ≈ n·u` of the exact value, for
  *every* rounding. `#print axioms` → only `propext` + the `Real` base + the 3
  `u` axioms; no `sorryAx`. EML's straight-line scalar restriction is what makes
  this a closed-form bound rather than a CompCert-scale semantics theorem.
  Full write-up: [`docs/cross_target_equivalence_2026_06_26.md`](foundations/docs/cross_target_equivalence_2026_06_26.md).
- **Conditioned bounds + precision-generic model** (same module): `RoundsW w`
  parameterizes the standard model over the precision's unit roundoff (f64 2⁻⁵³,
  f32 2⁻²⁴, bf16 2⁻⁸) — one theorem, every target, and *no* `u` axiom (rests
  only on `propext` + the `Real` base). `dot2_fwd_error` handles the mixed-sign /
  cancellation-prone case `length_sq` avoids: `|fl(a·b+c·d) − exact| ≤
  ((1+w)²−1)·(|a·b|+|c·d|)` — absolute error against the conditioning quantity,
  the honest statement when the result can cancel to ≈0. Helpers `roundsW_abs`,
  `abs_le_one_add`, `mul_one_add_sub`.

## [Unreleased] — 2026-06-25

### Added — ring-v3, the decompose-first toolkit, and a close-rate harness

- **`MachLib.MPolyRing` (ring-v3)** + the `mach_mpoly` tactic: a nested multivariate
  polynomial normal form. Reify once, normalise once, compare once — polynomial in
  the monomial count, not exponential in the variable count. Closes identities the
  recursive multivariate tactic could not: the 8-variable Euler four-square
  (quaternion-norm) identity goes from *not finishing in 50 minutes* to *seconds*,
  `sorryAx`-free.
- **`MachLib.Decompose`** — four reusable "decompose before nlinarith" lemmas
  (`abs_le_sqrt`, `mul_mem_symm_band`, `lerp_le_of_le`, `quad_denom_pos`) + the
  `mach_decompose` tactic, safe-by-construction (apply/exact + assumption; fails
  cleanly, never silent-`sorry`).
- **`foundations/scripts/closerate.sh`** — a reproducible close-rate harness for the
  Forge `@verify(lean)` corpus. Compiles each emitted obligation independently
  (recursively over all sub-corpora) and counts which `mach_positivity | rfl | sorry`
  cascades genuinely close vs fall through. Current figure: **387 / 581 = 66.6%**
  auto-close, 251 files, 0 build errors (up from 364 / 582 = 62.5%: a 2026-06-26
  refresh brought 16 Discovered obligations up to current `eml-compile`
  emission — the committed copies were stale bare-`sorry` output predating the
  `first | mach_positivity | rfl | sorry` cascade; +23 close, −1 theorem from a
  shadow_pcf re-emit). (The textual `sorry` fallback is in every
  emitted proof, so file-grep is NOT the close-rate — only compilation is.)

Full write-up: [`docs/verification_automation_2026_06_25.md`](docs/verification_automation_2026_06_25.md).

## [Unreleased] — 2026-06-14

### Calibration note — interim audit figures over-counted

In-flight prose around the Khovanskii closure on 2026-06-14 quoted an
audit summary of "210 Forge `@verify` obligations proven-in-place,
80%/19% gap-vs-discharged" and a related sorry count of "269 discovered
sorries (up from 222)". Both figures came from a local working tree
that contained, alongside the publicly-tracked files, ~62 ungated
Discovered/ stubs auto-emitted by the local `auto_prove.py` workflow
(blanket-ignored under `foundations/MachLib/Discovered/.gitignore`),
plus 32 duplicate `.eml` files in a forge `build/` artifact directory.
Neither was visible to a fresh public clone.

The CI-emitted `status.json` (`.github/workflows/status.yml`, lands on
the `status-data` branch on every master push) reports the
public-verifiable figures: 1088 `@verify` obligations total, 36
proven-in-place, 225 placeholder, 823 open, gap_pct 96.3%,
discharged_pct 3.7%, 198 discovered sorries. Those are the numbers a
stranger running `lake build` at the recorded SHA can reproduce.

The 4 strengthened Forge contracts shipped this cycle (Butler-Volmer,
plasma concentration, defibrillator discharge, critically-damped spring)
are publicly tracked and verified, and counted in both the local and
public audits. The over-count was concentrated in `proven_in_place`
(stubs the Forge backend auto-emitted with concrete-enough bodies that
the audit's heuristic classifier didn't flag them).

Follow-up: `forge_verify_audit.py` now defaults to `git ls-files`-aware
file enumeration so a local audit gives the same number as CI. The
`--include-untracked` flag preserves the full local view for callers
who want it. Until the 62 ungated stubs are reviewed and pushed, the
CI figure is the right one to quote.

### Added

- `MachLib.Applications.PlasmaConcentrationNonneg` — pharma kernel
  proof. Bi-exponential IV-bolus central-compartment concentration is
  non-negative under the Forge kernel preconditions. Domain: TCI
  anaesthesia pumps, ICU monitors. Safety class: IEC 62304 Class C, FDA
  510(k). Also closed the `sorry` for `plasma_concentration_nonneg`
  inline in `MachLib/Discovered/pk_two_compartment.lean`.
- `MachLib.Applications.DischargeVoltageSafety` — defibrillator kernel
  proof. Strengthens the Forge `True := by trivial` placeholder for
  `discharge_voltage_decays_exponentially` to sign preservation under
  non-negative initial voltage (no polarity inversion mid-phase). IEC
  62304 Class C. Pointer comment added to the Discovered stub.
- `MachLib.Applications.SpringCriticallyDamped` — game-animation kernel
  proof. Khovanskii-localised positivity of the critically-damped
  harmonic spring `A · (1 + ω·t) · exp(-ω·t)`. ExpPoly length 1, total
  degree 2; the lone zero at `t = -1/ω` is excluded by the animation
  window `t ≥ 0`. Sign-preserving + strictly-positive variants ship;
  the underdamped (cos-bearing) branch remains open pending
  trig-Khovanskii. From `eml-stdlib/gaming/animation/spring.eml`'s
  `spring_critical_signed` obligation.
- `MachLib.SingleExpKhovanskii` — constructive Khovanskii zero bound for
  polynomial-in-(x, eˣ), three resolution paths:
  - `expPoly_khovanskii_bound` (parametric capstone; user supplies an
    `IsKhovanskiiReducibleExp` witness).
  - `expPoly_auto_bound_with_propagation_aux` (strong-induction auto-bound
    over `length + Σ degreeUpper(polySimplify coeffs)`, parametric in a
    propagation hypothesis).
  - `expPoly_ode_no_zeros` (MVT-based ODE corner case: when
    `f' - c·f ≡ 0` on `(a, b)`, `f` is zero-free).
- `MachLib.KhovanskiiReduction` — `khovanskii_bound_full` for general
  triangular Pfaffian chains, parametric in a reduction witness
  (`IsKhovanskiiReducible` with `reduce` + `drop` constructors).
- `MachLib.MultiPolyToPoly` — `MultiPoly 0 → Poly` conversion + the
  chainLength-0 base-case zero bound.
- `MachLib.Applications.ButlerVolmerKhovanskii` — Forge kernel proof for
  the Butler-Volmer electrode-kinetics safety contract: current = 0 iff
  overpotential = 0. Strengthens the `True := by trivial` placeholder
  in `MachLib/Discovered/butler_volmer.lean` (pointer comment added).
  Domain: BMS, fuel cell controllers, corrosion engineering.
- `foundations/AxiomAudit.lean` — reproducible `#print axioms` over the
  headline theorems, run via `lake env lean AxiomAudit.lean`.
- `foundations/KhovanskiiExamples.lean` — three worked applications.

### Foundations note

Results are proven **modulo MachLib's axiomatized analytic base**: a Rolle
zero-counting corollary (`zero_count_bound_by_deriv`), the `HasDerivAt`
rules + `HasDerivAt_unique`, `exp_pos` / `exp_zero`, and `MachLib.Real`
arithmetic / order. In mathlib every one of these is a theorem, not an
axiom — grounding the base in mathlib is open work, not done here.

`zero_count_bound_by_deriv` does the core analytic work; the Khovanskii
layer added in this release is the reduction and the explicit-bound
bookkeeping on top of it. The audit (`AxiomAudit.lean`) makes the
dependency set fully visible.

The release added no assumptions beyond that documented base.

### Notes

- The textbook Khovanskii operator `f' - c·y_n'·f` does not drop degree
  in single-exp chains. The operator that works is `scaledReduction c f :=
  f' - c·f` (see the git history around the `4fe434a` commit for the
  discovery).
- `expPoly_ode_no_zeros` does not invoke `Classical.choice` in its Lean
  dependency closure. This is **not** a constructive-analysis claim — the
  MVT it rests on is classical in spirit and only escapes the dependency
  list because the MVT itself is axiomatized in MachLib.
- 3 `sorry`-warnings exist in 2 non-headline modules (`MachLib.ForgeTest`
  and `MachLib.HighDimensional`, work-in-progress queues unrelated to this
  release). Transitive-import closure of the headline theorems and the
  audit (25 modules) confirms neither is in the dependency chain.

### Verification

- `lake build` of the foundations target is green.
- Headline files have zero `sorry`.
- `lake env lean foundations/AxiomAudit.lean` reproduces the per-theorem
  axiom listing.

### Attribution

Formalization developed by an AI agent (Claude Code) driving MachLib
commits. Coordination on behalf of the Monogate research team.
