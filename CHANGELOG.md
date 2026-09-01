# Changelog

All notable changes to MachLib are recorded here. Format roughly follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/). Versions are
release-snapshot identifiers; see the release manifests for the authoritative
per-release status.

## [Unreleased] — 2026-08-28 (en)

### The query germ's ZERO branch, closed — and it costs one analytic axiom less

`ratGerm_eventual_sign` splits a rational germ three ways and
`oneQueryDichotomy_of_uniformBoundsFrom` needs a uniform bound on each. `(ej)` did the **positive**
branch; `MachLib/EMLQueryGermZeroBranch.lean` (new) does the **zero** branch. Two of three.

**Totalisation does the work.** Where `u x = 0`, `Fbasis (u x) = exp 0 + log₀ 0 = 1` — the totalised
`log` annihilates itself at the boundary — so on that ray

```
bipev N x (Fbasis (u x))  =  bipev N x 1  =  pev (sumCoeffs N) x
```

an ordinary univariate polynomial, its coefficients the **row-wise sum** of `N`, because Horner at
`y = 1` just adds them. **No transcendental survives, so none of the Khovanskii machinery is
needed**: `poly_root_count_bound` applies directly and its bound is `degreeUpper`, which mentions no
interval — exactly the `UniformZeroBoundFrom` shape.

**And the footprint is strictly lighter than the positive branch's.** Both carry `rolle_ct`; the zero
branch does **not** carry `analytic_finite_zeros_compact`, which the Khovanskii descent needs and
polynomial root-counting does not. One fewer analytic axiom on this branch, which is the kind of
difference worth measuring rather than assuming — I expected "much lighter" and the honest answer is
"one axiom lighter", since Rolle underlies both.

`¬ EvZeroF` is what makes the polynomial non-trivial: without it the germ could be identically zero
and no bound would exist — the same conditioning `EMLZeroBoundRay` explains at length for the general
antecedent, appearing again in the smallest case.

**What is left is one branch**: `u < 0` eventually, where totalisation gives `Fbasis u = exp u` and
the germ is a polynomial in `x` and `exp (P/Q)` — no log level, so no `FTree` route, and
`ExpRationalKhovanskii` is the relevant track.

Gotcha paid again, and it is in `CLAUDE.md` already: `obtain` on the `EvZeroF` existential yields an
**unreduced** `(fun x => …) x`, so `rw` cannot match the beta-reduced goal. Bind it through a typed
`have`. Third time this pattern has cost a build in this arc.

## [Unreleased] — 2026-08-28 (eo)

### The negative branch — and a correction: only ONE of the three branches is a `UniformZeroBoundFrom` producer

`MachLib/EMLQueryGermNegBranch.lean` closes the last of `ratGerm_eventual_sign`'s three cases, and
writing it surfaced an over-claim in `(ej)` that needs stating first.

#### The correction

I described the **positive** branch as closed. It is proved, but it is **interval-local**:
`queryTerm_zero_bound` takes a nonzero witness *inside* `(a,b)` as a hypothesis, because
`encBound_bounds` needs one there. `¬ EvZeroF` does **not** supply it — that gives non-vanishing
arbitrarily far out, not inside a nominated bounded interval.

So the honest count is:

| branch | reaches `UniformZeroBoundFrom`? |
|---|---|
| `u` eventually zero | **yes** — `poly_root_count_bound` needs a witness only *somewhere*, then bounds every interval |
| `u > 0` eventually | no — interval-local |
| `u < 0` eventually | no — interval-local |

**One of three, not two.** What the other two await is a single shared lemma: the germ is non-vanishing
*somewhere in every subinterval beyond the ray*, which follows from analyticity plus `¬ EvZeroF` by an
identity-theorem argument and is not proved. Writing the third branch is what made the gap visible —
the second instance of a pattern where building the "harder" case exposes that the "easy" one was
weaker than recorded.

#### The negative branch, and why it needed no declamping

Where `u < 0`, totalisation gives `Fbasis u = exp u + log₀ u = exp u`, so the germ is a polynomial in
`x` and `exp (P/Q)` — **no logarithm anywhere.**

The obvious route was `EMLDeclampEncoder`: the `Fbasis`-built tree fails `LogArgPosOn` at its
`logTree` node, and `declamp` rewrites exactly such nodes. **That route is a trap worth recording.**
Its natural uniformity fix — bound every `declampVariant` — is *provably impossible*:
`variantBounds_hypothesis_unsatisfiable` exhibits a variant that is identically zero while the node it
came from never vanishes. The reachable form avoids it, but `declamp_logArgPos` gives positivity only
on the `(a,b)` declamped for, which is not the shape the reachable form then asks for.

**None of it was needed.** Once totalisation has removed the log, `exp (u x)` is directly an EML node
(`expOf t = eml t (const 1)`, log argument the constant `1`). Assembling the germ from `expOf` and the
`Gen` combinators makes the `LogArgPosOn` obligation **unconditional except for `pev Q x ≠ 0`**:

| piece | cost |
|---|---|
| `polyE L = toEML (pevTerm L)` | nothing — no `F`, no `div` |
| `addGen`, `mulGen` | nothing — they shift through `domTree` |
| `divGen a b` | `b.eval x ≠ 0` |
| `expOf t` | nothing |

**So the branch that looked hardest needs the fewest hypotheses**, because the failing positivity was
an artefact of routing through `Fbasis`. Same lesson this arc keeps paying for: the difficulty was in
the representation, not the object.

Seventh duplication caught: `Fbasis_of_nonpos` already exists in `EMLQueryComplexity`. Third one
caught **because the obvious name was chosen** — a creative name would have shipped the twin.

## [Unreleased] — 2026-08-28 (ep)

### The shared gap closed: vanishing on one subinterval of a ray forces `EvZeroF`

`(eo)` recorded that two of the query germ's three branches are **interval-local** — `encBound_bounds`
wants a nonzero witness *inside* `(a,b)` and `¬ EvZeroF` gives non-vanishing only eventually — and
that both await one shared lemma. `MachLib/EMLRayIdentity.lean` (new) supplies it.

`evZeroF_of_vanishes_on_subinterval`: if an EML tree with log-positivity on a ray vanishes identically
on **some** subinterval of it, it is `EvZeroF`. Contrapositive
(`exists_nonzero_in_subinterval`): a tree that is *not* eventually zero has a nonzero point in
**every** subinterval of the ray — precisely the per-interval witness both branches were assuming.

The argument: vanishing on `(p,q)`, take the interval `(p, x+2)` for any `x ≥ q`; log-positivity holds
there, so the tree is analytic on `Icc m (x+1)` for `m` strictly inside; the identity theorem then
propagates the vanishing across `Ioo m (x+1)`, which contains `x`. The `+2`/`+1` are not slack —
`eml_tree_analytic_on_interval` is stated *strictly inside* its interval, because analyticity at a
point needs a neighbourhood while `LogArgPos` controls only the open interval.

#### The axiom cost, measured after I claimed it wrongly

`analytic_zero_on_subinterval_imp_zero` is a **theorem** (from `analytic_finite_zeros_compact`), not a
new assumption — so I wrote that the lemma "consumes no axiom the branches don't already stand on".
**Then I measured:**

```
exists_nonzero_in_subinterval   analytic_finite_zeros_compact, eml_tree_analytic_on_interval
queryTerm_zero_bound            analytic_finite_zeros_compact, analytic_ne_zero_nbhd, rolle_ct
```

`eml_tree_analytic_on_interval` is **not** in the positive branch's footprint. It is a pinned corpus
axiom used elsewhere in this lane, so **the total does not move — 243 unchanged** — but composing
this lemma with either branch makes *that branch* strictly more trusting, and the branch footprint is
what a reader of those theorems actually cares about.

This is the arc's recurring error in its smallest form: an optimistic guess about cost, one
`#print axioms` away from settled. The disclosure is in the module docstring, not just here.

#### A small standing annoyance, recorded

`a < a + 1` is defined **privately** in `EMLZeroBoundRay`, `EMLAnalyticDischarge`, `EMLDepthTameness`
(as `lt_succ_self`) and `EMLZeroBoundAssembly`. This module needed a fifth copy, because `private`
guarantees the next module writes it again. Not worth a refactor; worth a line, since the pattern will
keep recurring until one of them is made public.

## [Unreleased] — 2026-08-28 (eq)

### Both interval-local branches upgraded to `UniformZeroBoundFrom` producers

`(ep)` supplied the missing per-interval witness; this joins it to the two branches that needed it.
`MachLib/EMLQueryGermUniform.lean` (new) does the upgrade **once**, as a lemma about EML trees rather
than twice about germs — the branches differ only in which tree they hand over.

```lean
uniformZeroBoundFrom_of_rayTree (t) (f) (X) (hX1)
  (hagree : ∀ x ≥ X, t.eval x = f x)
  (hlog   : ∀ a b, X ≤ a → a < b → LogArgPosOn t (Icc a b))
  (hne    : ¬ EvZeroF f) :
    UniformZeroBoundFrom f X (encBound t)
```

`hlog` is used twice and both uses are needed: on `Icc` it feeds `encBound_bounds`; narrowed to the
open interval it feeds `exists_nonzero_in_subinterval`, which supplies the witness `¬ EvZeroF` does
not give.

So all three branches now produce `UniformZeroBoundFrom`:

| branch | producer | constant |
|---|---|---|
| `u` eventually zero | `queryGerm_zero_branch_bound` | `degreeUpper (pevPoly (sumCoeffs N))` |
| `u > 0` eventually | `queryGerm_pos_branch_uniform` | `encBound (toEML (queryTerm N P Q))` |
| `u < 0` eventually | `queryGerm_neg_branch_uniform` | `encBound (negGermTree N P Q)` |

The negative branch's hypothesis list is **shorter** than the positive branch's — no positivity —
which is the asymmetry `(eo)` recorded, now visible in the two statements side by side.

#### What this does NOT do, said before anyone reads the table above and concludes otherwise

**It discharges nothing.** Composing the three into
`oneQueryDichotomy_of_uniformBoundsFrom`'s antecedent still needs the case split on
`ratGerm_eventual_sign`, and that antecedent is universally quantified over `N`, `P`, `Q`. The ledger
row stays open, the obligations gate says so, and **5 distinct open obligations is unchanged.** The
module docstring leads with this for the same reason.

#### `private` bit me with my own helper

`EMLQueryGermUniform` wanted `le_addr`/`le_addl` — which I had written `private` in
`EMLNegTranslation` earlier the same session, one file after complaining that `a < a + 1` exists as
four private copies. No import path reached them anyway, so the two lines are inlined.

They are now public regardless, with the docstring saying plainly that **the immediate cause
evaporated** and the change is a unilateral improvement rather than a response to a live need — a
justification that quietly outlives its reason is the kind of prose this session has spent all day
correcting.

## [Unreleased] — 2026-08-28 (er)

### `BipolyNoOscillation` is a theorem — and a second over-quantification, in this morning's own fix

`MachLib/EMLQueryGermAntecedent.lean` (new) joins the three branches through
`ratGerm_eventual_sign`, proving the antecedent and hence `BipolyNoOscillation` outright. No
`sorryAx`, no `zero_count_bound_classical`; the footprint is the lane's accepted analytic base
(`rolle_ct`, `analytic_finite_zeros_compact`, `analytic_ne_zero_nbhd`,
`eml_tree_analytic_on_interval`).

#### It does NOT discharge the obligation, and the gate says so

```
OneQueryDichotomy    ∀ C P Q X, 1 ≤ X → (∀x≥X, pev Q x ≠ 0) → …
proved here          ∀ C P Q X, 1 ≤ X → (∀x≥X, pev Q x ≠ 0) →
                       (∀x≥X, DivDenomsOK C x …) →
                       (∀x≥X, bipev (ctxFrac C).2 x … ≠ 0) → …
```

**Two extra hypotheses** — the div side conditions along the curve, unaddressed. `check_obligations`
independently confirms it: *"OneQueryDichotomy: open, no theorem concludes it"*, and the count stays
at **5 distinct open obligations**. The warning is at the *top* of the module docstring, because
"the antecedent is proved" is one short step from "the obligation is discharged" and here they are
separated by exactly two hypotheses.

#### The over-quantification, found in `(eh)`'s own theorem

`bipolyNoOscillation_of_uniformBoundsFrom` — written this morning — demanded a bound for **every**
`Q`, including one vanishing identically. There `pev P x / pev Q x` is `divR _ 0`, and **`divR` is an
opaque axiom whose `div_def` is stated only for a non-zero denominator**. So the antecedent asked for
a zero bound on a function nothing in the corpus constrains: **no producer could ever have supplied
it.**

`BipolyNoOscillation` hands over `X`, `1 ≤ X` and `∀ x ≥ X, pev Q x ≠ 0`. The proof discarded all
three as `_`.

That is the *same* defect `(eh)` was written to fix — *"a hypothesis quantified far past its use makes
the remaining work look larger than it is"* — and I committed it in the same edit, narrowing the
**interval** quantifier while leaving the **`Q`** quantifier wide. One over-quantification fixed, one
introduced, in one theorem.

`bipolyNoOscillation_of_ratUniformBounds` passes them through. Strictly weaker as a hypothesis,
strictly easier to supply, and it is what `RatGerm` — *defined* by exactly this non-vanishing —
naturally produces.

#### The assembly

Three cases, each already a theorem: `u` eventually zero collapses the germ to a polynomial; `u > 0`
takes the `Fbasis` route through `toEML`; `u < 0` lets totalisation kill the log and uses the log-free
tree. Rays are combined as `X + X'` rather than a maximum — both are `≥ 1`, so the sum dominates each,
and the corpus has no `Real.max` lemmas to hand.

## [Unreleased] — 2026-08-29 (eu)

### `divClamp`, and its value-preservation half

`MachLib/EMLCtxDivClamp.lean` (new) defines the clamp `(et)` specified and proves the half that makes
it sound: **`divClamp_eval` — on a ray, the clamped context evaluates exactly as the original.**

`divClamp` replaces every `div` node whose **divisor is eventually zero** by `const 0`. `a / 0 = 0`
is what makes that an equality rather than an approximation, and it is the third distinct use of
totalisation in this vein — after `Fbasis 0 = 1` (zero branch) and `Fbasis u = exp u` (negative
branch).

#### Why `declamp`'s uniformity problem does not recur

`declamp t a b` is a **different tree per interval**, because a log argument's sign can differ from
interval to interval — hence `declampVariants`, and hence
`variantBounds_hypothesis_unsatisfiable`. Here the trigger is `EvZeroF`, a **ray property**: once the
ray is far enough out the clamped context is *fixed*. No variant list, no reachability subtlety, no
unsatisfiable-hypothesis trap. That is a real structural difference, not a lucky one.

#### What is left

The denominator half: that the clamped context's `bipev (ctxFrac ·).2` is eventually non-zero. The
argument is known — clamping swaps the divisor's *numerator* (zero) for `const 0`'s *denominator*
`[[1]]`, and the surviving factors compose via `bipolyNoOscillation_holds`, since a bipev germ that is
not eventually zero is eventually non-zero and a finite product of such is non-vanishing.

#### Three small things the proof cost, all worth a line

* **`qGerm` as an `abbrev` broke `rw`.** The goal displays unfolded, so `rw` could not match the
  folded form. It survives only as the clamp's *condition*, where nothing rewrites through it; the
  theorem statement writes `FCtx.eval` out.
* **`obtain ⟨…⟩ := hz` consumes `hz`**, which `if_pos hz` still needed one line later. `id hz` fixes
  it. Obvious in retrospect and invisible in the error, which reported `hz` as an unknown identifier
  rather than as consumed.
* **`le_addr`/`le_addl` restated a sixth and seventh time**, no import path reaching
  `EMLNegTranslation` where they were made public. The complaint in `EMLRayIdentity` about `a < a + 1`
  now applies to three separate helpers.

## [Unreleased] — 2026-09-01 (gf)

### Applicability, and the rule that was still an argument

Two structural fixes from review, plus a live defect in `(ge)`'s own replacement claim.

#### `WITNESS-AUDIT OK` now states what it cannot examine

`witness_audit.py` excludes theorems concluding `False` **by design** — an unsatisfiable hypothesis
set is their content. Correct, and invisible: the line `OK — 35 uninstantiated capstones, exactly
the pinned set` printed beside the whole log-junction arc for a day while structurally unable to
comment on it.

It now reports the exclusion, ported from Forge's obligation axis, which reports
`preserved / not-applicable / unknown` with a reason on every not-applicable row rather than folding
them into the pass count:

> `WITNESS-AUDIT OK — 35 uninstantiated capstones, exactly the pinned set; 60 refutation theorem(s)
> NOT APPLICABLE.`

**Sixty**, each named with its reason. A gate reporting `PASS` where the honest value is
`NOT_APPLICABLE` had no way to say so; now it does, and the blind spot is a row you read rather than
a discovery made by mis-stating a vacuity test first.

#### Five failures were one rule, stated as two

`(fy)`'s gotcha split the session's failures into *non-execution* and *instrument-measured-itself*,
and claimed only the first was mechanically fixable. That split is wrong at the level that matters.
Both halves are the same requirement:

> **Every instrument must be shown capable of both verdicts before either verdict is read.**
> *Positive control:* run the pattern against a line you know matches, before believing zero matches.
> *Negative control:* feed the checker known-bad input; if it passes, the run is worthless.

An errored grep, a `lake build` over a gutted docstring, a launcher exiting `0` while
`GATE_RC=127`, a seed grid reported as a census, a cut-off reported as a property of the object —
five costumes, one defect: **an instrument that could only return one value.**

#### `(ge)`'s replacement claim had the same defect on the other axis

Recorded in the research repo as Finding 9b, and repeated here because the pattern is the point.
*"Every located zero of every rung has `|z| ≤ 2.71828`"* — `located` is the **search's** property. The
inner cutoff was named and audited twice; the outer one was never stated, and the boundedness claim
rested on it. The outer *filter* read `|z| < 22`, but the **seeds** reach only `|z| ≈ 9.2`, so the
effective bound was the seeds, not the filter.

The claim survives by a different instrument, with the bound in the sentence: converged windings give
`N(R) = 3` at `R = 9.4, 15.7, 22.0, 34.6` on both rungs, and three zeros are located in each — so
**no zeros with `2.72 < |z| < 34.6`**, beyond which: unknown. `instrument.py` now refuses to emit a
count without **both** bounds, and refuses a *search* without its seed reach.

#### The rule, installed as a field on both sides

Stating it in a gotcha is what `(fy)` did, and `(ge)` violated it hours later. So it is now a
**required field** in two places:

* `instrument.py` (research repo) refuses a count without **both** region bounds, and refuses a
  *search* without its **seed reach** — the outer filter is not the outer bound.
* `tools/absence_claims.json` now carries a **`positive_control`** on every search claim: a line the
  pattern must match. `absence_audit.py` refuses the claim otherwise.

The second closes a real asymmetry rather than adding ceremony. The **probe** branch has always
demanded a probe fail for the *right reason* — *"a broken probe is not evidence of absence"* — while
searches had no equivalent, and a pattern that cannot match returns exactly what a true absence
returns. The registry already encoded half the rule; the missing half is the half that failed.

Convict-tested, both polarities, and reported as `UNAVAILABLE` rather than `FAIL` because "could not
be checked" is not "checked and passed":

```
UNAVAILABLE  no-complex-in-machlib: search has no positive_control — an instrument that has
             not been shown capable of a hit cannot evidence a miss
UNAVAILABLE  no-measure-theory: pattern does not match its own positive control
             'axiom Measurr : Type' — a broken search is not evidence of absence
```

Ledger unmoved: 22 rows, 4 distinct open obligations, 243 axioms.

## [Unreleased] — 2026-08-31 (ge)

### A specimen for the interval theorem — and a FALSE ABSENCE, caught by the build

New module `MachLib/LogNotRationalSpecimen.lean`. `log_recip_not_rational_on_unit_interval`
(**48 axioms**, `sorryAx`-free).

### The retraction first

The first draft of this entry claimed **"`PIrred` appears at 55 sites, 40 of them as a hypothesis,
and nothing had ever been shown to satisfy it"** and presented a `pIrred_X` as the corpus's first
witness.

**That was false.** `MachLib/GermClearedSpecimen.lean` has proved `pIrred_X` since the
cleared-relation arc, uses it at six sites, and its header states the identical discipline in nearly
the same words — *"conditional on a pole hypothesis set that, until now, nobody had ever
instantiated"* — having found **two hypotheses there that were genuinely unsatisfiable** and fixed
them. That module is a better instance of the practice than the one I was proposing to introduce.

**`lake build` caught it, not me**, via a name collision:
`environment already contains 'MachLib.pIrred_X._proof_1_1' from MachLib.LogNotRationalSpecimen`.

The search behind the false claim was broken **twice over**, and both failures are already in this
repo's gotchas:

* the pattern `PIrred \[` cannot match the actual text `PIrred ([0, 1] : List Real)` — a bracket
  where the source has a paren;
* the exit code was read off `head` through a pipe, so a grep that matched nothing reported `rc=0`.
  `CLAUDE.md` gained a gotcha about exactly this **earlier the same day**, after the same defect.

Duplicate deleted; the module now imports the existing witness.

### What is genuinely new, and it is narrow

A specimen for the **interval** theorem, which did not exist before `(gd)`. `GermClearedSpecimen`
instantiates the germ/cleared-relation arc; nothing instantiated `log_not_rational_on_interval`. With
`P = 1`, `Q = q = x`, `r = 0`, `Qt = 1` on `(1,2)`:

> **`log (1/x)` is not a rational function on `(1,2)`.**

So `(gd)` has content rather than quantifying over an empty configuration space — the check no gate
here can perform, for a theorem class the vacuity gate excludes by design.

Ledger unmoved: 22 rows, 4 distinct open obligations, 243 axioms.

## [Unreleased] — 2026-08-31 (gd)

### `log` of a rational function is not rational on any interval — and the corollary is consumed

`log_not_rational_on_interval` (**48 axioms**, `sorryAx`-free), new module
`MachLib/LogNotRationalInterval.lean`.

`(gc)` named a specific risk: the `k = 1` corollary `no_rational_logarithm` was quoted by docstrings
and **applied by nothing**, while the witness audit that exists to catch exactly that cannot see it,
because theorems concluding `False` are excluded from that audit **by design**. This discharges the
risk by construction rather than by argument — the corollary now has a caller.

`hchar` is not a hypothesis of the consumer: `derivCoprime_of_irred` `(fy)` supplies it inline from
`PIrred q`. What a caller provides is structural — `q` irreducible, numerator coprime to it, the
denominator's exact multiplicity `ppow q (r+1)` with `¬ Pdvd q Qt` — or non-vanishing on the
interval. **No tail. No growth premise. Nothing eventual.**

### The arc, from `(fy)` to here

| step | supplied by |
|---|---|
| nine structural hypotheses | `lowest_terms_with_ord`, `derivCoprime_of_irred`, `exists_coprime_representative` + transports `(fy)` |
| the tenth, `hident`, from an interval | `hident_of_log_rational_on_interval` `(gc)` |
| the lift that made any of it local | `peq_of_eq_on_interval` `(ga)` |
| the differentiation step, on an interval | `logRat_deriv_eq_on_interval` `(gb)` |
| **the application** | **`log_not_rational_on_interval` — here** |

### Still not claimed

This says nothing about `BoundedGermTranscendence`, and it is not the general instrument `(fz)`
called for: that allows arbitrary degree in `F(S x)` and **algebraic-function** coefficients, where
this is `k = 1` with polynomial coefficients. The residue of `OneQueryLevelSet` is untouched.

Ledger unmoved: 22 rows, 4 distinct open obligations, 243 axioms.

## [Unreleased] — 2026-08-31 (gc)

### `hident` from an interval — the composition, written rather than described

`hident_of_log_rational_on_interval` (**45 axioms**, `sorryAx`-free), appended to
`MachLib/LogRatDerivInterval.lean`.

`(gb)` said the four pieces "line up by shape" and stopped, on the grounds that a chain which
typechecks in prose is not a theorem. Written out it is three lines — differentiate on the interval,
clear denominators pointwise, lift — and it compiled on the first attempt, which is the expected
outcome when every ingredient has already been measured and the only question was orientation.

It produces `no_rational_logarithm`'s tenth hypothesis from

> `log (P/Q)` agrees with `N/D` on an open interval

with **no tail, no growth premise, and nothing eventual anywhere in the statement**.

### The k = 1 instrument, honestly scoped

| hypothesis | source |
|---|---|
| `hident` | **`hident_of_log_rational_on_interval` — new, interval-local** |
| `hq`, `hPd`, `hQ`, `hQtd` | `lowest_terms_with_ord` `(fy)` |
| `hchar` | `derivCoprime_of_irred` `(fy)` |
| `hlow` | `exists_coprime_representative` + the two transports `(fy)` |
| `hPn`, `hNn`, `hDne` | the germ's own data |

So the `k = 1` case is now instantiation, not construction.

### What is NOT shown — stated correctly on the second attempt

The first draft of this section said *"nothing here demonstrates the ten hypotheses are jointly
satisfiable."* **That is the wrong test for this theorem.** `no_rational_logarithm` concludes
`False`, so joint satisfiability is exactly what it denies; `witness_audit.py` says so in its own
header — *"a theorem concluding `False` is MEANT to have an unsatisfiable hypothesis set, that is
what it proves"* — and therefore **excludes this whole class from vacuity checking by design.**

The correct test for a refutation theorem is that its **structural** hypotheses, minus the one being
refuted, are satisfiable — otherwise it refutes nothing. On that test:

* `no_rational_logarithm_scaled`, the parent, **is** applied with concrete arguments
  (`RelCoeffsEqCase:219`), so the family is instantiated.
* `no_rational_logarithm` itself, the `k = 1` corollary, has **no consumer** — only docstring
  mentions. It is "the statement the analytic argument quotes", and nothing yet quotes it.

So the honest position is narrower and more useful than the first draft: the risk is not that the
hypotheses are unsatisfiable, it is that **the `k = 1` corollary is currently unconsumed and the
audit that would notice cannot see this theorem class.** `hident_of_log_rational_on_interval` is a
step toward a consumer, not a consumer.

Ledger unmoved: 22 rows, 4 distinct open obligations, 243 axioms.

## [Unreleased] — 2026-08-31 (gb)

### The differentiation step goes interval-local too — same pattern, one step upstream

New module `MachLib/LogRatDerivInterval.lean`. `deriv_eq_of_eq_on_interval` (**29 axioms**),
`logRat_deriv_eq_on_interval` (**42**), both `sorryAx`-free.

`(ga)` found the junction was interval-local except for the lift. One step upstream was still
ray-shaped: `logRat_deriv_eq` consumes `deriv_eq_of_eq_on_ray`, so the identity it produces was only
available on `[X, ∞)`. Both now have twins.

**The ray was never in the mathematics.** `div_hasDerivAt`, `logComp_hasDerivAt` and `hasDerivAt_pev`
are pointwise; the ray entered only through a *lemma about locality* that had been stated for a ray.
The ray version takes `δ = x − X`, the distance to its one boundary; an interval has two, so `δ` must
sit below both. `exists_pos_le_both` supplies one **by trichotomy** rather than by a `min` GLB lemma
this corpus does not carry — the same move as `(ga)`'s pigeonhole avoidance, and for the same reason:
the missing general tool was never needed, only a witness.

### The `k = 1` chain, and what is left of it

    interval relation
      -> logRat_deriv_eq_on_interval        (gb, new)
      -> logRat_cross_identity              pointwise already
      -> peq_of_eq_on_interval              (ga, new)
      -> no_rational_logarithm              no eventual hypothesis at all

Every arrow now exists. **What is NOT claimed: that this composition has been written.** The four
pieces line up by shape and the end-to-end application is unwritten, which is exactly the distinction
`(fy)` drew between an interface and a proof. Ledger unmoved: 22 rows, 4 open, 243 axioms.

### A placement note, stated rather than left to be noticed

`deriv_eq_of_eq_on_interval` belongs beside `deriv_eq_of_eq_on_ray` in `GermDerivFbasis`. It is in
the new module instead so this arc does not edit a 560-line file for two theorems. That is a
deliberate deferral with a trigger — move it when a second consumer appears — not an oversight.

## [Unreleased] — 2026-08-31 (ga)

### The log junction is interval-local, and the bridge is three theorems

New module `MachLib/PolyIntervalIdentity.lean`. `exists_in_interval_notMem` (**29 axioms**),
`pnorm_nil_of_zero_on_interval` (**32**), `peq_of_eq_on_interval` (**32**). All `sorryAx`-free.

An outside reader asked whether `(fy)`'s six banked results reach further than the junction they were
cut to fit. **They do, and by more than expected.**

`no_rational_logarithm` takes ten hypotheses and **not one is eventual** — every one is a polynomial
identity (`PEq`, `Pdvd`, `PNormal`) — and `logRat_cross_identity` is pointwise field algebra with no
quantifier at all. The whole apparatus was already interval-local. The single place a tail ever
entered was the final lift from "the relation holds" to `PEq`, because the corpus's only lift,
`pnorm_eq_nil_of_evZero`, is stated for a tail.

### The pigeonhole that was not needed

The obvious route to the interval lift is: a finite root list cannot cover an infinite interval, so
bound a nodup list of roots by that list's length. That wants `DecidableEq Real` for `List.erase`
plus a counting argument the corpus does not carry, and `exact?` finds nothing in Lean core either —
asked, not assumed.

**None of it is necessary.** `exists_ge_notMem` escapes a finite list by stepping *above* its upper
bound; a bounded interval forbids that, so escape **inward**. If `r` lies inside `(a,b)` the induction
runs on the strictly smaller `(r,b)`, and every point there exceeds `r`, so `y ≠ r` falls out of the
order with no counting anywhere. `pnorm_nil_of_zero_on_interval` is then a four-line twin of
`pnorm_eq_nil_of_evZero` — same `rcases pev_zero_or_finite_roots`, same shape, one lemma swapped.

The asymmetry is worth recording because it runs the *other* way from intuition: the bounded case is
harder than the unbounded one at exactly this point, since the tail's escape hatch is unavailable.

### What this unlocks, and what it does not

It makes the junction usable from a **local** hypothesis. That is the `k = 1` half of the
interval-local instrument `(fz)` named as the `OneQueryLevelSet` residue's real requirement: a
relation `a₀(x) + a₁(x)·F(S x) = 0` on an open interval no longer needs a tail to become a `PEq`.

It does **not** supply the general instrument. `(fz)`'s target allows arbitrary degree in
`F(S x)` and algebraic-function coefficients; this handles polynomial coefficients and the lift only.
Ledger unmoved: 22 rows, 4 distinct open obligations, 243 axioms.

## [Unreleased] — 2026-08-31 (fz)

### `OneQueryLevelSet`: the two stalls have one cause, and it names the instrument to build

**No new theorems.** This is a reading of existing modules, recorded because it changes what a next
attempt should build. Every sub-claim below is read off source and cited; the synthesis is mine and
is not mechanically checked.

`(fn)` recorded the obstruction analytically: at a P-root the argument diverges only logarithmically,
the bound `|N_top| ≤ C/|log (x−r)|` gives one root, deflating turns it into
`C/(|x−r|·|log (x−r)|) → ∞`, and the induction dies. *Logarithmic divergence kills a simple root; it
cannot kill a polynomial.* Two independent routes stall at the same single root.

**But the thing being proved there is algebraic, not analytic.** The relation is
`Σ N_k(x)·y^k = 0` on an interval with `y = Fbasis (S x)`, and `Fbasis x = exp x + log x`
(`EMLUnaryBasis:58`). Rates are irrelevant to that shape: if `exp(S) + log(S)` admits no polynomial
relation over `ℝ[x]` on the component, every `N_k` vanishes at once and no endpoint analysis happens
at all.

**The algebraic lane is not empty — but every instrument in it is tail-shaped.**
`Fbasis_not_algebraic` (`EMLFTranscendence:255`), `FS_not_algebraic_of_ge_linear` (`:467`) and
`_of_le_linear` (`:494`) all take `∃ X, 1 ≤ X ∧ ∀ x ≥ X, …`, the last two behind a growth premise `c·x ≤ S x`. A
bounded component supplies neither the tail nor the growth.

**The interval→tail bridge exists, and is blocked at the same feature.** `EMLAnalyticDischarge` §4
propagates interval-vanishing outward by widening and re-running the identity theorem — but
`eml_tree_analytic_on_interval` (`:160`, the 243rd axiom) requires `LogArgPos t a b`, and
`LogArgPos (.eml t1 t2) a b` unfolds (`EMLEncoder:344`) to include `∀ x ∈ (a,b), 0 < t2.eval x` — the
**Fbasis argument** positive. On the positive branch that argument *is* `S`, so widening past a zero
of `S` loses the hypothesis.

This does **not** contradict the standing note that `negGermTree_logArgPos` takes only `hQ`, i.e.
that analyticity on the negative branch is indifferent to the sign of `S`. There the log argument is
not `S`. Different branch, different `t2` — and the contrast is the point: analyticity crosses
P-roots on the negative branch precisely because `S` is not what has to stay positive there.

**And that block is not a missing lemma.** As `S → 0⁺`, `log (S) → −∞`, so the germ genuinely blows
up at the endpoint. It is not analytic there and nothing continues through it. A stronger analyticity
axiom is not available to be wished for — the mathematics closes that route, not the corpus.

So the two stalls are **one** stall. A zero of `S` is where the log branch changes, which makes it
simultaneously the place where divergence is weakest and the place where analyticity is unavailable.

#### What this says to build

An **interval-local** transcendence instrument: no tail, no growth hypothesis. That is a sharper
target than "logarithmic divergence is too weak", because it says what to construct rather than what
failed.

#### The obvious first attempt, and why it fails

Recorded because it is what a reader of the paragraph above will try first.

On the component `S` takes each value `s ∈ (0, M)` **twice**, at `x₁` and `x₂`, and both points
satisfy the relation with the *same* `y = Fbasis s`. Subtracting:

```
Σ (N_k (x₁) − N_k (x₂)) · (Fbasis s)^k = 0
```

which looks like a constant-coefficient polynomial vanishing at infinitely many distinct values of
`Fbasis s` — and `PolynomialCanonical`'s Phase E identity theorem would finish it, interval-locally
and with no rate at all.

**It fails.** `x₁` and `x₂` are *functions of* `s`, so `N_k (x₁ (s)) − N_k (x₂ (s))` is not a
constant — the polynomial identity theorem does not apply. Repairing it means allowing coefficients
algebraic in `s`, i.e. proving `exp s + log s` transcendental over the algebraic functions of `s`
near `0`. That is the same statement relocated from `x` to `s`, not a weaker one.

What the attempt does establish is that the missing instrument is not merely "interval-local" — it
must tolerate **algebraic-function coefficients**, which no instrument in `EMLFTranscendence` does.

#### One thing NOT claimed

It is tempting to call `OneQueryLevelSet` and `BoundedGermTranscendence` non-independent, the way
`(fo)` showed `TowerLowerBound` and `DecayFloor` are. **They are not the same statement**: one needs
interval-local algebraic independence of `exp(S) + log(S)`, the other a tail-shaped `¬ RatGerm`. I
have not checked that either implies the other, and the ledger keeps them as two rows.

Ledger unmoved: 22 rows, 4 distinct open obligations, 243 axioms pinned.

## [Unreleased] — 2026-08-31 (fy)

### The reduction closed, and `hchar` with it

`(fx)` predicted the remaining induction was plumbing. It was — but the plumbing came out **stronger
than the statement it was written for**, and that made a second hypothesis fall.

* **`exists_coprime_representative`** (**19 axioms**) — strip common irreducible factors from `P/Q`
  until none remain. Termination is `cofactor_length_lt`, each cancellation is transported by
  `cross_lift_of_common_factor`, and the branch condition is `∃ q, PIrred q ∧ Pdvd q Q ∧ Pdvd q P`.
* **`exists_irred_not_dividing`** (**20**) — was to be the induction; it is now six lines on top of
  the above, splitting on `2 ≤ Q'.length` and calling `exists_irred_divisor'`.
* **`lowest_terms_with_ord`** (**20**) — the same fact in the shape `no_rational_logarithm` takes:
  the exact multiplicity `PEq Q' (pmul (ppow q (r+1)) Qt)` with `¬ Pdvd q Qt`, via `exists_ord_factor`
  plus `exists_pos_ord_factor` (**19**), the one step that spends `Pdvd q Q'` to make the power positive.

**Why stripping to exhaustion instead of to a witness.** `hlow` fixes its irreducible from the *other*
fraction, so no witness-producing statement can supply it — it needs a universally quantified one.
The exhaustive induction costs no more than the one-witness induction: same recursion, same two
lemmas, different branch condition. So the one-witness version was **deleted, not kept beside** the
strong one; it is a corollary now, and there is only one induction in the file.

### `hchar`, discharged — new module `MachLib/PolyDerivNonzero.lean`

`pnorm_pderiv_ne_nil` (**37 axioms**), `pnorm_pnsum_succ_ne_nil` (**29**), `derivCoprime_of_irred`
(**37**): from `PIrred q` alone, `∀ r, DerivCoprime q (r + 1)`.

The obvious argument is *"the leading coefficient of `q'` is `(n−1)·aₙ ≠ 0"*, and it is not
available: **`pderiv` does not trim.** `pderiv [a, b] = [b, 0]`, so reading a leading coefficient off
it needs exactly the index development `PolyDerivShort` was written to avoid. The route taken is
analytic instead — if `q' ≡ 0` then `pev q` has zero derivative everywhere, `mean_value_theorem_ct`
makes it constant, and `peq_of_ev_eq` turns constancy back into `PEq q [c]`, contradicting
`2 ≤ q.length`. **`peq_of_ev_eq` — built in `(fs)` with no consumer — is what closes it.**

### The interface, hypothesis by hypothesis

`no_rational_logarithm` takes ten. Where each now comes from:

| | source |
|---|---|
| `hq`, `hPd`, `hQ`, `hQtd` | `lowest_terms_with_ord` |
| `hchar` | `derivCoprime_of_irred` — **new** |
| `hident` | `logRat_cross_identity` (`(fu)`) |
| `hPn`, `hNn`, `hDne` | the germ's own data — normalisation and a non-zero denominator |
| `hlow` | `exists_coprime_representative` applied to `N/D`, transported by `cross_identity_descends` |

### `hlow` is traded, not free — and the price was already paid

Coprimality holds for a *reduced* pair, and `hident` names the originals, so it must be transported.

This entry first recorded that transport as a **new obligation**, asserting the Wronskian-shaped
numerator "should scale by `g²`" from the shape of the expression, *not proved*. **That was wrong,
and one grep found it.** `peq_cross_common_factor` in `CrossIdentities` — which predates this whole
arc — is exactly `W(cA, cB) ≈ c²·W(A,B)`, and its docstring already explains why no divisibility
hypothesis is needed: the two `c·c′·A·B` terms cancel identically, so no derivative of `c` survives.

New module `MachLib/CrossIdentityDescent.lean` assembles it from three theorems that all predate it
— `peq_cross_common_factor`, `peq_cancel_left` (`RelCoeffsEqCase`), `pmul_nil_cancel'`
(`RelCoeffsLand`):

* `pnorm_pmul_self_ne` (**19 axioms**) — a square of a non-zero polynomial is non-zero.
* `cross_identity_descends` (**21**) — the `N/D` side.
* `cross_identity_descends_right` (**21**) — the `P/Q` side, which `lowest_terms_with_ord` also
  reduces. There the factor arrives twice by different routes — `P·Q` picks up `h²` by regrouping,
  `W(P,Q)` by homogeneity — and it is the same `h²`, so one cancellation clears both.

Both compiled on the first attempt. **The interface is ten of ten**: every hypothesis of
`no_rational_logarithm` is now a theorem here or the germ's own data.

### What is still open

The **unit branch** (`Q'.length ≤ 1`) is untouched, and it is where a *bounded* germ is finally
spent: a fraction whose reduced denominator is a unit is a polynomial, and a bounded polynomial is
constant. Route A steps 3–4 are likewise untouched. Ten of ten hypotheses is not a proof — the
end-to-end application has not been written.

### The witness gate fired, correctly

`check_all.sh` came back **10 passed, 1 FAILED (witness, rc 1)**, and the failure was the ratchet
doing its job: `derivCoprime_of_ne_zero` sat on `tools/witness_baseline.json` as a capstone whose
hypothesis nobody could supply, and `derivCoprime_of_irred` now supplies it. Baseline ratcheted
36 → 35 unwitnessed. This is the one gate whose *failure* is the good outcome, and it is the direct
descendant of the vacuous-theorem episode: a hypothesis that cannot be instantiated is tracked until
something instantiates it.

### Traps

* `pderiv` does not trim — now in a module docstring, since it is the reason for the analytic route.
* **`by_contra` does not exist in MachLib.** The memory saying so was on file and the tactic was
  reached for anyway. Third time. The lesson is not "remember harder" — a *tactic* name deserves the
  same grep-before-use as a *lemma* name, and it gets skipped because tactics feel like syntax.
* **An unquoted heredoc executed the backticks in a docstring.** Writing
  `MachLib/CrossIdentityDescent.lean` through `python3 - <<PYEOF` instead of `<<'PYEOF'` let bash
  treat every `` `identifier` `` as command substitution; sixteen `command not found` lines scrolled
  past and the file landed with **every backticked name deleted from its documentation**. `lake build`
  passed — Lean does not read docstring content. A new instance of an old shape: *a green build says
  TRUE, not "the one you need"*. Caught by reading the file rather than trusting the build.

## [Unreleased] — 2026-08-31 (fx)

### The lowest-terms cancellation's two substantive steps, built

New module `MachLib/PolyLowestTerms.lean`. `cross_lift_of_common_factor` (**15 axioms**) and
`cofactor_length_lt` (**18**), both pure polynomial.

* **Lifting** — if `P ≈ q·P₁` and `Q ≈ q·Q₁`, a cross-multiplied identity for the reduced pair lifts
  to the original. Seven `PEq.trans` steps, **every one an existing congruence** from `PolyPEq`:
  `peq_pmul`, `peq_pmul_assoc`, `peq_pmul_comm`, `PEq.refl/symm/trans`. Nothing new was required.
* **Termination** — `Q ≈ q·Q₁` with `q` irreducible gives `Q₁.length < Q.length`, because `PIrred`
  carries `2 ≤ q.length` and `pmul_length` is exact on non-empty normal lists. `pnorm_eq_self` and
  `pmul_normal` turn the `PEq` into a genuine equality first.

#### The estimate held, and why that is the point

`(fv)` called these *"bookkeeping with named ingredients, not research"*, declined to build them at
the end of a long session, and they took about twenty minutes the next morning.

That estimate was right **because it was made from what the corpus contains** — the ingredients were
named, and the naming was checked. The seven false absences of `(fw)` and before came from the
opposite: estimates made from the *shape of the argument*, with the corpus consulted afterwards or
through a search that never ran.

Same discipline, two directions. The failures were not carelessness about *whether* to check but
about whether the check **executed and was read** — which is why the searches behind this entry
printed their exit codes.

#### What remains of the reduction

The induction's plumbing: `obtain` the `Pdvd` witnesses, discharge the non-vanishing side conditions
on the cofactors, apply the IH, assemble. Every component is now a theorem; none of it is research.

## [Unreleased] — 2026-08-31 (fw)

### An errored search looks exactly like an empty one — the seventh false absence, and the worst

`(fv)` recorded two gaps in the lowest-terms reduction and said of the first: *"no theorem in
`MachLib/` states `PEq X X`, searched by name **and** by statement."*

**`MachLib/PolyPEq.lean` — a module entirely about `PEq` — contains:**

```
PEq.refl   PEq.symm   PEq.trans   peq_padd   peq_pscale   peq_pmul   peq_psub   …
```

`PEq.refl` is `rfl`, because `PolyPEq` defines `PEq X Y` as `pnorm X = pnorm Y`. And `peq_pmul` is
the congruence gap 2's cancel branch was going to need.

#### The cause is new, and worse than the previous six

The by-statement search was

```
grep -rnE "PEq ([A-Za-z_']+) \1\b" MachLib/*.lean
```

ugrep rejects the backreference: `error at position 23 … invalid escape`. **The error line was in the
output.** I read past it to the empty result below and recorded an absence.

The previous six false absences came from searching for the wrong *thing* — a name I would have
chosen, a pattern narrower than the claim, a lane instead of the corpus. This one came from a search
that **never ran at all**, reported as a search that found nothing.

That is precisely the distinction `check_all.sh` enforces for gates — **`UNAVAILABLE` is not `PASS`** —
and I built that rule yesterday, then failed to apply it to my own greps within a day. A tool that
errors and a tool that returns empty are the same two lines of terminal output unless you look.

#### Standing rule, since seven instances is a pattern and not a run of luck

Before recording an absence: **confirm the search executed.** A non-zero exit, a `warning:`, an
`error:` line — any of them means the result is `UNKNOWN`, not `absent`. Where the claim will justify
*building* something, run a second search of a different shape; where it will justify *deferring*
something, do that twice over.

#### Consequence for the construction

Both of `(fv)`'s gaps are smaller than recorded. Gap 1 does not exist. Gap 2's lifting step has its
congruence (`peq_pmul`) and its transitivity (`PEq.trans`) already available; what remains is the
`Pdvd`-witness extraction and the `pmul_length` termination argument.

## [Unreleased] — 2026-08-30 (fv)

### The lowest-terms reduction: statement fixed, skeleton typechecked, two gaps named

The single remaining piece of `¬ RatGerm (log ∘ S)`'s representation half. Not built — **scoped to
the point where the next attempt starts from a compiling skeleton rather than a plan.**

#### The statement, and why it is cross-multiplied

```lean
theorem exists_irred_not_dividing : ∀ (n : Nat) (P Q : List Real), Q.length ≤ n →
    PNormal P → PNormal Q → pnorm P ≠ [] → pnorm Q ≠ [] →
    ∃ P' Q' : List Real, PNormal P' ∧ PNormal Q' ∧ pnorm P' ≠ [] ∧ pnorm Q' ≠ [] ∧
      PEq (pmul P Q') (pmul P' Q) ∧
      (Q'.length ≤ 1 ∨ ∃ q, PIrred q ∧ Pdvd q Q' ∧ ¬ Pdvd q P')
```

`PEq (pmul P Q') (pmul P' Q)` is `P/Q = P'/Q'` **cross-multiplied**, so the induction stays purely
algebraic and the `pev` bookkeeping happens once, at the call site. Stating it as a germ identity
would drag division through every recursive step.

The `Q'.length ≤ 1` disjunct is the fraction collapsing to a polynomial — which the *bounded* setting
excludes downstream, since a bounded polynomial is constant, but which the reduction itself cannot
rule out and should not pretend to.

#### What typechecks

Everything except two holes: the `zero` case, the `¬ 2 ≤ Q.length` case, and the branch where the
irreducible factor found by `exists_irred_divisor'` already fails to divide `P` — which is the
success case and closes immediately.

#### The two gaps

1. ~~**`PEq` reflexivity** — no theorem in `MachLib/` states `PEq X X`, searched by name *and* by
   statement.~~ **FALSE — see `(fw)`.** `PEq.refl` exists in `MachLib/PolyPEq.lean`, along with
   `PEq.symm`, `PEq.trans` and `peq_pmul`. The "search by statement" that reported it absent
   **errored out** and printed nothing.
2. **The cancel branch** — where `q` divides both. Extract the witnesses from `Pdvd`, recurse on
   `(P₁, Q₁)`, and lift the result back: from `PEq (pmul P₁ Q') (pmul P' Q₁)` to
   `PEq (pmul P Q') (pmul P' Q)`, using `P ≈ q·P₁` and `Q ≈ q·Q₁` and a `pmul` congruence.
   Termination is `Q₁.length < Q.length`, from `pmul_length` and `2 ≤ q.length`.

Neither is research; both are bookkeeping with named ingredients. Recorded rather than attempted at
the end of a long session, because this arc's error rate on long constructions has been visibly worse
late than early — three of today's retractions were claims made while building, not while scoping.

#### Also noticed

`MachLib/PolyGcd.lean` carries `eea_divides` — an extended Euclidean algorithm producing a common
divisor of two polynomials. Not needed for the induction above, which only wants *one* irreducible
factor, but it is the tool if a future step needs the actual gcd.

## [Unreleased] — 2026-08-30 (fu)

### The representation half, scoped: two pieces present, one absent, and no real pole is needed

`(ft)` left `¬ RatGerm (log ∘ S)` with its analytic half done and the *representation* half untouched.
Scoped now.

`no_rational_logarithm` wants `PIrred q`, `Pdvd q Q`, `¬ Pdvd q P`, and the `q`-adic factorisation of
`Q`. Checking each **by statement**:

| piece | status |
| --- | --- |
| an irreducible factor of `Q` exists | **present** — `exists_irred_divisor'` (`PolyFactor`) |
| the `q`-adic factorisation `Q ≈ qʳ⁺¹·Qt`, `q ∤ Qt` | **present** — `exists_ord_factor` |
| an irreducible factor of `Q` that does **not** divide `P` | **absent** — nothing concludes `¬ Pdvd q P` |

The third needs `P/Q` in **lowest terms**, and reaching it is a cancellation-with-termination
argument: while some irreducible `q` divides both, cancel it; the degree of `Q` strictly drops, so it
terminates. `euclid_lemma` is present and is the step that makes each cancellation legitimate.

#### A worry that dissolved on inspection

`Pdvd q Q ∧ ¬ Pdvd q P` reads as *"`S` has a pole at `q`"*, and a **bounded** non-constant rational
germ — which is exactly `BoundedGermTranscendence`'s setting — need not have a real pole at all.
`S = x/(1 + x²)` is bounded, non-constant, and pole-free on `ℝ`.

It does not matter. `PIrred` over `ℝ` admits irreducible **quadratics**, and `q = 1 + x²` divides
`Q = 1 + x²` while not dividing `P = x`. The hypothesis is algebraic divisibility, not a real
singularity. And `Q` must be non-constant in this setting anyway: a bounded polynomial is constant, so
`S` non-constant forces `deg Q ≥ 1`.

Worth recording because the reading *"this needs `S` to have a pole"* would have looked like a
counterexample to the whole route on the bounded branch — the branch the obligation is about — and it
is not one.

#### Remaining

One construction: **reduce a rational germ to lowest terms**, or more precisely produce a single
irreducible factor of the denominator that does not divide the numerator. Ingredients named and
present; the induction is not written.

## [Unreleased] — 2026-08-30 (ft)

### Leg 2b closes — all four legs of the route are theorems, the lemma they serve is not

`cross_of_div_eq_div` and `logRat_cross_identity` (`LogRatDeriv`), both **pure field, no analysis**.

The corpus had `div_eq_div_of_cross` — *building* an equality of quotients from a cross product — but
never the direction that **reads one off**. Added, and used immediately.

#### Order of clearing, again

Multiplying through by `Q·Q` closes it in **one** step: that cancels the left quotient outright *and*
turns `Q·Q·(P/Q)` into `Q·P`, with nothing left over. Clearing the outer division first — the obvious
order — leaves a stray `Q` needing its own cancellation.

Second time today the same lesson: `D·(1/(D·D)) = 1/D` in `(fr)` was proved by cancelling a factor
rather than unfolding `1/·` twice, for the same reason. **In this corpus the order denominators are
cleared in decides whether the remainder is one `mach_mpoly` call or a chain of them**, because the
normaliser cannot relate distinct reciprocals.

#### The route ledger, complete

| leg | state |
| --- | --- |
| 1 — differentiate the germ identity | **theorem** |
| 2a — derivatives agree, written out | **theorem** |
| 2b — clear denominators to `hident` | **theorem** |
| 3 — promote `pev` equality to `PEq` | **theorem** |

#### And what that does *not* establish

**The legs are theorems; the lemma they are legs of is not.** Assembling them into
`¬ RatGerm (log ∘ S)` means feeding `hident` to `no_rational_logarithm`, whose *other* hypotheses are
the ones `(fg)` audited: `PIrred q`, `¬ Pdvd q P`, and the pole structure
`PEq Q (pmul (ppow q (r+1)) Qt)`. Those need `P/Q` **in lowest terms with an irreducible factor of
`Q` in hand** — which `(fg)` listed under *representation* and marked untouched, and which is still
untouched.

So the **analytic half** of the absent lemma is done and the **algebraic-representation half** is the
remainder. Stated this way because "all the legs are green" is exactly the sentence that would let a
reader conclude the lemma is close, and the same shape of inference has been wrong three times this
week.

## [Unreleased] — 2026-08-30 (fs)

### Leg 2 splits: its derivative half is a theorem, its algebra half is named

New module `MachLib/LogRatDeriv.lean`. `logRat_deriv_eq`: from `log (P/Q) = N/D` on a ray, both sides
differentiate and the derivatives agree at every **interior** point.

```
((P′Q − PQ′)/(Q·Q)) / (P/Q)  =  (N′D − ND′)/(D·D)
```

**No new mathematics** — it is legs 1 and 3's lemmas composing. It is worth having as a *checked
theorem* rather than as a claim that they compose, and that distinction has cost this arc twice
already: `(fq)` asserted the chain and quotient rules "compose" before either existed, and `(fk)`
found four bricks re-deriving generic machinery because nobody checked whether the summit was
occupied. Composition claims in this corpus have a poor record; this one is now typechecked.

#### The remainder, named rather than estimated

Cross-multiplying the display into `(P′Q − PQ′)·(D·D) = (N′D − ND′)·(Q·P)` — which *is* `hident` at
`k = 1` — then `peq_of_ev_eq` to promote it from a ray identity to `PEq`.

Three nested divisions cleared against each other. Standard, and **long in this corpus's idiom**:
`mach_mpoly` cannot relate distinct reciprocals, so each clearing step needs its own
`div_of_eq_mul` or `mul_left_cancel`. Recorded as open rather than estimated — the word "assembly"
has been wrong twice in two days, on `OneQueryLevelSet`'s remainder and on leg 1's composition.

#### Route ledger

| leg | state |
| --- | --- |
| 1 — differentiate the germ identity | **theorem** |
| 2a — derivatives agree, written out | **theorem** (this entry) |
| 2b — clear denominators to `hident` | open, target exact |
| 3 — promote `pev` equality to `PEq` | **theorem** |

## [Unreleased] — 2026-08-30 (fr)

### Two derivative rules the corpus was missing — `log ∘ S` and a quotient

New module `MachLib/DerivQuotientLog.lean`. Both checked absent **by statement**: nothing in
`MachLib/` concludes `HasDerivAt (fun t => log (S t)) _ _` or `HasDerivAt (fun t => N t / D t) _ _`.

* **`logComp_hasDerivAt`** — the logarithmic derivative, `(log ∘ S)′ = S′/S` for `S > 0`. This is the
  object the entire `¬ RatGerm (log ∘ S)` route turns on: a rational function's logarithmic
  derivative possessing a *rational primitive* is exactly what `no_rational_logarithm` refuses.
* **`div_hasDerivAt`** — the quotient rule. `Differentiation` ships `HasDerivAt_inv` (the reciprocal)
  and `HasDerivAt_mul`, but never composes them, so every quotient derivative in this corpus has been
  open-coded from the two.

The reciprocal-to-quotient step needs one field identity, `D·(1/(D·D)) = 1/D`, and it is proved by
**cancelling a factor** (`mul_left_cancel`) rather than by unfolding `1/·` twice. That is what
reduces the remainder to `mach_mpoly` over a single atom `1/(D·D)`; the unfolding route leaves two
reciprocals the normaliser cannot relate.

#### Leg 1 is now assembled

`(fq)` left leg 1 as *"the ray step is a theorem; the chain and quotient rules compose"*. They now
exist as named theorems rather than as a claim that they compose. Leg 1's three inputs —
`deriv_eq_of_eq_on_ray`, `logComp_hasDerivAt`, `div_hasDerivAt` — are all in place.

Leg 2 (clear denominators to `hident`) remains the open one, with its target known exactly.

## [Unreleased] — 2026-08-30 (fq)

### `deriv_eq_of_eq_on_ray` — generalised beside, then the special case derived

`deriv_eq_zero_of_zero_on_ray` (brick 1, `(fb)`) turned out to be the `g = 0` instance of something
`(fm)`'s route needs in general: **two functions agreeing on a ray have equal derivatives in that
ray's interior**. That is the step which turns a *germ* identity into a *derivative* identity, and
it is leg 1 of the three the route needs.

The neighbourhood construction was identical, so the general form was added **beside** the special
one and the special one is now three lines citing it — `29` and `30` axioms respectively. No
duplicate proof left behind.

That ordering is deliberate: the corpus's own record shows what happens otherwise. `abs_sub_comm`
has five private re-proofs of a lemma that was already exported publicly, and `a < a + 1` has seven —
**two of them added by this session**. The cheap moment to generalise is when the second instance
appears, not when the fifth does.

#### Route status after this

`(fm)`'s three legs to `¬ RatGerm (log ∘ S)`:

| leg | state |
| --- | --- |
| 1 — differentiate the germ identity | **the ray step is a theorem**; the chain rule for `log ∘ S` and the quotient rule for `N/D` compose from `HasDerivAt_log_pos`, `HasDerivAt_mul` and `HasDerivAt_inv` |
| 2 — clear denominators | untouched. Worth recording: the target *is* `no_rational_logarithm`'s `hident` at `k = 1` — `(P′Q − PQ′)·D² = P·Q·(N′D − ND′)` is exactly what cross-multiplying `S′/S = (N/D)′` gives |
| 3 — promote `pev` equality to `PEq` | **theorem** (`peq_of_ev_eq`, `(fp)`) |

Two of three legs now stand. Leg 2 is algebra with a known target, which is a different kind of open
than it was this morning — but it is still open, and the route is still a route.

## [Unreleased] — 2026-08-30 (fp)

### `peq_of_ev_eq` — the germ-to-polynomial step, discharged

New module `MachLib/PevEvEq.lean`. **Eventual equality of polynomial evaluations is polynomial
equality.**

`(fm)` sketched the route to `¬ RatGerm (log ∘ S)` in three steps and labelled the third — *promote
eventual equality of `pev`s to `PEq`* — as the one carrying the sketch's risk, with the note that
"each step looks present" has been wrong often enough this week to have no credit left.

Checked, and it composes from two existing theorems:

* `pnorm_eq_nil_of_evZero` — a polynomial whose evaluation is eventually zero normalises to `[]`.
  This is where *"a non-zero polynomial is not eventually zero"* actually lives.
* `peq_of_psub_nil` — a vanishing difference is an equality.

So the lemma is six lines, and every germ-to-polynomial argument in the corpus has been open-coding
this step. It now has a name.

**What this does and does not settle.** It discharges the *third* step of `(fm)`'s sketch. Steps 1
(differentiate the germ identity) and 2 (clear denominators) are untouched, and the sketch remains a
sketch — one of its three legs is now a theorem, which is progress and not completion.

## [Unreleased] — 2026-08-30 (fo)

### Scoping `TowerLowerBound` — it has no uniform argument at all, and the reviewer's Q4 is exactly it

The third open obligation was listed as *unscoped*. Scoped now.

```
TowerLowerBound : ∀ n u, u.depth < n → Meets (towerSpec n) u → False
```

i.e. **no tree shallower than `n` computes the `n`-fold tower**. The upper half is done for every `n`
(`towerTree_accepted`, `towerTree_depth = n` on the nose), so this is the whole of what is missing
for an infinite certified depth-optimal family.

#### It is proved level by level, and that is all

`tower_lower_bound_upto_four` is **four ad-hoc theorems**, one per level:
`exp_not_depth_zero`, `expExp_not_depth_le_one`, `tower3_not_depth_le_two`,
`tower4_not_depth_le_three`. There is **no uniform argument** — the `4` is where the case analysis
stopped.

A tempting inference, checked and **rejected**: the corrected `LogSafe` note says the quantitative
half is closed for *depth ≤ 3*, and the tower bound is proved to *N = 4*. Those numbers line up, and
they are unrelated — the four cases do not go through the envelope at all. Read as a structural link
it would have been this week's fifth overshoot, from a numerical coincidence.

#### Where the real link is

The uniform argument would be the **growth envelope used as a lower-bound oracle** — precisely what
an outside reader proposed as Q4's consumer for that machinery:

```
growth_envelope (t) (k) (hk : t.depth ≤ k) (hs : LogSafe 1 t) :
    ∃ M, ∀ x ∈ (0,1], t.eval x ≤ envelope k M x
```

If every depth-`≤k` tree sits under `envelope k M` and `towerFn n` escapes it for `k < n`, the
obligation follows for all `n` at once. **And the reviewer's suggestion to invent a benchmark family
is unnecessary: the family is already in the ledger as this open row.**

The blocker is the side condition. `growth_envelope` demands `LogSafe 1 t` of the **candidate** `t` —
an *arbitrary* tree of depth `< n`, which need not be `LogSafe` at all. Removing that is exactly the
`DecayFloor` programme's quantitative decay-by-depth bound.

#### Consequence for the ledger's shape

Two of the four open obligations are therefore **not independent**: a uniform `TowerLowerBound` runs
through the envelope, and the envelope's side condition is what the frozen `DecayFloor` cycle exists
to remove. The ledger counts them as distinct debts, correctly — they are distinct *statements* — but
a plan that treats them as separately attackable is wrong about the second one.

## [Unreleased] — 2026-08-30 (fn)

### `OneQueryLevelSet`'s remainder is NOT assembly — the P-root endpoints stall the induction

The status report said the bounded-component obstruction was closed and *"the remainder is assembly
from pieces that all exist."* Working it, that is **wrong**, and the obstruction that remains is
sharper than "assembly".

#### Q-roots and P-roots behave completely differently

A cut-free interval's endpoints are roots of `pev P` or of `pev Q`, and the endpoint argument
depends on *which*:

| endpoint | behaviour of `y = Fbasis (S x)` | induction |
| --- | --- | --- |
| **Q-root** (pole, `S → ±∞`) | negative branch: `exp (S) → 0`; positive branch: `Fbasis (S) ~ exp (S) → ∞`. **Super-polynomial** either way | **runs** — this is `poly_zero_of_exp_decay` |
| **P-root** (`S → 0⁺`) | `exp (S) → 1`, `log (S) → −∞` **logarithmically**, since `S ~ k·(x − r)` | **stalls after one peel** |

At a P-root the bound is `|N_top| ≤ C/|log (x − r)| → 0`, which gives `N_top (r) = 0` — one root.
Deflating once turns the bound into `C / (|x − r| · |log (x − r)|) → ∞`, and the induction dies.
**Logarithmic divergence kills a simple root; it cannot kill a polynomial.**

Confirmed independently: routing the same configuration through
`ContinuityDivergenceBarrier` with `log_unboundedBelowNearRight` yields the same single root, so the
stall is a property of the configuration and not of the argument I happened to choose.

#### The residue, exactly

A component with **at least one Q-root endpoint** is fine — the super-polynomial argument runs there
and kills every coefficient. So what remains is:

> **bounded components of `{S > 0}` both of whose endpoints are zeros of `S`.**

These exist: `S = (x − r₁)(r₂ − x)/Q` with `Q > 0` on the interval. Not a corner case to be argued
away.

#### On the retracted claim

"The remainder is assembly from pieces that all exist" was stated in a status report and repeated to
an outside reader. It was produced the same way as this week's other overshoots — from the shape of
the argument (*"cut, pick a branch, bound each piece"*) rather than from asking what each endpoint
actually supplies. The endpoint lemma covers poles. Zeros of `S` are also cuts, and nothing covered
them.

The correction is a strict improvement in the record: the obstruction moves from an unexamined
"assembly" to a named geometric configuration, which is the form a next attempt can actually attack.

## [Unreleased] — 2026-08-30 (fm)

### The absent transcendence input: why the `S = id` proof does NOT generalise, and what does

Route A's one absent ingredient is `¬ RatGerm (log ∘ S)` for non-constant rational `S`. The corpus
proves the `S = id` case (`log_not_ratGerm`, `EMLLogNotRational`). Read its proof before assuming it
generalises — **it does not**, and the reason is structural.

#### The `S = id` proof is a substitution trick

Assume `log = P/Q` on a tail. Substitute **`x = exp t`**: because `log (exp t) = t`, the germ identity
becomes `t · Q(exp t) = P(exp t)` — a polynomial relation in `exp t` with coefficients polynomial in
`t`, which `exp_not_algebraic_of_not_all_evZero` refuses.

The move works because `log`'s inverse is `exp`, so the substitution is *available in the language*.
For `log ∘ S` the same step needs `x = S⁻¹(exp t)`, and the inverse of a rational function is not
rational. **The trick is specific to `S = id`.**

#### What does generalise

`log (S x) = N(x)/D(x)` on a tail. Differentiate:

```
S′/S  =  (N/D)′
```

so `S′/S` — the **logarithmic derivative** of a rational function — has a *rational primitive*. That
is precisely what `no_rational_logarithm` refuses: its `hident` hypothesis

```
(N′D − N D′)·P·Q  =  k · (P′Q − P Q′) · D²
```

*is* the cleared form of `(N/D)′ = k·(P/Q)′/(P/Q)`. The mathematical content is the classical one —
a rational function's derivative has no simple poles, while a logarithmic derivative has simple poles
with integer residues, so a rational primitive forces every residue to zero and `S` to be constant.

#### The bridge that has to be built

From the **germ** identity `log ∘ S = N/D` on a tail to the **polynomial** identity `hident`:

1. differentiate the germ identity (`GermDeriv`-style, or `hasDerivAt` of a quotient);
2. clear denominators to a germ identity between polynomial evaluations;
3. promote *eventual equality of `pev`s* to `PEq` — available, since a non-zero polynomial is not
   eventually zero.

Each step looks present; the composition does not exist. **And per this week's record, "looks
present" has been wrong often enough that this is a route sketch, not an estimate.** What is
established is narrower and worth stating exactly: the existing `S = id` theorem is *not* a stepping
stone, and the general terminus is `no_rational_logarithm` rather than a generalisation of
`log_not_ratGerm`.

## [Unreleased] — 2026-08-30 (fl)

### Route A's next step, by instantiation — and the duplication audit verified rather than asserted

`fbasis_top_two_identity` (`GermDerivFbasis`) — **39 axioms, nothing from the analytic or
zero-counting lane**. Route A's step after the hinge, obtained by instantiating
`minimal_grel_identity` at `u = Fbasis ∘ S`, `v = (exp ∘ S + 1/S)·S′`:

```
EvZeroF (fun x => cd x * (ed1 x + ((exp (S x) + 1/S x) · s x) * ((m+1)·cd x)) − ed x * cd1 x)
```

It needs **none of the descent bricks** — only the chain rule `fbasisComp_hasDerivAt` and
`two_bounds'`.

#### The duplication audit is now measured

`(fk)` recorded the audit and said explicitly that it was not verified and that acting on an
unverified duplication claim would be worse than the duplication. Both halves were then checked, in
scratch, before anything was written to the corpus:

* **brick 1's content is an instance of `gEvRel_gdrel`** — six lines, using only
  `fbasisComp_hasDerivAt` and `two_bounds'`. So the chain rule for `F ∘ S` is the *only* genuinely
  new input in bricks 1–2.
* **`minimal_grel_identity` instantiates at `u = Fbasis ∘ S`** — the theorem now committed.

So the audit's claim is no longer a reading of two files; it is two typechecked instantiations.

#### Where route A stands

| step | state |
| --- | --- |
| the `log`-carrying summand vanishes at the top degree | **theorem** (`subMul_summand_top_vanishes`) |
| the top-two-coefficient identity | **theorem** (`fbasis_top_two_identity`), by instantiation |
| separate `A + B·log(S x) ≡ 0`, conclude `cd ≡ 0` against properness | argument |
| `¬ RatGerm (log ∘ S)` for non-constant rational `S` | **absent** |

Two of four are theorems, and the two that are not are precisely identified. The descent bricks are
**not** on this path; `(fk)` records what should happen to them, and that rewrite is still not done —
deliberately, since it is cleanup and the path forward is not blocked on it.

## [Unreleased] — 2026-08-30 (fk)

### DUPLICATION AUDIT: most of `GermDerivFbasis` re-derives generic machinery that already existed

Scoping route A's next step turned up `MachLib/GermDerivEntry.lean` and the tail of
`MachLib/GermDeriv.lean`. Both were already there, both are **generic in `u` and `v`**, and between
them they contain most of what `GermDerivFbasis` was built to do.

| what I built | what already existed | verdict |
| --- | --- | --- |
| `fbasis_relation_differentiates` (bricks 1–2) | **`gEvRel_gdrel`** — *"the differentiated relation is a relation"*, generic, with `gdrel v cs es = gadd es (gscale v (gyd cs))` **by definition** | duplicate |
| `fbasis_relation_differentiates_packaged` | `gdrel` **is** that packaging, definitionally | duplicate |
| `gyd_eq_append_zero` (brick 4) | **`gyd_getElem_top`** (`GermDerivEntry:151`) | duplicate |
| `fbasis_minimal_descent` (brick 5) | **`minimal_grel_identity`** (`GermDerivEntry:233`) — generic, and *stronger*: it yields the explicit top-two-coefficient identity, not merely proportionality | duplicate, and weaker |
| `fbasis_relation_substituted` (brick 3) | — | **genuinely new**; `Fbasis`-specific |
| `subMul_summand_top_vanishes` (§6 hinge) | corollary of `gyd`'s trailing zero | new *statement*, existing content |

#### How

`gEvRel_gdrel` is at **line 225 of a 247-line file**. I read that file and quoted from it four times
— `gbipev_hasDerivAt` (72), `gbipev_gadd` (135), `gbipev_gscale` (150), `gbipev_gyd` (161),
`gyd_length` (197) — and stopped **28 lines short** of the theorem that does the whole job.

The search that found those was for the *primitive* I had decided I needed (differentiate a germ
evaluation), not for the *statement* I actually wanted (a differentiated relation is a relation).
Having found a usable primitive, I built upward from it and never asked whether the summit was
already occupied. This is the week's recurring failure with the roles reversed: not *"does X exist?"*
answered wrongly, but *"is there something above X?"* never asked at all.

#### The consequence is good news for route A

`minimal_grel_identity` **is** route A's step after the hinge, already proved, generically:

```
EvZeroF (fun x => cd x * (ed1 x + v x * ((m+1) · cd x)) − ed x * cd1 x)
```

Instantiated at `u = Fbasis ∘ S`, `v = (exp S + 1/S)·S′`, that is the top-two-coefficient identity
route A needs — and it arrives without the descent bricks at all. The `S > 0` branch had already
walked this path for `exp`; the path was generic and I re-walked it for `Fbasis` without noticing.

#### What should happen to `GermDerivFbasis`

Re-derive it **on top of** `gdrel` / `minimal_grel_identity` rather than in parallel. Brick 3's
substitution and the §6 hinge survive as the genuinely `Fbasis`-specific content; the rest becomes
instantiation. Not done here — recording the audit before acting on it, because a rewrite driven by
an unverified duplication claim would be worse than the duplication.

## [Unreleased] — 2026-08-30 (fj)

### Route A's hinge is now a theorem, not a paper claim

`subMul_summand_top_vanishes` (`GermDerivFbasis`) — **18 axioms, pure list and field, nothing
analytic**.

`(fi)` recorded route A as a paper argument and flagged that this week's paper routes have
overshot three times. The argument's hinge turned out to be checkable directly, so it was checked.

#### The hinge

Of the three summands making up the differentiated list, **exactly one carries `log ∘ S`** —
`gscale (fbasisSubMul S s) (gyd cs)`, since `fbasisSubMul S s = s · (1/S − log S)`. If that summand
reached the **top** coefficient, the top coefficient would carry `log S` and the proportionality
equations could not be split into a rational part and a `log S` part. Route A would not start.

It does not reach it, and the reason was already proved: `gyd` ends in an identically-zero
coefficient (`gyd_eq_append_zero`, §4 of the descent), and `gscale` preserves that. So the top
coefficient of the differentiated relation is **free of `log S`**, and each proportionality equation
really does read

```
A(x) + B(x)·log (S x) ≡ 0        with A, B free of log
```

#### What is and is not now verified

* **Verified**: the `log`-carrying summand contributes nothing at the top degree. The step that
  route A's separation rests on.
* **Still paper**: that `B ≢ 0` forces `log ∘ S` to be a rational germ, and that the resulting
  cancellation drives `cₙ ≡ 0` against properness. Those are the remaining steps, and the transcendence
  input they need (`¬ RatGerm (log ∘ S)` for non-constant rational `S`) is still absent.

The distinction is worth keeping sharp: a route whose hinge is a theorem and whose remainder is
bookkeeping-plus-one-absent-lemma is in a different state from one that is paper throughout — but it
is not finished, and `(fi)`'s caution stands for the part that is still argument.

## [Unreleased] — 2026-08-30 (fi)

### Route A's terminus is `no_rational_logarithm`, and the audit transfers to it by luck

Following `(fh)`'s separation of the two routes, route A was worked through on paper to find where it
actually lands.

#### The shape of route A

The proportionality equations carry `log S` **only** through `fbasisSubMul = s·(1/S − log S)`, and the
top coefficient `d = cₙ′ + s·n·cₙ` is **free** of it — because `gyd` ends in a zero, which
`gyd_eq_append_zero` already proves. So each equation reads

```
A(x) + B(x)·log (S x) ≡ 0        with A, B rational
```

If `B ≢ 0` then `log ∘ S` **is** a rational germ. Everything after that — log terms cancel, hence the
formal `y`-derivative vanishes, hence `cₙ ≡ 0` against properness — is bookkeeping.

**So route A needs exactly one transcendence input:** *`log ∘ S` is not a rational germ, for `S` a
non-constant rational germ.*

#### What the corpus has

| | |
| --- | --- |
| `log_not_ratGerm : ¬ RatGerm log` | the `S = id` case, **proved** (`EMLLogNotRational`) |
| `no_rational_logarithm_scaled` | the general case at the **polynomial-identity** level (`PolyLogDeriv`) |
| `¬ RatGerm (log ∘ S)` for non-constant rational `S` | **absent** — checked by statement |

#### The audit transfers, and that was luck

`no_rational_logarithm_scaled` carries `hq`, `hchar`, `hPd`, `hkd` — **the same four hypotheses**
audited in `(fg)` against `no_proper_cleared_relation`. So the audit's findings (one free, one reduced
to `q′ ≠ 0`, both degree facts rather than restrictions) apply to *both* termini.

That is worth naming as luck rather than design: `(fg)` audited the theorem believed to be the
destination, and `(fh)` then showed the destination was a different theorem. The audit survived only
because the two share their arithmetic hypotheses. A less fortunate pairing would have made `(fg)` a
day spent auditing an interface nothing reaches.

#### Status of this route

**Paper argument, not verified.** The log-separation step is reasoning about what the coefficients
must satisfy, and this week has repeatedly shown paper routes overshooting what the corpus supports —
the `exp ∘ S` base case, the properness question, the "small" `pderiv` lemma. It is a hypothesis about
the route, recorded so the next session can attack or refute it, not a result.

## [Unreleased] — 2026-08-30 (fh)

### TWO ROUTES WERE BEING DESCRIBED AS ONE — and the built theorem is on the other one

`(fc)` described the destination as: *"substituting `E = y − log S` … descending `n` times eliminates
`y` and leaves a polynomial relation for `log S` over `ℝ(x)` — which is the shape
`no_proper_cleared_relation` already refutes."* Brief #4 and the interface audit `(fg)` both build on
that sentence.

**`fbasis_minimal_descent` does not do that.** Re-reading its own conclusion:

```
∃ L₀ d, L₀.length = ms₀.length ∧ ∀ c ∈ gscaleSub m d ms₀ L₀, EvZeroF c
```

i.e. `m · (L₀)ᵢ − d · (ms₀)ᵢ ≡ 0` for every `i` — the differentiated relation is a **germ multiple**
of the original. That is *proportionality*, reached in **one** step by minimality. It is not a
relation in `log S`, and no number of `log S` powers appears in it.

#### The two routes, separated

| | route A — proportionality | route B — iterated elimination |
| --- | --- | --- |
| step count | **one** descent, minimality closes it | `n` descents, one per degree |
| needs | comparing top coefficients ⟹ a differential equation for the leading coefficient ⟹ `S′` is a logarithmic derivative ⟹ contradiction with `S` rational non-constant | a freshly differentiated relation **at each degree**, then the `log S` relation |
| terminus | **may need no junction theorem at all** | `no_proper_cleared_relation` |
| built? | **yes** — `fbasis_minimal_descent` is its first and possibly only step | no |

Route A is also the shape the outside reader's own Q2 sketch describes — differentiate the minimal
polynomial, use separability in characteristic zero, conclude `y′ ∈ K(y)`. The corpus is on route A
and the prose has been describing route B.

#### What this does to the answers already given

* **Q1 ("is the log junction the right terminus?")** — the answer *"yes, the algebra forces `log S`
  out"* describes **route B**. On route A the terminus is a logarithmic-derivative contradiction and
  the junction may be unnecessary. The Q1 answer is not withdrawn; it is **re-scoped to the route it
  was about**, and which route to take is now an open choice rather than a settled one.
* **The interface audit `(fg)`** stands exactly as measured — those hypotheses are what
  `no_proper_cleared_relation` demands, and they transport as described. What changes is how much it
  matters, since route A may not invoke that theorem.
* **Q2 ("build the minimum differential-algebra lemma")** — on route A the abstract closure lemma
  (*algebraic ⟹ derivative algebraic*) looks like **zero** work rather than minimum work, because the
  descent operates on coefficient lists directly. Same shape as minimality sidestepping properness.
  Not yet verified; flagged, not claimed.

#### Why it went unnoticed

The sentence in `(fc)` was written while planning the route, and the theorem was built the next day
to the same *name*. Both are about "the descent", both are correct in isolation, and nothing checks
prose against a theorem's **conclusion** — the claim auditor checks a theorem's *footprint*, and the
obligations gate checks a *ledger row*. A route description is neither. **The gates cannot catch a
narrative that has drifted from its artifact**; only re-reading the statement can, which is what
happened here.

## [Unreleased] — 2026-08-30 (fg)

### INTERFACE AUDIT: do `no_proper_cleared_relation`'s hypotheses survive the descent?

An outside reader's call on the log junction was *"mathematically motivated, not
repository-motivated — but make the next task an interface audit, not another large proof,"* with the
specific worry: **do the irreducibility / coprimality / pole hypotheses transport from the
bounded-germ setup, or is the theorem too specialised to invoke?**

Audited, hypothesis by hypothesis. **The worry is largely unfounded**, and the reason it looked
worse than it is matters.

| hypothesis | transport status |
| --- | --- |
| `hkd : ∀ r, ¬ Pdvd q (pnsum (r+1) [1])` | **FREE.** `not_Pdvd_pnsum_one'` (`BipevComposition`) proves it from `PIrred q` **alone** — fully general, no side conditions. |
| `hchar : ∀ r, DerivCoprime q (r+1)` | **Reduces to one small lemma.** `derivCoprime_of_ne_zero` (`PolyDerivShort`) is general and cuts it to `pnorm (pnsum (k+1) (pderiv q)) ≠ []`, i.e. *`q′ ≠ 0`*. |
| `hpos` (positivity on a tail) | **Already a hypothesis of the descent** — `Fbasis_hasDeriv` needs `0 < S x`, so `GermDerivFbasis` carries it and the junction wants the same thing. |
| `hPn`, `hQn`, `hQne`, `hQz` | routine normalisation plus "`Q` not eventually zero". |
| `hq`, `hPd`, `hQd` | need `P/Q` in **lowest terms** and an irreducible factor of `Q`. Real, but a representation question, not a specialisation of the theorem. |
| `hcl : ClearsToExp` | **the genuine open one.** See below. |

#### Why `pnsum` made these look frightening

`pnsum r Z` is `Z` added to itself `r` times, i.e. **`r · Z`**. So `DerivCoprime q (r+1)` reads
*"`q` does not divide `(r+1)·q′`"* and `hkd` reads *"`q` does not divide the constant `r+1`"*. Both
are **degree** statements, and both are consequences of `PIrred q` rather than restrictions on it —
which is invisible until `pnsum` is unfolded, because the names suggest a coprimality condition on a
derivative tower.

That also explains why they *appeared* specimen-specific. `GermClearedSpecimen` discharges the whole
conjunction at `q = x` because **the conjunction** needed a witness after the vacuity repair — not
because each conjunct is hard. Reading "only discharged at `q = x`" as "each hypothesis is
restrictive" was my error in Brief #4's §4, and it inflated the estimate.

#### The one absent lemma

`pnorm (pderiv q) ≠ []` for `PIrred q` — the derivative of a non-constant polynomial is non-zero, a
characteristic-zero fact. **Checked absent by statement**, not by name: no theorem in `MachLib/` has
`pnorm (pderiv _)` in its conclusion, and `PolyDerivShort` proves only the *length* bound
(`pnorm_pderiv_length_lt`), never non-vanishing.

**CORRECTION, same day: this is not "small", and calling it that was the week's overshoot pattern
again.** `PolyDerivShort`'s own header says it deliberately avoided needing `pderiv`'s **leading
coefficient** — and non-vanishing is exactly what needs it. The available route is a three-module
composition:

```
pnorm (pderiv q) = []  →  q′ ≡ 0 as a function        (pev_pnorm)
                       →  q constant                   (mean_value_theorem_ct / mvt_bound)
                       →  q bounded, contradicting     (PevLeading: c·xᵈ ≤ |pev q x| on a tail, d ≥ 1)
```

Each step exists; the composition does not, and it crosses `PolyEvZero`, `Rolle`/`Weierstrass` and
`PevLeading`. So `hchar` is *reduced to a named, general fact* — which is real progress and is what
the audit claims — but it is **not** one small lemma away, and the estimate above said otherwise
before the routes were checked. The pattern is the one this changelog keeps recording: naming the
next obstacle from the shape of the argument rather than from what the corpus actually provides.

#### The genuine residues, in the reviewer's own three-part frame

* **Representation** — `P/Q` in lowest terms with an irreducible factor of `Q` in hand. Not hard, not
  present.
* **Nontriviality** — the descent must not have produced the zero relation. Untouched.
* **Hypothesis transport** — **largely solved**: one hypothesis free, one reduced to the absent lemma
  above, one already carried by the descent. What remains is `ClearsToExp` membership: the descended
  coefficients are rational in `x`, and clearing by their common denominator should land them in the
  `expCoeffs` image with trivial `exp`-degree. *Plausible and unverified* — it is now the top item.

**Net:** the junction is closer than Brief #4 estimated, and the estimate was inflated by reading a
witness-for-a-conjunction as evidence that each conjunct was restrictive.

## [Unreleased] — 2026-08-30 (ff)

### `tools/check_all.sh` — the first all-gates runner, and the composite-exit-code defect it fixes

There was no single runner. Every session assembled one inline as `{ gate1; gate2; … }`, and such a
block exits with the status of its **last** command. So a run in which the claim audit *failed*
reported `exit 0`; the failure was visible only because the audit's verdict line happened to be
printed and read by a human eye.

That is the `gate | tail` disease with a wider blast radius: **a composite's exit code is not its
gates'.** It had been latent in every gate invocation of this arc.

#### What the runner does, each rule a defect already paid for

* every gate's `rc` is captured **immediately**, before any pipe or `echo` can overwrite `$?`;
* nothing is piped in a way that discards a status — output goes to a file, then is read;
* **`UNAVAILABLE` (rc 2) is distinguished from `FAIL`**, with its own exit code — "could not run" is
  not "passed";
* the summary names every non-passing gate with its last twelve lines, so a scrolled-off failure
  cannot hide.

Current state: **11 gates, all green, `rc = 0`** — build, aggregator, consistency, axiom-ledger,
obligations, discovered, claims, witness, hypothesis, absence, sorry.

#### The self-test tests the mechanism that was broken, not the one that worked

A first `--selftest` injected a failing gate, confirmed it **registered in the accumulator**, and
exited `0`. That tests *detection*, which was never broken. The bug was the failure **reaching the
exit code**. The self-test now falls through to the real summary and exit path and returns `1` — the
same code path a real failure takes. A canary that does not traverse the mechanism under suspicion is
theatre.

#### And it shipped with its own comment already overstating it

The verdict-surfacing line was `tail -n 3 | grep`, which silently dropped the obligations verdict
because that gate prints two count lines *after* its `OK`. Cosmetic — `SUMMARY` decides from the
captured `rc`, never from the text — but the comment said "surface the gate's own verdict line" and
it did not always. Fixed before committing. **A comment that overstates what a gate does is how a
gate's scope drifts from its description**, which is the same disease as the substring deny-list and
the too-narrow absence grep, in shell.

## [Unreleased] — 2026-08-30 (fe)

### §5 lands on the second attempt — the germ-side wiring, and what made the difference

`bipev_abs_bounded_on_Icc` (41 axioms) and `bipev_zero_near_pole_kills_head` (49), neither touching
the analytic or zero-counting lane. `PolePolynomialKill` is now complete through §5, and
`(fd)`'s note that §5 was "deliberately not here" is superseded — the module's own status section
says so rather than leaving the two in contradiction.

```
bipev_zero_near_pole_kills_head :
  a one-query germ vanishing along a pole approach kills its head coefficient
```

#### What actually changed between the attempts

Nothing mathematical. The first attempt reached for four lemma names that did not exist and left a
`sorry`; the second checked **every** name by *statement* before writing a line:

| needed | found as |
| --- | --- |
| `0 ≤ a → b ≤ a + b` | `add_le_add_wit` + `le_max_right`, no new lemma |
| `a ≤ b → c ≤ d → a + c ≤ b + d` | `add_le_add_wit` (`EMLDepth2InvX`, already imported) |
| `a ≤ b → exp a ≤ exp b` | `exp_monotone` (`Exp`) |
| `a ≤ b → 0 ≤ c → c * a ≤ c * b` | `mul_le_mul_of_nonneg_left` (`Forge`) |
| `M < M + 1` | **not needed** — `add_le_add_wit hM0 (le_refl 1)` gives `0 + 1 ≤ M + 1` directly |

That last row is the interesting one: the "missing" lemma was an artifact of how I had phrased the
step, not of the corpus. Checking by statement dissolved it instead of adding an eighth private copy
of `a < a + 1`.

The one genuine miss was an **import**, not a lemma: `bipev` lives in `EMLFTranscendence`, which the
module had no reason to import until §5. `unknown identifier` for a definition is a different
diagnosis from `unknown identifier` for a lemma, and conflating the two is what produced the first
attempt's guesswork.

#### Totalisation, a fifth time

`H = bipev N' · (exp (S ·))` is bounded because `0 < exp (S x) ≤ 1` on the negative branch — there is
no growth in `y` to fight at all. `Fbasis` **is** `exp` where its argument is non-positive, so the
`log` half never appears. Fifth independent occasion in this arc where the totalised operator turned
the expected pathological case into the trivial one.

#### §6 — the one ingredient that really was absent

`neg_floor_nbhd_of_continuousAt` (32 axioms). `neg_nbhd_of_continuousAt` (`IntermediateValue`) gives
`f y < 0` near a point where `f r < 0`; the pole bound needs a **floor**, `f y ≤ −p` with `p > 0`,
because a bound that only says *negative* cannot be multiplied up by `exp T` to give anything.

**Checked absent by statement, not by name** — the existing lemma's conclusion is `0 < f y` / `f y < 0`
with no witness for the distance from zero. After four false absences the previous day, that check was
run before writing rather than after failing.

A rewrite-loop detail worth keeping: `f r + (−f r)/(1+1) = −((−f r)/(1+1))` cannot be closed by
rewriting `f r`, because `f r` occurs **inside** the half being rewritten. `conv_lhs` does not exist
here. Abstracting the half — `∀ q, q + q = −f r → f r + q = −q` — makes it a ring fact about one
atom, and the instantiation happens outside the rewrite.

#### What is left on this arc: assembly, not ingredients

The pole lower bound `S (r + exp (−T)) ≤ −(c · exp T)` now follows from pieces that all exist:
`pev_deflate` at a root of `pev Q` turns `pev Q (r + exp (−T))` into
`exp (−T) · pev (deflate r Q) (r + exp (−T))`; `div_mul_div_eq` (`EMLRationalGerm`, reachable) moves
the `exp T` out; §6 holds the quotient below a negative floor near `r`. Everything downstream of that
bound is now a theorem.

## [Unreleased] — 2026-08-29 (fd)

### The endpoint lemma for `OneQueryLevelSet` — and four "missing" lemmas that all existed

New module `MachLib/PolePolynomialKill.lean`. `eq_zero_of_small_nearby` (32 axioms) and
`small_nearby_of_exp_decay` (41), neither touching the analytic or zero-counting lane.

Written after an outside reader reprioritised: attack the bounded-component hole in
`OneQueryLevelSet` *before* sinking months into differential algebra, on the grounds that it has the
smallest clearly-isolated missing clause. That read was right, and for a sharper reason than
expected — see below.

#### The argument

On a bounded pole-free component the rational argument `S` has constant sign; where it is negative
the germ is `bipev N x (exp (S x))` by totalisation. If the germ vanishes identically there then
`N₀(x) = −exp (S x)·H(x)` with `H` bounded near the endpoint — and the endpoints of a *bounded*
component are **poles of `S`**. Where `S → −∞`, the right side decays faster than any power of
`x − r`, while a non-zero polynomial vanishes to *finite* order. So `N₀ ≡ 0`, `exp (S x) ≠ 0` divides
out, and the same runs on the next coefficient.

The conclusion is stronger than "this component is fine": every coefficient dies, so the germ
vanishes **everywhere** and the level set is co-finite. The bad case does not exist rather than being
excluded.

#### Growth: unavailable there, exactly right here

`BoundedGermTranscendence` cannot use growth — `polyEnvelope_of_Fbasis_floor` proves `F ∘ S` is
polynomially enveloped on that branch. **The same machinery is precisely what this needs.** Decay at
a finite pole rather than growth along a tail: same tool, opposite end.

And the two ends trade difficulty in the opposite direction from how they read. Where `S → +∞` the
germ diverges and the continuity-versus-divergence barrier applies *in principle* — but that barrier
has **no user outside its own module** and driving it needs *local* dominance, while every dominance
tool here is tail-shaped. The `−∞` end, which looked like the ugly residue, hands over
super-polynomial decay for free.

#### FOUR FALSE ABSENCES IN ONE AFTERNOON

An earlier revision of the new module's header listed four field lemmas as **missing** and deferred
§2 on that basis. That claim shipped into a docstring. **All four existed:**

| searched for | actually called |
| --- | --- |
| `div_self` | `self_div` (`FieldLemmas`) |
| `mul_one_div_cancel` | `mul_inv` — a `Basic` **axiom**, named in `FieldLemmas`' own header |
| `one_div_one_div` | `one_div_one_div_pos` (`EMLDepthTameness`) |
| `mul_lt_mul_of_pos_left` | `mul_lt_mul_pos_left_wit` (`EMLDepth2InvX`), already imported |

Searching by **name** is searching for the name *you* would have chosen; this corpus chose others.
Searching by **statement** found all four in one pass.

A fifth instance the same afternoon, smaller radius, same disease: a grep pattern requiring a
trailing space reported `div_pos_of_pos_pos` absent **while the file was compiling with it**. And a
sixth: "five private copies of `abs_sub_comm`" came from `grep private theorem abs_sub_comm`, which
by construction could not see the *public* one — and the public one was the whole point.

This is now the sharpest form of the recurring lesson in this repository, and it is not the one the
`absence_audit` registry was built for. That gate checks *registered* absence claims. These were
absence claims made **in passing, to justify deferring work** — and every one of them was wrong in
the direction that created work rather than avoided it.

#### §4 — `|pev L|` bounded on a compact interval

`pev_abs_bounded_on_Icc`. `continuousAt_bddAbove_Icc` bounds a continuous function **above**, and
`abs` needs both directions, so it is applied twice — to `pev L` and to `0 - pev L`, whose continuity
comes from the same `HasDerivAt_sub` construction `PevSignOnCutFree` already uses for the mirrored
intermediate value. Reusable well beyond this arc.

#### §5 stopped deliberately, and the file says so

`bipev (L :: Ls) x y = pev L x + y * bipev Ls x y` is **definitional**, so
`pev N₀ x = −exp (S x)·bipev N' x (exp (S x))` needs no lemma; `H` is bounded because
`0 < exp (S x) ≤ 1` on the negative branch (totalisation again — `Fbasis` *is* `exp` there, so the
`log` half never appears); and the pole bound feeds `poly_zero_of_exp_decay` at `a = 0`.

A first attempt at it reached for four non-existent lemma names **and left a `sorry` in the file**.
Both were removed rather than committed. Having hit the same reach-for-the-name-you-would-choose
failure twice inside one file, the honest response is to stop and return with a fresh look rather
than push through on placeholders — so §§1–4 are what this module ships, and its header records why.

#### §3, same commit — the endpoint lemma is CLOSED

`poly_zero_of_exp_decay` (47 axioms, still nothing from the analytic or zero-counting lane):

> **A polynomial with super-polynomial decay at a pole is identically zero.**

Not "zero at `r`", not "zero on the component" — *identically* zero. So the germ it came from
vanishes everywhere and the level set is co-finite: the first disjunct of `OneQueryLevelSet` holds,
and the bad case is shown not to exist rather than being excluded.

`pev_deflate` peels `(x − r)`, `deflate_length` drops the degree, and each peel divides the value by
`exp (−T)` at the evaluation point — i.e. **multiplies the bound by `exp T`**, which the
`a·T − c·exp T` form absorbs by bumping `a`. The hypothesis is therefore stable under deflation and
the induction is on length alone.

**That stability is why the bound carries a free `a`.** A shape with a fixed power would need
re-deriving at every peel; the linear coefficient is not decoration, it is what makes one induction
suffice.

## [Unreleased] — 2026-08-29 (fc)

### Brick 2: the differentiated relation, packaged for the descent

`fbasisChainMul`, `fbasis_relation_differentiates_packaged`, `gEvRel_fbasis_deriv`,
`gadd_gscale_gyd_length` — all in `GermDerivFbasis`, all assembly from lemmas that already existed.

#### Why packaging is a step at all

`gcancel_top` (`GermRelation`) descends **two relations in one `u`**. `(fb)` left the differentiated
form as a *sum of two shapes* — `gbipev es …` plus a multiplier times `gydiff cs …` — which
`gcancel_top` cannot take. `gbipev_gyd`, `gbipev_gscale` and `gbipev_gadd` fold it into the single
list `gadd es (gscale (fbasisChainMul S s) (gyd cs))`, and the proof needs no new arithmetic at all:
three rewrites and the `(fb)` theorem.

`gEvRel_fbasis_deriv` then puts it in `GEvRel` form. The threshold moves from `X` to **`X + 1`**,
because `GEvRel` wants a *closed* ray and the derivative only exists on the open one; `X + 1` sits in
the interior of `[X, ∞)` and inherits `1 ≤ ·`. `gadd_gscale_gyd_length` supplies `gcancel_top`'s
standing length side condition from `gyd_length`, `gscale_length` and `gadd_length_of_le`.

#### No specimen here, and the reason is not laziness

`gEvRel_fbasis_deriv`'s hypothesis `hrel` is satisfiable **only degenerately**: any true relation of
that form is the zero polynomial, which is exactly what the arc is trying to establish. This is a step
*inside a refutation* — its premise is the thing being refuted — so a specimen would validate the
mechanism while looking like evidence for the premise.

That distinction is now written into the module, next to the two theorems that *do* carry firing
specimens (`zeroList_specimen`, `cutFreeBounds_specimen`) precisely because their premises are
genuinely satisfiable. "Every theorem needs a specimen" is the wrong rule; "every theorem whose
premise could be vacuous needs one" is the right one.

#### The destination changed, and for the better

Working the algebra through: substituting `E = y − log S` into the differentiated relation gives
coefficients in `ℝ(x)[log S]` with top-degree coefficient `cₙ′ + n·S′·cₙ`. Descending `n` times
eliminates `y` and leaves a polynomial relation for **`log S`** over `ℝ(x)` — which is the shape
`no_proper_cleared_relation` (`GermClearedDescent`) already refutes.

So the arc plausibly lands on the `S > 0` branch's existing investment rather than needing a new
`exp ∘ S` transcendence result, which is what `(fb)` predicted it would need. Better destination,
and it reuses work already paid for.

#### Brick 3, same commit: the substitution — and the coefficient ring finally matches

The packaging above still leaves the chain-rule multiplier containing `exp ∘ S`, so the
differentiated relation's coefficients are **not** in the same ring as the original's. Descending two
relations over different rings means nothing, so this had to be fixed before anything else.

`Fbasis` is *definitionally* `exp + log`, so `exp (S x) = u x - log (S x)` needs no lemma, and

```
(exp (S x) + 1/S x)·s x  =  s x · u x  +  s x · (1/S x - log (S x))
```

splits the multiplier into a part **linear in `u`** — which raises the `y`-degree by one, and is
exactly the `0 ::` prepend, via `gbipev_zeroCons` — and a part **free of `u`**.

`fbasis_relation_substituted` (38 axioms, still nothing from the analytic or zero-counting lane) is
the result: **every coefficient of the differentiated relation is free of `u`.** Both relations now
live over `ℝ(x)` extended by `log ∘ S`, which is the ring `no_proper_cleared_relation` speaks in.

#### A correction to this entry's own algebra

The top coefficient `cₙ′ + n·S′·cₙ` quoted above is a fact about the **substituted** form, not about
brick 2's packaging. In brick 2's form the multiplier is an opaque coefficient function, the `gyd`
part has `y`-degree `n − 1`, and the top coefficient is just `cₙ′`. Both presentations are correct;
they are not the same list, and only the substituted one supports the descent. Worth stating because
the two differ by exactly the term that makes the argument work.

#### Brick 4, same commit: the descent is now SET UP

`gcancel_top` wants two relations in one `u`, **of equal length**. The substituted list is one longer
than the original — that is the `0 ::` raising the `y`-degree — but its top slot is identically zero,
so the extra degree is spurious.

```
gadd_append_right    gadd a (b ++ [t]) = gadd a b ++ [t]        for a.length ≤ b.length
gscale_append        gscale a (l ++ [t]) = gscale a l ++ [a·t]
gyd_eq_append_zero   gyd (c :: cs) = ys ++ [z]  with  z ≡ 0     — 5 axioms, pure list induction
fbasisDeriv_descends → a SECOND relation, same length, same coefficient ring
```

`gyd cs` ending in a zero is the formal statement that the `y`-derivative's degree genuinely drops.
It is stated with `∀ x, z x = 0` rather than syntactic equality, because `gadd` builds
`fun x => c x + d x` — the last entry has the *shape* `0 + 0`, not the literal zero function.

**Why not pad the original instead.** Appending a zero coefficient to `cs` would equalise the lengths
just as well, and it is the obvious move. It is also useless: `gcancel_top` against a *zero* top
coefficient reproduces the original relation scaled, so nothing descends. The trailing zero has to
come off the differentiated side, which is the harder direction and the reason for the list surgery.

**Ordering is load-bearing, again.** `gadd_append_right` appends on its *second* argument, so
`fbasisDerivList` puts the one-longer summand there and peels the zero in one application. `(fc)`'s
ordering is value-equal but would need a mirrored lemma plus associativity, so `fbasisDerivList`
re-derives from `fbasis_relation_differentiates` rather than from `fbasis_relation_substituted`.

#### Brick 5, same commit: the descent EXECUTED — and the question above did not need answering

I wrote that properness of the descended relation was "the first step in this arc that is not
mechanical". **Wrong, and the corpus already had the answer.** Routing through *minimality* sidesteps
properness entirely: `all_gcoeffs_evZero_of_shorter'` (`GermRelation`) turns "shorter than the minimal
proper relation" into "every coefficient is eventually zero" while asking nothing whatsoever about top
coefficients.

`fbasis_minimal_descent` therefore yields, from a minimal proper relation for `u = F ∘ S`, the system

```
∀ i,   m · (L₀)ᵢ  −  d · (ms₀)ᵢ  ≡  0    eventually
```

with `m` the minimal relation's top coefficient and `d` the differentiated one's — concrete equations
over `ℝ(x)` extended by `log ∘ S`. Two small lemmas were missing and are proved here:
`gscaleSub_length_le`, and a non-empty-list form of brick 4's descent.

**The general lesson, since this is twice in one arc.** Both times I named the next obstacle by asking
*"what would I have to prove?"* rather than *"what does this corpus already prove?"* — first the
`exp ∘ S` base case that turned out to be the wrong target, now properness that turned out not to be
needed. Predicting the obstacle from the shape of the argument reliably overshoots what the existing
machinery demands.

**Next:** extracting a contradiction from that system, which is where the arc meets
`no_proper_cleared_relation`'s territory.

#### A seventh copy

Brick 5 needed `a < a + 1` again while compiling in isolation — the **seventh** private copy, two of
them added by this session. The cleanup this entry keeps deferring is now bigger than when it was
first noticed, which is the usual way.

## [Unreleased] — 2026-08-29 (fb)

### `BoundedGermTranscendence`: the differentiation brick, and why growth is provably unavailable

New module `MachLib/GermDerivFbasis.lean` — `fbasisComp_hasDerivAt`,
`deriv_eq_zero_of_zero_on_ray`, `fbasis_relation_differentiates`. **38 axioms, none from the analytic
or zero-counting lane.**

#### The route is the corpus's own

`EMLFTranscendence`'s docstring says it outright: *"the missing step is
differentiation-preserves-algebraicity, not anything about `exp`."* This is the mechanical half of
that step, and all three tools already existed — `gbipev_hasDerivAt` (`GermDeriv`) differentiates a
germ-coefficient relation, `Fbasis_hasDeriv` (`EMLGermSign`) gives `F′ = exp + 1/·` on the positive
side, `HasDerivAt_comp` chains them.

From `Σⱼ cⱼ(x)·F(S x)ʲ = 0` on a ray:

```
Σⱼ cⱼ′(x)·F(S x)ʲ  +  (exp (S x) + 1/S x)·S′(x) · ∂/∂y[Σⱼ cⱼ(x)·yʲ](F (S x))  =  0
```

#### Why the usual instruments are not merely unhelpful but *provably* silent

`BoundedGermEnvelope.polyEnvelope_of_Fbasis_floor` is a **theorem**: on the bounded branch `F ∘ S` is
polynomially enveloped. Every exclusion instrument here — `not_polyEnvelope_of_ge_exp`,
`not_polyEnvelope_of_ge_exp_scaled`, and through them `FS_not_algebraic_of_ge_linear` / `_of_le_linear`
/ `Fbasis_not_algebraic` — needs the generator to **outgrow every polynomial**. On this branch that
hypothesis is false, as a theorem. The instruments are not silent by accident of formulation.

#### The open ray is forced

The conclusion holds on `X < x`, not `X ≤ x`. A derivative is local, the relation is known only on
`[X, ∞)`, and `HasDerivAt_congr` wants `|y - x| < δ` — at the endpoint no such δ exists inside the
ray. `deriv_eq_zero_of_zero_on_ray` takes `δ = x - X` and is stated separately because it is about
any function, not about germs.

#### `Fbasis_hasDeriv` was `private`

Made public. Third time this session a needed lemma was `private` one module away
(`le_addr`/`le_addl` were the first two). Worth noticing as a pattern rather than as three incidents:
`private` is being used for *"local to this proof"* and then the lemma turns out to be the interface.

#### What is NOT done, and no obligation for it

This produces a relation, not a contradiction. Eliminating `F (S x)` between the two relations is
where the Euclidean layer (`euclid_lemma`, `Pdvd`) would come in — and then the **real** base case is
needed: `exp ∘ S` transcendental over the rational functions for non-constant rational `S`.

That is **not** `exp_not_algebraic`. That one is about `exp x` and is proved by growth, which this
branch has ruled out. Writing "the base case exists" would have been the natural sentence and it
would have been wrong — the base case that exists is for the wrong function, by the wrong method.

`constant_germ_is_algebraic` shows the non-constancy hypothesis cannot be dropped: `S ≡ 0`,
`Fbasis 0 = 1`, and a non-trivial bipoly vanishes identically.

#### Also noticed — and the first count of it was wrong

Six declarations state `abs (x - y) = abs (y - x)`. **Five are `private`** — `ExpLipschitz`,
`InverseTrigBounded`, `NewtonReciprocalDivision`, `TransNodes`, `TanLipschitz` — and the sixth,
`TrigLipschitz.abs_sub_comm`, is **public**. So this is not five copies of a missing lemma; it is
five private re-proofs of a lemma that was already exported. Six private copies of `a < a + 1` sit
alongside them, one of which this session added.

I first wrote "five private copies" from a grep for `private theorem abs_sub_comm`, which by
construction could not see the public one — and the public one is the whole point. A pattern narrower
than the claim it supports, for the third time today. Recorded, not fixed: it is a cleanup, not a
correctness issue, and it wants one commit of its own rather than a rider on this one.

## [Unreleased] — 2026-08-29 (fa)

### One sign per cut-free interval — and the residue is a NEW KIND of input, not more assembly

New module `MachLib/PevSignOnCutFree.lean`. `pev_sign_constant_on_cutFree`,
`ratGerm_sign_constant_on_cutFree`, `pev_ne_zero_on_cutFree`, plus the two lemmas they needed:
`pev_continuousAt` and `pev_root_between_of_opposite_signs`. All four confirmed absent beforehand by
exhaustive grep.

#### What it gives

With the roots of `pev P` and `pev Q` as the cut list, a cut-free interval has **one sign of
`P/Q` throughout**, so exactly one branch tree describes the whole of it — `toEML (queryTerm …)`
where `S > 0`, `negGermTree` where `S < 0`. There is no third case inside, because `S = 0` needs a
root of `pev P`, which is a cut. All four quotient-sign combinations already existed; the corollary
is a case split.

`intermediate_value` fires in **one direction only** (left-negative, right-positive, `a < b`). Both
orders are needed, so the reversed case goes through `0 - pev L`, whose roots are exactly `pev L`'s.
`pev_root_between_of_opposite_signs` packages both once.

**Footprint: 40 axioms — derivative rules, `hasDerivAt_continuousAt`, `sup_exists`, and no
`analytic_*`, no `rolle`, no `zero_count_bound_classical`.** Sign constancy is bought with
*completeness*, not with the zero-counting lane. A later step needing `encBound_bounds` pays that
lane separately; this module does not pre-pay it.

#### Caveat the callers must carry

The hypothesis is a **finite** list containing every root. If `pev P ≡ 0` no such list exists, the
hypothesis is unsatisfiable, and these theorems say nothing about that case — it is
`pev_zero_or_finite_roots`'s *other* branch, which the query modules already split on
(`queryGerm_zero_branch_bound`). Not a defect; a division of labour that must not be forgotten at the
call site.

#### The residue, scoped properly — and a conclusion I had to walk back

The route to `OneQueryLevelSet` is assembled except for one clause: `encBound_bounds` needs a point
*inside* each interval where the germ is non-zero, and on a **bounded** cut-free component nothing
supplies it yet.

Looking for what could, I first searched the transcendence lane and found a clean story. Every
`: False` in `EMLFTranscendence` — **8 of 8, counted by script, not by eye** —

```
not_algebraic_of_dominates_exp   Fbasis_not_algebraic        not_algebraic_of_dominated_by_exp
FS_not_algebraic_of_ge_id        FS_not_algebraic_of_le_negId
FS_not_algebraic_of_ge_linear    FS_not_algebraic_of_le_linear   exp_not_algebraic
```

— has a **tail** hypothesis `∃ X, 1 ≤ X ∧ ∀ x ≥ X`, and not by oversight: all eight run through
`not_polyEnvelope_of_ge_exp_scaled` and `EvDom`, which are **growth envelopes**. Growth is the
mechanism, and a bounded interval is where growth says nothing. `DiffAlgebraic` and
`BoundedGermEnvelope` contain no `: False` at all.

I was about to conclude *"the gap needs a new kind of input the corpus does not have."* Then I ran
the census **corpus-wide** instead of over the lane I had picked, and it refuted that:

```
281 theorems/axioms conclude False;  20 have a tail hypothesis;  8 have an INTERVAL hypothesis
```

Re-derivable — split every `.lean` outside `Discovered/` on declaration boundaries, keep the
declarations whose *head* (before `:=`) matches `:\s*False\b`, and classify by whether that head
contains a tail bound (`1 ≤ X` / `X ≤ x`) or a two-sided strict interval (`_ < x … x < _`, `Ioo`,
`Icc`). Classify by the **head**, not the body: a growth proof mentions intervals all over its
internals while its hypothesis is a tail.

Those eight exist, and two are directly relevant:

* **`CompactIntervalNonApproximation`** — an interval-local barrier for EML trees, built from
  `enc_combinedBound` plus IVT-induced zeros. Interval-local non-representability is *already done*
  here, once.
* **`ContinuityDivergenceBarrier.no_continuousAt_eq_unboundedBelowNearRight`** — a function
  continuous at `x₀` cannot equal, on a one-sided neighbourhood, a target unbounded approaching
  `x₀`. Explicitly advertised as tree- and target-agnostic.

The second bites here. A bounded cut-free component's endpoints are **poles of `S`**. Where
`S → +∞`, `exp(S) → ∞` and the germ diverges — while a germ identically zero is bounded. That is the
barrier's exact shape, with machinery that already exists.

**So the honest residue is narrower than "a new kind of input".** It is the sub-case where `S → −∞`
at *both* ends of a bounded component: there `exp(S) → 0`, the germ tends to its constant-in-`y`
coefficient `pev N₀`, and no divergence is available to contradict. That sub-case is open. The
`+∞` endpoints look reachable with what is on the shelf.

The lesson is the one this repo keeps re-learning: **I searched the lane I expected the answer to be
in, and the lane's uniformity read as the corpus's.** The count that mattered — 8 interval-shaped
results — only appeared when the search covered everything. Filed against
`absence_from_a_truncated_search_is_not_absence`, whose point is not that greps get truncated but
that the *scope* does.

## [Unreleased] — 2026-08-29 (ey)

### Gluing over an UNSORTED cut list — the interval-independence step, and what it costs

`ZeroCountOn.glueOverCuts` (`ZeroCountGlue`) and `uniformZeroBound_of_cutFreeBounds`
(`EMLZeroListFromBound`). A bound on every **cut-free** sub-interval gives a bound on *every*
interval, with a constant that mentions neither endpoint.

#### Why unsorted matters

`pev_zero_or_finite_roots` hands over a `List` of roots with **no order structure**. Sorting it is
real work this corpus does not have lying around. `glueOverCuts` needs none: at each cut it asks only
*is this cut strictly inside the current interval*, splits if so, and recurses on the whole remaining
list in both halves. A leaf interval is cut-free because every cut was either split at — making it an
endpoint, not interior — or skipped for an interval containing the leaf.

The hypothesis is **interval-relative** (`a ≤ u → v ≤ b → …`), and that is load-bearing rather than
decorative: the left-half recursion needs to know `v ≤ m` in order to discharge `m` itself from the
cut-free obligation. A globally-quantified hypothesis does not carry that and the induction does not
close.

#### The cost, stated rather than buried

```
cutBound 0       K = K
cutBound (n + 1) K = cutBound n K + cutBound n K + 1
```

**Exponential in the number of cuts.** Recursing into both halves with the whole remaining list is
what buys freedom from sortedness, and doubling is what it costs. That is acceptable here because
`UniformZeroBound` asks only for *some* interval-independent constant and `n` depends on `P`, `Q`
alone — but it is not free, and `ZeroCountOn.glueList` gives the sharp `(n+1)·K + n` for anyone who
does have a sorted list.

`cutFreeBounds_specimen` makes the price concrete instead of leaving it as a remark: `x - 1` has one
zero, `uniformZeroBound_specimen` proves the sharp bound `1`, and routing it through a single cut
yields `cutBound 1 1 = 3` — proved as `rfl`, not asserted. Three where one is true, for one cut.

#### Footprints

| theorem | axioms | |
|---|---|---|
| `ZeroCountOn.glueOverCuts` | **10** | order only — `leR`, `ltR`, `lt_total`, `lt_trans_ax`, `lt_irrefl_ax`, `le_iff_lt_or_eq` |
| `uniformZeroBound_of_cutFreeBounds` | 11 | the same, plus `zeroR` to say `f z = 0` |
| `cutFreeBounds_specimen` | 20 | arithmetic, only to *name* `x - 1` |

Still no arithmetic in the reduction itself.

#### What remains, named precisely

The route to `OneQueryLevelSet` is now: cuts = roots of `pev P` and `pev Q` (from
`pev_zero_or_finite_roots`); on a cut-free interval `S = P/Q` has constant sign, which
`hasDerivAt_pev` + `hasDerivAt_continuousAt` + `intermediate_value` deliver, so exactly one branch
tree applies throughout; `encBound_bounds` then bounds that interval — **given a point in it where
the germ is non-zero.**

That last clause is the whole remaining gap, and it is the residue `(ew)` identified, now in its
final position: `¬ EvZeroF` supplies a non-zero point only on a *tail*, and a bounded cut-free
interval between two poles is where no tail reaches.

**No obligation is registered for it.** The demand "the germ is non-zero somewhere in every bounded
cut-free interval" might be vacuous or might be false, and `EMLDeclampUniform` already documents what
promoting an unvalidated per-piece demand cost this arc once. This module ships the reduction and
stops, exactly as that one did.

## [Unreleased] — 2026-08-29 (ex)

### Zero counting, glued — one lemma for three predicates, at six axioms

New module `MachLib/ZeroCountGlue.lean`, importing `MultiVarBucket` **and nothing else**.

#### Three predicates, one statement

```
BoundedZerosBy f a b K     (EMLExplicitBound)  -- f : PfaffianFn, one interval
UniformZeroBound f N       (EMLZeroBoundRay)   -- f : Real → Real, EVERY interval
UniformZeroBoundFrom f R N                     -- f : Real → Real, every interval past R
```

All three unfold to *"every duplicate-free list of points in the interval where a predicate holds is
at most `K` long"*. `ZeroCountOn p a b K` is that with the predicate abstract, and the identifications
are **definitional** — `uniformZeroBound_iff_zeroCountOn` and `uniformZeroBoundFrom_iff_zeroCountOn`
are both `Iff.rfl`.

#### What that buys, measured

| theorem | axioms |
|---|---|
| `ZeroCountOn.glue` | **6** — `Classical.choice`, `Real`, `ltR`, `lt_total`, `Quot.sound`, `propext` |
| `ZeroCountOn.glueList` | **6**, the same six |
| `piecesBounded_is_weaker_than_the_conclusion` | 12 (the extra six only to *name* `0`, `1`, `1+1`) |

Six. The gluing needs the **order** on `Real` and no arithmetic whatsoever — `lt_total` for the
trichotomy at the cut, and nothing else. That content had been sitting inside a `PfaffianFn`-typed
lemma where nothing else could reach it.

`EMLExplicitBoundGlue.BoundedZerosBy.glue` now cites the general lemma: **−42 lines, +3**. Generalised
beside the original and then the original deleted in the same commit, rather than leaving the
duplicate to be cleaned up later.

#### The `+ 1` per cut is not slack

A cut point lies in *neither* adjacent open interval, so a zero sitting exactly on it is invisible to
both pieces and must be paid for once per cut. Over `n` cuts: `(n + 1) * K + n`.

#### A vacuous draft, caught by writing the specimen

`glueList`'s first draft assumed `∀ u v, ZeroCountOn p u v K` — a bound on **every** interval, which
is `UniformZeroBound` itself. Its hypothesis therefore implied its conclusion and the theorem said
nothing, exactly the shape of
`feedback_a_theorem_can_be_vacuous_and_all_gates_pass`: it compiles, cites no bad axiom, and is
worthless.

The fix is `PiecesBounded p K a cuts b`, a recursion asking for a bound on **each named piece** and
on nothing else. And because a hypothesis being weaker is the whole point,
`piecesBounded_is_weaker_than_the_conclusion` exhibits the separation: the zero set of
`(x - 1)·(x - 2)` cut at `1` satisfies `PiecesBounded` at `K = 1` — `(0,1)` holds no zero, `(1,3)`
holds one — while `ZeroCountOn p 0 3 1` **fails**, because `(0,3)` holds two. Reinstating the draft's
hypothesis now fails to compile.

#### Where this is going

`OneQueryLevelSet` needs a bound on every interval for a germ whose defining tree changes at the
poles of its rational argument. Those poles are finitely many and depend on `P`, `Q` alone — not on
the interval — so they are the cut list, and `glueList` is what converts per-piece bounds into the
interval-independent one. That is the remaining half; `(ew)` closed the ray half.

## [Unreleased] — 2026-08-29 (ew)

### A uniform zero bound now yields the LIST — and one-query germs have finitely many zeros on a ray

New module `MachLib/EMLZeroListFromBound.lean`. Two bridges and a specimen, plus the composition
with `(ev)`'s antecedent.

#### The gap, measured before it was filled

`UniformZeroBound f N` says every interval holds at most `N` distinct zeros; every "the level set is
finite" statement in this corpus wants a `List Real` containing the zeros, because a `List` is how
this corpus spells finite. Nothing bridged the two. An **exhaustive** `grep -rn ': UniformZeroBound '`
across `MachLib/` — not a truncated one — finds exactly one theorem *concluding* the global form, and
it is a specimen: `uniformZeroBound_specimen` (`x - 1`, bound `1`). **No producer.**

I first wrote "no producer and no consumer either", and the same grep refutes the second half:
`eventually_nonzero_of_uniformZeroBound` and `uniformZeroBoundFrom_mono` (`EMLDeclampUniform`, a
module I did not know existed until the search printed it) both consume a bound. The search answered
*is anything concluded*; the sentence claimed *is anything used*. Two different questions, and the
one I ran was not the one I wrote down — the recurring shape behind
`absence_from_a_truncated_search_is_not_absence`, here with an untruncated search and a drifted
predicate instead.

#### What closed it

`nat_least_element` (`PolynomialCanonical`) is well-ordering in the form this corpus carries it. Take
the least `n` with **no** nodup zero list of length `n`; the bound makes `N + 1` such an `n`, and the
empty list makes `n ≠ 0`, so `n` has a predecessor whose witness list is **maximal**. A zero outside
it would cons on — `List.nodup_cons` wants exactly non-membership — and reach the impossible length.

```
zeroList_of_uniformZeroBoundFrom : UniformZeroBoundFrom f R N → ∃ E, ∀ x, R < x → f x = 0 → x ∈ E
zeroList_of_uniformZeroBound     : UniformZeroBound f N       → ∃ E, ∀ x,        f x = 0 → x ∈ E
```

**Footprint: 26 axioms, and not one of them is analysis.** No `rolle`, no `analytic_*`, no
`HasDerivAt`, no `exp`, no `log` — order, field and `Classical.choice`. Same virtue as
`eventually_nonzero_of_uniformZeroBound`: it cannot be wrong for chain-shape reasons, so it serves
any future zero-counting result.

`zeroList_specimen` instantiates it on the corpus's only `UniformZeroBound` and exhibits `1 ∈ E`.
Both halves are needed: without a satisfiable hypothesis the theorem is vacuous, and without a
*member* the produced `E` could be `[]` with the statement still typechecking.

#### The composition — the first FINITE statement about a level-1 germ

```
queryGerm_finite_zeros_on_ray :
  1 ≤ X → (∀ x ≥ X, pev Q x ≠ 0) → ¬ EvZeroF (bipev N · (Fbasis (pev P ·/ pev Q ·)))
    → ∃ R E, ∀ x, R < x → bipev N x (Fbasis (pev P x / pev Q x)) = 0 → x ∈ E
```

71 axioms — *identical count to `oneQueryDichotomy_holds`*, and the 26 above are a subset, so the
bridge costs nothing on top of the antecedent it consumes. Every previous level-1 result said
**eventually non-zero**; this one says **finitely many, here is the list**.

#### The adversarial pass on `OneQueryLevelSet`, and where the residue actually is

Before writing any of this I spent the hour trying to **refute** `OneQueryLevelSet` — a germ
identically `c` on a region with interior but not off a finite set. No counterexample. Any candidate
needs a non-trivial rational relation between `x` and `exp(S(x))` holding on an interval, with `S`
rational; that is false mathematically, and the corpus's transcendence inputs
(`BoundedGermTranscendence`, `FS_not_algebraic_of_*`) are all **tail**-shaped.

The residue is **narrower than the obvious guess**, and the reason is worth carrying:

| branch | evaluation agreement needs | analyticity needs |
|---|---|---|
| negative (`negGermTree`) | `pev Q x ≠ 0` **and** `S x ≤ 0` | `pev Q x ≠ 0` **only** |
| positive (`toEML (queryTerm …)`) | `pev Q x ≠ 0` and `0 < S x` | `pev Q x ≠ 0` and `0 < S x` |

Read off `negGermTree_logArgPos`, which takes only `hQ`, against `negGermTree_eval`, which takes both.
So on the negative branch an identity **does** cross a sign change of `S` — the tree is analytic
there — and `analytic_zero_on_subinterval_imp_zero` carries it to the whole pole-free component. The
sign changes are not the obstruction. **The poles are**: an identity established inside a *bounded*
component between two roots of `pev Q` has nowhere to propagate to, and the tail machinery never sees
it. That is the whole remaining gap, and it is one component-shape, not a general transcendence
question.

I had this wrong an hour earlier — I wrote that the sign change blocked propagation. It blocks the
*agreement*, not the *analyticity*, and only the second matters for the identity theorem.

## [Unreleased] — 2026-08-29 (ev)

### `OneQueryDichotomy` DISCHARGED — four distinct open obligations

`oneQueryDichotomy_holds` (`EMLCtxDivClamp`). The ledger reads **22 rows, 7 open rows, 4 distinct open
obligations** — down from six when the day began. No `sorryAx`, no `zero_count_bound_classical`;
footprint is the lane's analytic base (`rolle_ct`, `analytic_finite_zeros_compact`,
`analytic_ne_zero_nbhd`, `eml_tree_analytic_on_interval`) plus `div_zero`.

#### What closed it

The obligation omits two side conditions that `oneQueryDichotomy_divConditioned` carries.
`divClamp` supplies exactly those, and both halves are now proved:

* **value preserved** (`divClamp_eval`) — `a / 0 = 0` makes clamping a degenerate `div` to `const 0`
  an *equality*;
* **denominator non-vanishing** (`divClamp_denom_and_divDenomsOK`) — clamping swaps the divisor's
  *numerator* (zero) for `const 0`'s *denominator* `[[1]]`, and the surviving factors compose via
  `bipolyNoOscillation_holds`.

The second is proved as a **conjunction with `DivDenomsOK`**, because `ctxFrac_eval` — needed in the
`div` case to rule out a degenerate numerator — takes both as hypotheses; proving either alone would
be circular.

#### Measured: the clamp costs nothing

`#print axioms` on both capstones, diffed set-against-set:

```
oneQueryDichotomy_holds     71 axioms
bipolyNoOscillation_holds   71 axioms
capstone \ bipoly           EMPTY
bipoly \ capstone           EMPTY
```

**Identical footprints.** Every axiom the clamp needs — `div_zero` included — was already spent by
the composition lemma it rests on. The construction is free at the trust boundary, which is the
argument for preferring it to any route that would have introduced a new positivity or
non-vanishing axiom to dodge the degenerate `div`.

#### The refutation attempt is what supplied the mechanism

`(er)` tried to prove this obligation **unprovable**: `FCtx.eval` hits `divR _ 0`, `div_def` covers
only non-zero denominators, so `divR · 0` looked unconstrained and the statement independent of the
axioms. The grep run to *support* that argument turned up

```
MachLib/Basic.lean:149:   axiom div_zero (a : Real) : a / 0 = 0
```

and that axiom is now **load-bearing in the proof**. The adversarial hour did not merely fail; it
handed over the mechanism it was trying to exploit.

#### Totalisation, four times

`Fbasis 0 = 1` (zero branch), `Fbasis u = exp u` (negative branch), `a / 0 = 0` in the clamp, and
`a / 0 = 0` again in the value transfer. **Every time, the degenerate case turned out to be the easy
branch rather than an obstacle** — consistently the opposite of what I predicted going in. A totalised
operator does not merely avoid undefinedness; it collapses the hard case into a constant, and this
vein is now four independent data points for that.

#### Scope

`OneQueryLevelSet` is **not** discharged and does not follow: the ledger notes it reduces to
`q_F(sign) ≥ 2` *and not to* `OneQueryDichotomy`, and `EMLOneQueryGlobal` exists to keep the two
apart. Remaining: the `DecayFloor` cycle (frozen research programme), `TowerLowerBound` ⇄
`TowerReducesToSign`, `BoundedGermTranscendence`, `OneQueryLevelSet`.

## [Unreleased] — 2026-08-29 (et)

### Which hypothesis the witness breaks — and it is not the one `(es)` named

`(es)` closed by describing the corrected route as *"a div-clamp … then apply
`oneQueryDichotomy_divConditioned` to the clamped context, which then satisfies `DivDenomsOK`"*.

**`DivDenomsOK` was never the problem.** `divDegenerateCtx_divDenomsOK` proves it holds for the
witness outright.

The two remaining hypotheses are about **different polynomials**:

| hypothesis | what it constrains | in `hole + (1/0)` |
|---|---|---|
| `DivDenomsOK C x y` | at each `div` node, the **divisor's** `ctxFrac` *denominator* | `ctxFrac (const 0) = ([[0]], [[1]])`, denominator `1` — **holds** |
| `bipev (ctxFrac C).2 ≠ 0` | the **whole context's** denominator, a product over the entire tree | zeroed by the divisor's *numerator* — **fails** |

Conflating them is what made `(es)`'s one-line route description wrong: I reached for the hypothesis
with "denom" in its name rather than the one the counterexample actually violated, having just
proved the counterexample.

#### The route still stands, for the other hypothesis

Clamping a `div` node whose divisor is eventually zero to `const 0` changes the factor that node
contributes to the whole-context denominator from the divisor's **numerator** (zero) to `const 0`'s
**denominator** `[[1]]` (one). That removes the zero factor while `a / 0 = 0` preserves the value.

And the remaining factors then compose: by `bipolyNoOscillation_holds`, a bipev germ that is not
eventually zero is eventually **non**-zero, so a product of finitely many such is eventually non-zero.
That is the step that makes the clamped context's denominator non-vanishing on a ray, and it is
exactly what `(er)`'s theorem was for.

So: same construction, different hypothesis discharged, and one more reason to state which polynomial
a side condition is about rather than which word appears in its name.

## [Unreleased] — 2026-08-29 (es)

### The degenerate-denominator route is FALSE — refuted with a witness, not a corrected sentence

`(er)`'s adversarial pass ended by proposing a two-case split to close `OneQueryDichotomy`'s remaining
gap, the second case being: *denominator germ eventually zero → `a / 0 = 0` collapses the node → the
`EvZeroF` branch holds outright*.

**That case is false.** `MachLib/EMLCtxDegenerate.lean` (new) carries the witness.

```
C = hole + (1 / 0)
```

`ctxFrac (div a b) = (num_a · den_b, den_a · num_b)`, so dividing by something with numerator `0`
gives that node denominator `0`; `ctxFrac (add a b)` multiplies denominators, so **the whole
context's normal-form denominator is identically zero.** But `FCtx.eval (add a b) = eval a + eval b`
and `1 / 0 = 0`, so the context evaluates to the hole — take `y = Fbasis 0 = 1` and it is never zero.

`denom_evZero_does_not_imply_eval_evZero` proves exactly that, with `P = []`, `Q = [1]`.

**A degenerate denominator does not make the value degenerate**, because `add` keeps the live part
alive. The `ctxFrac` normal form discards information `FCtx.eval` retains.

#### The prediction I attached was also wrong, and differently

`(er)` predicted the cost would be in `div`/`mul` — *"where a germ can be eventually zero without
either operand being"*. The failure is in **`add`**, and it is not about germs multiplying to zero at
all: the normal form's denominator is a product over the *whole tree*, so one degenerate leaf zeroes
it, while the value only degenerates if that leaf sits on a multiplicative path to the root.

So the prediction was wrong about the location *and* the mechanism. Recorded because a plan whose
refutation lives only in prose gets re-attempted; one that lives as a `False`-producing witness does
not.

#### The corrected route

A **div-clamp**, exactly analogous to `declamp` for EML trees: replace each `div` node whose divisor
is degenerate on the ray by `const 0` — justified by the same `a / 0 = 0` — and apply
`oneQueryDichotomy_divConditioned` to the clamped context, which then satisfies `DivDenomsOK`.

`declamp`'s uniformity problem does **not** arise here: "eventually zero" is a ray property, so the
clamped context is fixed once the ray is far enough out rather than varying per interval. That is the
one respect in which this is easier than the EML analogue.

#### Gotcha, fourth time today

`obtain`/application on an `EvZeroF` existential yields an **unreduced** `(fun x => …) Y`, so `rw`
cannot match. Bind through a typed `have`. It is in `CLAUDE.md`; reading it is evidently not the same
as recognising its shape mid-proof.

## [Unreleased] — 2026-08-28 (ek)

### `absence_audit.py` — the class of claim nothing checked, and three false ones in `CLAUDE.md`

`CLAUDE.md` has said for weeks that the claim auditor *"is structurally blind to a claim about a
theorem that does not [exist] — including 'this obligation is still open'. `check_obligations.sh`
covers that one case."* **One case.** The general shape was checked by nothing:

* *"These order lemmas do NOT exist here: … `mul_lt_mul_of_pos_left` …"* — **it exists**
  (`WitnessResidualGrowthCompetitionNumeric`).
* *"`min` and `abs` do not exist."* — **both exist**, in `Basic.lean`, under `namespace MachLib.Real`,
  and are used (`abs` in `EMLFTranscendence`, `min` across `Applications/`). That entry then told the
  reader to hand-roll `two_bound_witness` instead.

**An unchecked absence claim is not merely stale; it costs work.** All three are corrected in place,
with what replaced them.

#### Why now

This session made **six** wrong claims about what the corpus contains, every one under-estimating it.
The split is the argument for the tool:

* **Two were duplicate definitions** — `depth_le_two_exp_bounded_or_grows`, `pevTerm`. The compiler
  caught both in seconds, and only because I had picked the name the corpus already used. A creative
  name would have shipped the twin silently.
* **Four were assertions of ABSENCE** — and nothing caught them. One surfaced only via a duplicate
  name I happened to choose identically; **twice they became recommendations against machinery built
  for exactly that purpose**.

The compiler catches duplication. Nothing caught "this isn't there."

#### What it does

Each registered claim carries a **search that could falsify it**; the audit re-runs it and fails when
it starts matching. `TEXT-GONE` if the prose was edited away, `NOW-FALSE` if the search now hits,
`UNAVAILABLE` (exit 2, never a pass) if a source cannot be read.

Four canaries including a control, and — the part that matters — **a firing specimen against a real
defect rather than a synthetic one**: run against the former `min`/`abs` line it reports
`NOW-FALSE — 2 hit(s), first: MachLib/Basic.lean:221:noncomputable def abs`. The gate is validated by
the bug it was built for.

Seeded with three claims re-verified at registration: the five surviving absent order lemmas, the
absent `set`/`linarith`/`ring` tactics, and **no `Complex` in `MachLib`** — that last one load-bearing,
since the Frontier G work is non-transportable *because* of it, and several "does not transport"
claims would need re-reading if a `Complex` type ever landed.

#### Scope, and the limit that does not go away

It checks **searches, not meanings**. A vague absence claim can be registered with a search too narrow
to falsify it, and no script fixes that. It cannot find absence claims nobody registered —
registration stays a human act, the same limit `claim_audit` has. And an absence claim can be true and
useless. This measures decay, not value.

#### Extended the same day: probes, and three more claims

A grep is the wrong instrument for *"this tactic does not exist"*. `^syntax "linarith"` proves nobody
**declared** it here; it does not prove it is **unavailable**, because a tactic can arrive from a
dependency. So the auditor gained a second check kind — a Lean snippet that must fail to compile —
and the tactic entry was upgraded from grep to probe.

Three claims added, each verified at registration rather than assumed:

* `by_contra` (`EMLHeightInterface`) — probe reports `unknown tactic` ✓
* `conv_lhs` (`RatLogDeriv`) — same ✓
* **no measure theory** (`ElementaryEMLErf`) — and this one had to be **narrowed before it could be
  registered.** The prose said *"measure **and integration** theory, which does not exist anywhere in
  MachLib"*, but `RiemannIntegralMonotone` (monotone integrands) and `GaussianIntegral` /
  `GaussianImproperIntegral` all exist — and `git log --diff-filter=A` says all three files landed on
  **2026-07-24**, the same day. So it was never stale; it was **imprecise from the day it was
  written**. Measure theory is the part genuinely absent, and is what the search now checks.

Two further guards, both fail-closed: a probe failing for the *wrong* reason is reported broken rather
than passing (a typo in a probe reads exactly like the absence it was meant to establish), and a claim
registered with **neither** a search nor a probe is `UNAVAILABLE` — an absence claim nothing can
refute is not checked, merely written down. Canary 5 pins that.

Registry: 6 claims, all passing.

#### Registry 6 → 8, and an asymmetry between the two check kinds

Triaging the corpus's other 41 *"there is no …"* sentences confirmed most are mathematical prose
(*"there is no positive arch"*, *"no third behaviour"*) rather than capability claims — but four were
not, and two are worth pinning:

* **`there is no #eval path at all`** (`EMLCertifiedSynthesis`) — the best kind of absence claim to
  register, because it is **safety-relevant**: it is the reason a numerical spot-check cannot inhabit
  `Meets` and be mistaken for a discharged obligation. 0 occurrences at registration; if one ever
  lands, that argument needs re-reading before the prose is re-worded.
* **`OfNat Real` for `0` and `1` only** (`SymmetricTriple`) — why numerals must be written `natCast N`,
  which is the corpus's single most repeated tactic gotcha.

**The two check kinds fail in opposite directions, and only one is safe.** A malformed *probe* is
caught — if the expected error does not appear it is reported broken, so it cannot pass by accident.
A malformed *search* is not:

* too **broad** → false `NOW-FALSE`: loud, annoying, self-correcting. This happened at registration —
  a `(?!Zero|One)` lookahead, unsupported by POSIX ERE, matched `instOfNatOne`.
* too **narrow** → matches nothing and passes **silently**, indistinguishable from the claim being
  true. **No automatic guard exists for this.**

The only defence is writing the search so it *would* have matched the thing before it was removed, and
checking that it does. Done here: the corrected pattern was run against synthetic `nat_lit 2` and
`nat_lit 64` lines and matches both while leaving `nat_lit 1` alone. That check is now the documented
expectation for every search entry, in the tool's header and in the entry's own note.

## [Unreleased] — 2026-08-28 (ej)

### The query germ as an `L_F` term, with an explicit zero bound on the positive branch

`(eh)` reduced `OneQueryDichotomy` to a ray-relative uniform zero bound for
`bipev N x (Fbasis (pev P x / pev Q x))`; `(ei)` gave such a bound for **any** `L_F` term with safe
divisions and positive `F`-arguments. What sat between them was the germ itself as an `FTerm`.
`MachLib/EMLQueryGermTerm.lean` (new, 11 theorems, 179 lines) builds it.

No new axioms — 243 pinned; footprint is `rolle_ct` + `analytic_finite_zeros_compact`, inherited from
the descent. No `sorryAx`, no `zero_count_bound_classical`.

`queryTerm_zero_bound`: on `Icc a b` where `pev Q ≠ 0` and `pev P / pev Q > 0`, the germ's zeros are
bounded by `encBound (toEML (queryTerm N P Q))` — **a `Nat` built from `N`, `P`, `Q` alone, with no
`a` or `b` in it.** The two hypotheses are exactly the two the germ's shape leaves, and
`ratGerm_eventual_sign` (`PevSignGerm`) supplies both on a ray for the positive branch.

#### A false claim I made and then had to disprove

The module docstring first read: *"one `div` and **one** `F`. So `fOcc (queryTerm N P Q) = 1` — it is
a one-query term in the sense `OneQueryLevelSet` uses."*

**That is wrong.** Horner writes `u` once per coefficient level, so `fOcc (queryTerm N P Q) =
N.length` — the degree, not one. The germ is one-query in the sense of **one distinct `F`-argument**,
which is a different statement, and `EMLOneQueryGlobal` exists precisely to stop that conflation:
*"Conflating the two is the error this file exists to make impossible."* I made it anyway, in prose,
one file away.

`queryTerm_fOcc` and `bipevTerm_fOcc` now pin the actual number so the claim cannot drift back. The
correction is recorded in the docstring rather than silently applied — a docstring that quietly
changes its arithmetic teaches nothing.

#### Duplication, caught twice, both times by the obvious name

`pevTerm`/`pevTerm_eval` already existed in `EMLRationalGerm`, with the identical Horner definition
and the identical justification. I wrote them again; Lean rejected the duplicate name in seconds.

That is the second duplication of the session, and **both were caught the same way — because I picked
the name the corpus had already picked.** A construction given its obvious name collides audibly; the
same construction under a creative name ships silently beside its twin and nothing notices. Worth
preferring the obvious name for that reason alone, quite apart from readability.

Six wrong claims-about-the-corpus now, every one under-estimating it. The two cheap ones were the
name collisions; the four expensive ones were assertions of absence that no tool checks.

#### Scope: the positive branch only

`ratGerm_eventual_sign` splits a rational germ three ways and this module handles one. Where `u < 0`
eventually, totalisation gives `Fbasis u = exp u`, killing the log level — no `LogArgPos` obligation,
but also no `FTree` route, which is `ExpRationalKhovanskii`'s territory. Where `u` is eventually zero
the germ collapses to a polynomial in `x`. Neither is attempted, and the module says so rather than
letting "the germ is handled" form.

## [Unreleased] — 2026-08-28 (ei)

### `LogArgPosOn` through the change of basis — the link between `L_F ⊆ EML` and the explicit bound

`EMLBasisEquivalence` proves `L_F ⊆ EML` (`toEML`, `toEML_eval`). `EMLZeroBoundAssembly` gives an
explicit, **interval-independent** zero bound for any EML tree (`encBound`, `encBound_bounds`).
**Nothing connected them**, because `encBound_bounds` wants `LogArgPosOn t (Icc a b)` and no result
said when `toEML T` has it. `MachLib/EMLBasisLogArgPos.lean` (new, 19 theorems, 308 lines) supplies it.

No new axioms — 243 pinned. Footprint: `rolle_ct` + `analytic_finite_zeros_compact` (inherited from
the Khovanskii descent, this lane's accepted analytic base), **no `sorryAx`, no
`zero_count_bound_classical`**.

#### The observation that made it mechanical

**At every generator the `LogArgPosOn` side condition is exactly the `eval` side condition already
carried.** `subTree_eval` needs `0 < a.eval x`; so does `LogArgPosOn (subTree a b)`. `mulTree_eval`
needs `1 < a.eval x`; so does `LogArgPosOn (mulTree a b)`. `mulPos_eval` needs both factors positive;
so does `LogArgPosOn (mulPos a b)`. **The positivity a generator needs to compute the right value is
the positivity it needs to keep its logs in range** — so nothing new had to be discovered about the
constructions, only stated.

The consequence is the useful half: **the `Gen` layer is unconditional.** `subGen`, `addGen`,
`mulGen`, `negGen` all shift through `domTree u = exp (1 − u)`, positive for a structural reason, so
their obligations discharge with no hypothesis on `u` or `v` — mirroring exactly why `EMLRingClosure`
could drop the positivity hypotheses from `+`, `−`, `×` in the first place.

So in

```lean
logArgPosOn_toEML (T) (S) (DivSafe on S) (FArgsPos T S) : LogArgPosOn (toEML T) S
```

**five of the seven constructors carry no positivity at all**; `div` consumes `DivSafe`, which
`toEML_eval` already required, and **only `F` consumes `FArgsPos`**. That is the honest answer to
"when can an `L_F` germ be fed to the encoder": when `F`'s arguments are positive, and the question
arises nowhere else.

#### The payoff

`fterm_encBound_bounds`: any `L_F` term with safe divisions and positive `F`-arguments on `Icc a b`,
plus a nonzero witness, has its zero count bounded by `encBound (toEML T)` — **a `Nat` built from the
term alone, with no `a` or `b` in it**. That is the `UniformZeroBoundFrom` shape that `(eh)`'s
`oneQueryDichotomy_of_uniformBoundsFrom` asks for.

#### Correcting `(eh)`: the EML route is the right one, and that was miss number five

`(eh)` recommended **against** routing the query germ through EML trees, on the grounds that
`addTree`/`mulTree` carry positivity conditions a bivariate polynomial cannot meet.

**That was wrong.** `EMLRingClosure` had already retired those conditions, and says so in its own
header — *"the positivity side conditions on `subTree`/`addTree`/`mulPos` were never about the
class"*. I read the conditional lemmas, did not read the `Gen` layer built to replace them, and
recommended against the route those generators exist to enable.

Five wrong claims-about-the-corpus in one session, every one under-estimating what it contains:
the depth-4 construction, the ray bookkeeping, the depth-≤2 dichotomy, gap 1, and now the `Gen`
layer. **Reading a conditional lemma is not reading the module** — the unconditional replacement sat
forty lines below, under a header that stated the whole point.

#### What is left

Exhibit `bipev N x (Fbasis (pev P x / pev Q x))` as an `FTerm` and discharge `FArgsPos` — i.e.
`pev P x / pev Q x > 0` on a ray. A ratio of polynomials has eventually constant sign, so it splits
three ways: `u > 0` eventually (this module applies directly); `u < 0` eventually (totalisation gives
`Fbasis u = exp u`, no log level, `ExpRationalKhovanskii`'s territory); `P ≡ 0` (`Fbasis 0 = 1`,
polynomial in `x`).

Survey, with all five misses scored:
`monogate-research/exploration/query_vein_survey_2026_08_28/INVENTORY.md`.

## [Unreleased] — 2026-08-28 (eh)

### The query vein, surveyed — its classical bottom is closed, and the antecedent now matches its producers

Three of the five open obligations live here. This entry is mostly an **inventory**, because the
survey found more than the work did: the vein is much further along than its docstrings say.

#### `OneQueryDichotomy` is one gap from done, and it is not a classical one

```
OneQueryDichotomy
  ⇐ oneQueryDichotomy_of_uniformBounds        (EMLZeroBoundRay)
  ⇐ a Khovanskii bound for the chain carrying  Fbasis x = exp x + log x
  ⇐ IsExpLogRecipW — recip arm, dispatch, recursion, base all proven
  ⇐ exp_step + log_step  ⇐  exp_hard + log_hard
```

**Both cores are proven** — `exp_hard_proof` (`PfaffianExpHard`, *"exp arm CLOSED"*) and
`log_hard_proof` — giving `eml_eval_boundedZeros_unconditional`. Footprint read directly rather than
off prose: `rolle_ct`, `analytic_finite_zeros_compact`, `analytic_ne_zero_nbhd`, `HasDerivAt` — **no
`sorryAx`, no `zero_count_bound_classical`**. That is this lane's accepted analytic base, not new debt.

**And the interval-uniformity is done too.** `combined_descent_3_explicit`
(`EMLExplicitBoundComposition`) + `enc_combinedBound` + `encBound` (`EMLZeroBoundAssembly`) give an
explicit **interval-independent** bound for any EML tree. That track exists because `∃K` per interval
*"is too weak for `sin/cos_not_in_eml`"* — built for a different consumer, and it happens to serve
this one exactly.

#### What this commit adds: the antecedent stated where it can be met

`bipolyNoOscillation_of_uniformBounds` demands a bound on **every** interval; its conclusion needs
only the ray-relative one, and `eventually_nonzero_of_uniformZeroBoundFrom` was already there.
`EMLZeroBoundRay`'s own note says demanding more *"quantifies past the use"* and *"makes the
remaining work look larger than it is"* — and here that is load-bearing rather than stylistic:
**every plausible producer goes through logs of `pev P x / pev Q x`, positive only past some `R`**,
and below `R` it has nothing to say, exactly as `SignHardUniformZeroBound` had nothing to say below
its own `X₀`.

* `bipolyNoOscillation_of_uniformBoundsFrom`
* `oneQueryDichotomy_of_uniformBoundsFrom`
* `oneQueryDichotomy_of_uniformBounds_via_ray` — the interval form as a **corollary**, so the two do
  not carry separate proofs.

No new axioms; footprints are base field axioms.

#### The single remaining gap, and the route not to take

Exhibit `bipev N x (Fbasis (pev P x / pev Q x))` as something the explicit descent accepts, on a ray.

**Not through EML trees.** The combinators exist (`polyTree`, `addTree`, `mulTree`, `expOf`,
`logTree`) but `addTree_eval` needs `0 < a.eval x` and `mulTree_eval` needs `1 < a.eval x ∧ 0 < b.eval x`.
A bivariate polynomial has coefficients of both signs, so that route means threading a positivity
certificate through every node — difficulty created entirely by the routing.

**Through the chain directly.** `combined_descent_3_explicit` takes a `PfaffianChain` and
`ChainTags`, **not** an EML tree; the encoder is one client, not the interface. The natural chain is
`1/Q` and `1/u` (recip), `exp u` and `log u` (exp, log), with `bipev N` lifted to a `MultiPoly 4`.
Every side condition is then about `P, Q` on a ray — where `Q ≠ 0` and `u > 0` are the antecedent's
own hypotheses.

#### `BoundedGermTranscendence`: hard, with evidence rather than reputation

`PevDeriv`: on the bounded branch `F ∘ S` is polynomially enveloped, *"so every instrument in this
corpus has a false hypothesis"* — the growth tools do not merely fail there, their hypotheses are
unsatisfiable. `BoundedGermEnvelope`: progress *"must come from somewhere other than growth"*. Both
unbounded rates are theorems and constant `S` is a counterexample, so the statement is correctly
narrowed and the missing instrument is real. **Do not start there.**

#### The session's running error, now four for four

Every structural prediction I made about this vein was wrong, always in the same direction —
**under-estimating what the corpus already contains**: the depth-4 construction (already general),
the ray bookkeeping (no friction), the depth-≤2 dichotomy (already present, found by Lean rejecting
a duplicate name), and now gap 1 (already done, in a track named for a different purpose). The
mathematics was sound each time; the *inventory* was wrong each time.

Survey with the full map: `monogate-research/exploration/query_vein_survey_2026_08_28/INVENTORY.md`.

## [Unreleased] — 2026-08-28 (eg)

### `d(x + c) = 4` for `c < 0` — §4's open cell closed, and the instrument was never missing

`EMLDepthTameness` §4 carried one open cell and a strong claim about it:

```
c > 0   d(x + c) = 4  exactly      c = 0   d(x) = 0      c < 0   d(x + c) ∈ {3, 4}
```

> *"Whether the negative gap is real or an artefact of the missing instrument is **open**, and it is
> the first question this family raises that the existing machinery cannot answer."*

**Both halves of that sentence were wrong.** `x_plus_neg_c_depth_exact_four` closes the cell, and the
existing machinery could answer it — the blocker was never an instrument, it was `(ef)`'s obligation.

**No new axioms — 243 pinned.** Footprints are base `Real` field axioms.

#### What actually closes it

The depth-3 exclusion splits on the left child's exponential, and both branches were already
available once `(ef)` landed:

* **bounded** → `mirrorBand_not_depth_three_bounded_left`, with `x_plus_neg_c_mirrorBand` supplying
  the target's super-logarithmicity (the only genuinely new lemma here, and it is four lines);
* **growing** → `negativeTranslationGrowingLeft_holds`, discharged this morning in `(ef)`.

The split is exhaustive by `depth_le_two_exp_bounded_or_grows`. The upper bound is
`eml_const_offset_closure` at `K = 1 − c`, general in `c` since it was written. **So the whole cell
is assembly**, and the `{3,4}` uncertainty was an artefact of one open obligation, not of missing
theory.

A note on the one new lemma: `C + log w < w + c` wants `C − c < w − log w`, and the clean way to get
it **strictly** without halving is to make `log w` do double duty — past `exp X₄`, `2 log w ≤ w` gives
`log w ≤ w − log w`; past `exp (C − c)`, `C − c < log w`. Chain them.

#### The error worth recording: absence read off a truncated grep

I wrote this section by first proving a depth-≤2 exponential dichotomy from scratch, having recorded
in the route note that *"there is no depth-≤2 counterpart in the corpus — I grepped"*.

**`depth_le_two_exp_bounded_or_grows` has been in `EMLDepthTameness` (line 3143) all along**, with a
docstring reading *"the brick a depth-3 band argument needs on its left child"* — written for exactly
this use.

The grep that "established" its absence ended in `| head -6`. The lemma was below the cut.

> **Absence read off a truncated search is not absence**, and the failure mode is that it is
> *invisible*: a short result list is indistinguishable from a short answer. Nothing in this repo
> would have caught it — not a gate, not the claim auditor, not re-reading the note. Lean caught it,
> with `has already been declared`, only because I had duplicated the name.

This was the **third** wrong prediction in that route note, and all three had one shape: **a claim
about what the corpus does not contain, made without exhaustively searching it.** The other two were
"the depth-4 construction may not carry to negative `c`" (already general) and "the friction will be
the ray bookkeeping" (none — the existing dichotomy's bounded disjunct already has the shape the
mirror-band interface wants, because it was written for it). The mathematics in the note was sound
throughout; the *inventory* was wrong three times.

#### Prose corrected where it had gone false

The §4 table, `x_plus_neg_c_not_depth_le_two`'s docstring, and `MirrorBand`'s *"Status: half proved"*
were all describing a state that no longer holds. All three are updated in place with what replaced
them, rather than silently rewritten — the table now records the closure and says explicitly that the
gap was **not** the missing instrument. This is the class of prose no gate can see: the claim auditor
pins claims about theorems that *exist*, and is structurally blind to a paragraph asserting something
is open.

**What stays asymmetric is the proof, not the value.** The positive side runs through
`IntermediateBand` with `x < f x`; the negative needs the mirror band, the dichotomy, and a whole
module for one branch. Equal answers, unequal arguments.

#### An unexercised theorem, now exercised — found by the ratchet turning the other way

`hypothesis_audit` reported `FIXED MirrorBand: now has a producer — remove it from the baseline`, and
that line says something worth reading twice: **until today nothing in the corpus produced a
`MirrorBand`.** `mirrorBand_not_depth_three_bounded_left` has been a *conditional theorem nobody had
instantiated* since it was written — the exact shape of the `positive_branch_impossible` failure,
where a green corpus says `True` rather than "the one you need".

It was not vacuous: `x_plus_neg_c_mirrorBand` now supplies an instance, so the hypothesis was
satisfiable all along. But that was **not known** before this commit, and no gate was asserting it.
The audit built for capstones-with-no-callers caught it from the premise side, which is what the
mirror harness exists for. Baseline 34 → 33.

Route, with all three predictions scored:
`monogate-research/exploration/x_plus_neg_c_depth_2026_08_28/ROUTE.md`.

## [Unreleased] — 2026-08-28 (ef)

### `NegativeTranslationGrowingLeft` is DISCHARGED — six distinct open obligations become five

`(ee)`, an hour earlier, reduced this obligation to `PinnedRightChild` and said the residue's proof
was *"one sentence; formalising it needs a two-sided bound on `exp (A₁ x)`, whose lower half costs"*.
It cost about what that predicted. **`negativeTranslationGrowingLeft_holds` closes it**, and the
ledger moves for the first time in the 2026-08 arc: **22 rows, 8 open rows, 5 distinct open
obligations**.

**No new axioms — 243 pinned.** Footprints of both capstones are base `Real` field axioms: no
`sorryAx`, no `rolle`, no `analytic_finite_zeros`.

#### The residue, and why the perturbation never mattered

Write `u x = exp x − x − c`. The equation forces `B x = exp (u x)`, so a depth-2 `B = eml A₁ B₁` needs

```
exp (A₁ x) = exp (u x) + log (B₁ x)
```

with `log (B₁ x)` bracketed between `−(e^{C₂} + log x)` and `x + C₁` — **at most linear either way,
against a target exponential in `u`.** One step of `exp` swallows it: both folds run on
`exp (u ± 1) = e^{±1}·exp u`, and after `self_le_exp` turns `exp u ≥ u` each reduces to a
linear-versus-exponential comparison. So `pinned_band` pins `A₁ x` to `u ± 1`.

Then the five depth-≤1 forms are exhausted, and **which half of the band kills each one is the whole
story**:

| form | killed by | why |
|---|---|---|
| `α` | lower | a constant cannot reach `u − 1 → ∞` |
| `x` | lower | would force `exp w ≤ 2w + c + 1` |
| `c′ − log x` | lower | `−log w ≤ 0`, so it is capped by `c′` |
| `exp x − d` | **upper** | would force `w ≤ d − c + 1` |
| `exp x − log x` | **upper** | would force `w + c − 1 ≤ log w`, against `2 log w ≤ w` |

**The two forms that reach the right size are exactly the two that die on the `−x` term** — which is
the sentence `(ee)` predicted would be the entire proof, and it was.

#### Where the sign of the translation is actually used

`c < 0` appears in **one place**: `u_pos`, to know `exp w − w − c > 0` so the equation can be inverted
through the totalised `log`. Nowhere else — not in the band, not in the five-form split.

That is a thin use, and it is worth stating plainly: **this proof does not explain the
positive/negative asymmetry of `d(x + c)`.** `EMLDepthTameness` §4's table stands as recorded
(`c > 0` gives exactly 4; `c < 0` gives `{3, 4}`); one more branch of it is now closed, and the
asymmetry itself is untouched.

#### Non-vacuity, shipped with the capstone

An impossibility theorem is worth what its hypotheses are *individually* satisfiable for. If no
depth-≤2 tree could satisfy `Hgrow`, the result would be true and would say nothing —
`positive_branch_impossible` all over again. `growingLeft_growth_hypothesis_satisfiable` rules it out:
`var` satisfies the growth condition on the nose, so the configuration space being emptied was not
empty for a trivial reason. What is ruled out is the **conjunction**.

#### Ledger and baseline, both directions

`NegativeTranslationGrowingLeft` and `PinnedRightChild` are both **discharged**; the row that was
`reduced` for one hour is now a closure, and the residue registered beside it closed with it.
`hypothesis_baseline.json` drops `PinnedRightChild` (35 → 34) — the audit's ratchet turns the other
way too: *"now has a producer — remove it from the baseline"*, and a prop that gained one must not
stay pinned as unproduced.

Worth noting what the ledger did across `(ee)` and `(ef)`: **open → reduced → discharged**, all three
states in one day, each one checked. The intermediate `reduced` was not bureaucracy — for the hour it
stood it was the only honest description, and the gate refused the alternative.

Route: `monogate-research/exploration/negative_translation_growing_left_2026_08_28/ROUTE.md`. Its
Step 4 prediction — *"the fallback is to bound `exp (A₁ x)` one side at a time and use only the upper
half, which kills forms `α`, `x` and `c′ − log x`, leaving the two `exp x − …` forms to be killed by
the lower half"* — had the two halves **the wrong way round**: it is the *lower* band that kills the
first three and the *upper* that kills the last two. The route's structure was right and its
orientation was not, which is the kind of error a written-first route makes visible instead of
absorbing.

## [Unreleased] — 2026-08-28 (ee)

### `NegativeTranslationGrowingLeft` reduced to one child and one equation — the enumeration was avoidable

The obligation's own docstring calls it *"the same species of difficulty as `ExpExpGapBelow` and
`BoundedCellApproach`, which took an arc each"*, and expects a twenty-five-cell enumeration against a
cancelling equation. **It does not need one.** `MachLib/EMLNegTranslation.lean` (new, in the
aggregator) proves everything except a residue that is strictly narrower than the parent: no `A`, no
growth hypothesis, one child, one equation.

**No new axioms — 243 pinned, unchanged.** Footprints of all seven new theorems are base `Real` field
axioms: no `sorryAx`, no `rolle`, no `analytic_finite_zeros`.

#### Why it collapses

`Hgrow` gives `exp (A x) ≥ exp x`, so `log (B x) = exp (A x) − x − c → ∞` and *both* sides of the node
sit near `exp x` and **cancel** to leave `x + c`. No growth-rate argument can separate them — which is
what the docstring is pointing at, and it is right as far as it goes. The way in is that the
cancellation is **too exact to survive the depth-1 classification**:

1. **§1, the one genuinely new lemma.** `depth_le_two_log_growth_on_ray` — `log (t x) ≤ exp x + K` on
   a ray. The *growth* mirror of the existing `depth_le_two_decay_on_ray`; together they bracket
   `log (t x)` for a depth-≤2 tree. It follows from `depth_le_two_growth_envelope` by folding the
   envelope's additive `M` into its own exponential, using `1 + 1 ≤ exp 1`.
2. **§2, the squeeze.** With §1, `exp (A x) = x + c + log (B x) ≤ exp x + x + c + K`, and
   `exp (x+1) = e·exp x` has room to spare — so `x ≤ A x ≤ x + 1` on a ray. The band is deliberately
   width `1`; the sharp `A x − x = O(x e^{−x})` is true and costs more for nothing.
3. **§3, the band admits only `var`.** Three constructor cases. A constant cannot stay above the
   identity. A node dies to `depth_le_one_exp_bounded_or_grows` on its *left grandchild*: bounded
   loses to `Hgrow` (the node is then `≤ Kb + C + log x`, logarithmic — the mechanism of
   `mirrorBand_not_depth_three_bounded_left`, reused one level down), and growing loses to the band
   (the node is then `≥ exp x − (x + C)`). **That dichotomy does the work an enumeration would.**
   Nothing is assumed about the right grandchild beyond its depth.

**So the enumeration was avoidable because the destination was constrained first** — `A` is collapsed
to a single form *before* any shape analysis, and twenty-five cells never appear.

Worth recording separately: **`c < 0` is not used anywhere in §1–§3.** The collapse of `A` is a fact
about the band, not about the sign of the translation, so the negative side's difficulty lives
entirely in the residue and not in the geometry that reaches it.

#### What is left, named and open

```lean
def PinnedRightChild : Prop :=
  ∀ c : Real, c < 0 → ∀ B : EMLTree, B.depth ≤ 2 →
    (∀ x : Real, 0 < x → log (B.eval x) = exp x - x - c) → False
```

`log (B x) = exp x − x − c` forces `B x = exp (exp x − x − c)`, so a depth-2 `B = eml A₁ B₁` needs
`A₁ x → exp x − x − c`. The depth-≤1 forms are `α`, `x`, `c′ − log x`, `exp x − d`, `exp x − log x`,
and **none carries a `−x` term** — producing one needs `log (b x) = x + c` for `b` of depth 0, and
neither `log (const)` nor `log x` is affine in `x`. That sentence is the remaining proof; formalising
it needs a two-sided bound on `exp (A₁ x)`, whose lower half costs, because it needs the decay bound
on `B₁` with its sign split.

#### The ledger: a reduction is not a discharge, and the gate said so first

`negativeTranslationGrowingLeft_of_pinned (h : PinnedRightChild) : NegativeTranslationGrowingLeft` is
written with a **binder**, per the standing rule — and that is exactly why
`obligation_ledger_check.py` immediately reported

```
STALE  NegativeTranslationGrowingLeft: marked open but discharged by negativeTranslationGrowingLeft_of_pinned
OBLIGATION-LEDGER FAIL — 1/21 row(s) do not match the corpus
```

**The gate was right.** Something *does* now conclude the obligation; what the `open` row failed to
say is that it concludes it *from an open residue*. That is precisely what the `reduced` status
encodes, and the row is now `reduced → PinnedRightChild` with `PinnedRightChild` opened beside it.

**The count is unchanged: 22 rows, 9 open rows, 6 distinct open obligations.** A reduction to an open
residue relocates a debt; it does not remove one, and a ledger that let this read as a discharge would
have converted an honest reduction into a false closure — the failure mode `(dj)` and `(eb)` were both
about. Here the mechanism worked in the intended direction, unprompted, within a minute of the
theorem compiling.

`tools/hypothesis_baseline.json` gains `PinnedRightChild` (34 → 35), and the audit's own triage note
says why it belongs: *"named open obligations — meant to be consumed and unproved; that is what
'open' means"*. The shape that note tells you to watch for is a new name there that is **not** an
obligation you deliberately opened. This one is, and it was opened in the same commit that consumes
it.

Route, with its predictions and their outcomes:
`monogate-research/exploration/negative_translation_growing_left_2026_08_28/ROUTE.md`. Two of its
three "how this could be wrong" items fired as predicted (ray arithmetic, the sign split); the one it
missed is that `set` does not exist in this corpus, so "pick one big point" became the shared
`exists_big` lemma instead of a local definition.

## [Unreleased] — 2026-08-28 (ed)

### The claim auditor computed the right identity and printed the wrong one

Found while verifying `(ec)` — by **reading a passing gate's output**, not by it failing. Same
discovery mode as the defect canary 14 exists for, and its note says so in as many words.

#### What was wrong

`tree_fingerprint()` is sound and has been since `(bx)`: HEAD, the porcelain, **and a content digest
of every dirty path**, taken before and after the run. Canary 14 pins that it sees *content* — three
trees with byte-identical porcelain must give three different digests.

Both binding messages then printed `fp.splitlines()[0]`, which is **HEAD alone**.

The fingerprint deliberately includes uncommitted content. HEAD deliberately does not. So every dirty
tree on one commit logged the *same twelve characters*, and two runs over materially different trees
were indistinguishable in the record. That is precisely what binding a verdict to a tree exists to
prevent — see `(bx)`'s own framing, *"a gate certifies a repository state, not a work session"*.

**The `STALE` branch was worse.** It printed HEAD for *both* sides. The commonest staleness case is
an edit to an already-dirty file, which does not move HEAD — so the gate announced *"the worktree
changed while the audit ran"* directly above two identical lines. A reader would sooner conclude the
gate was broken than that they had edited during the run.

**Scope, stated rather than implied: no verdict was ever wrong.** The `before != after` comparison
uses the whole fingerprint and always did. What was wrong was the *record of what had been
certified* — a reporting defect in a gate whose entire job is establishing what it certified, which
is why it is worth a fix rather than a footnote.

#### The fix

`fingerprint_id(fp)` digests the **whole** fingerprint to twelve characters. Both messages now print
`tree <id> (HEAD <head12>)` — the id identifies, HEAD stays for orientation. `STALE` additionally
says when HEAD did not move, so the reader is told the change was uncommitted instead of being left
to infer it from two hashes that look the same.

#### Canary 16, and it fires

Two fingerprints sharing a HEAD and differing only below it — the exact shape of a mid-run edit. The
canary asserts the *old* label is identical across them (or the specimen does not reproduce the
defect and proves nothing) and the new one is not.

Verified against a **reverted copy** before being trusted: with `fingerprint_id` restored to
`fp.splitlines()[0][:12]`, both specimens return `4957a7e6d278` and canary 16 rejects it. A canary
that has never been seen to fail is a comment.

**The lesson, which is the transferable part: canary 14 tested DETECTION, and nothing tested the
MESSAGE.** A gate can compute the right thing and report the wrong one, and the reporting path is
exactly where that failure is invisible — the check passes, the output looks like an identity, and
the error only shows up when someone tries to *use* the record. Every gate that prints an identity,
a count, or a fingerprint needs a specimen for the printing, not only for the computing.

#### What it prints now

The first real run after the fix, on a dirty tree:

```
[self-test] canary 16 fires: two trees sharing a HEAD printed the SAME old label
            (4957a7e6d278) and print DIFFERENT ids now (94ad9ab6d30d, 8c09125c2681). ✓
CLAIM-AUDIT PASS — all 482 claims resolve against #print axioms.
[tree-binding] verdict bound to tree d4b50ba222f4 (HEAD 6d2bec17c571, worktree unchanged …)
```

**`d4b50ba222f4` is not `6d2bec17c571`**, and that gap is the whole defect made visible: the tree
carries uncommitted work, so its identity is not its commit's. Under the old scheme this run and
every other run on `6d2bec17` — including the one that certified `(ec)` against a *different* set of
uncommitted files — logged the same twelve characters.


## [Unreleased] — 2026-08-27 (ec)

### Depth was never the parameter, and the reduction to `LeadingMonomialFloor` was lossy

Two unrelated things, both found by taking a measurement seriously: a new module that sharpens the
decay programme's central bound, and a theorem count in `CLAUDE.md` that nobody can reproduce.

#### Where the question came from, since the Lean does not say

Frontier G — the complex-analysis frontier, opened the same day — measured the branch-point locus of
EML trees over `ℂ`. Findings 1–6 were all one tree, so the obvious next probe was whether they
generalise. **They do not**, and the way they fail names a parameter.

The branch points of a node's `log` are the zeros of its right child, one equation per inner sheet,
so the locus is a question about right children. Measured by keyhole winding count, there are at
least four regimes — empty (`exp z` on sheet `0`: an exponential never vanishes), finite (`1 − Log z`
on sheet `0`: one point, forever), comb (`exp z − Log z`: `R/π + O(1)`), and exponential
(`exp(exp z − Log z) − Log z`: `d(log N)/dR = 0.935`, confirmed by an independent root count) — and
**the regime can change from sheet to sheet within one tree**.

What selects the regime is **exponential height**, not depth. The discriminator is two pairs of
*equal depth*: at depth 1, `1 − Log z` (height 0) has `N(R) ≡ 1` out to `R = 53.4` while
`exp z − Log z` (height 1) has `4, 6, 8, 12, 18`; at depth 2, `e/z − Log z` (height 0) has `N ≡ 1`
while `exp(exp z − Log z) − Log z` (height 2) has `6, 14, 38`. Artifacts and failure record:
`monogate-research/exploration/Frontier_G_monodromy_2026_08_27/` (Findings 7–8).

**None of that transports.** `MachLib.Real` has no `Complex`. What transported was which statement
was worth proving.

#### `EMLHeightVsDepth` — twelve theorems, no new axioms

`EMLHeightInterface` proves `eh_le_depth` and its docstring calls `eh_sub` *"the axiom the whole
reframing turns on, and the one no tree measure satisfies"*. `EMLLadderMeasure` proves no `Nat`-valued
measure descending strictly to both children carries the induction. Neither file said what happens
jointly. Syntactic exponential height

    ehTree (eml A B) = Nat.max (ehTree A + 1) (ehTree B)

reads the `HeightModel` closure axioms off the tree, and `eh_le_ehTree` bounds **every** model by it.

**(1) The old reduction was lossy.** `decayFloor_of_heightModel` spends `eh_le_depth` and concludes
`DecayFloor`, which quantifies over `depth ≤ j`. But `LeadingMonomialFloor` constrains *height*, so
it was always giving a floor for every tree of height `≤ j` and the depth-indexed conclusion threw
the rest away. `decayFloorByHeight_of_heightModel` takes the **same hypothesis** and draws a
**strictly larger** conclusion — one lemma swapped. `decayFloor_of_decayFloorByHeight` recovers the
original, so nothing is lost. The gain is exhibited, not assumed: right spines of any length have
height 1, so at level 1 the height index already covers a family the depth index never reaches
(`height_index_covers_more`, `ehTree_lt_depth_witness` — depth 3, height 1). It buys **coverage and
not a shorter tower**: `LeadingMonomialFloor` gives one `m` per level with no monotonicity, and the
docstring says so rather than implying otherwise.

**(2) Height fails `right_le`, on the same side the germ route fails.** It satisfies `left_le` by one,
always. Going right the gap is **exactly zero**, not merely too small — `eml var (eml var var)` has a
right child of height 1 and node height `max(0+1, 1) = 1` — so `no_ladderMeasure_with_ehTree` rules
it out for *any* positive step. `tower_height_does_not_descend_right` (`EMLLadderMeasure`) reaches
the identical obstruction analytically, by building a node non-positive on `[1,∞)` whose right child
is an arbitrarily tall tower. The two share no machinery: `Nat.max` arithmetic on one side, towers on
the other. **One obstruction, two routes, one side.**

**(3) `ehTree` itself overcounts, and the witness is machine-checked.**
`ehTree_overcounts_witness`: `eml (eml (const 0) var) var` has height 2 but evaluates on `x > 0` to
`e/x − log x`, whose true height is 0. The `exp` is applied to `1 − log x`, which does not grow, so
it buys no level; the slack sits in `eh_exp`, whose `≤` is strict exactly there. So the chain
`eh ≤ ehTree ≤ depth` has slack at **both** steps, and closing the first needs `eh` of a quotient,
which `HeightModel` does not axiomatise — a limit of the interface, not of the tree.

Non-vacuity ships with the capstone, per the `positive_branch_impossible` lesson: `depth_ne_ehTree`
instantiates `no_ladderMeasure_with_ehTree` at `depthMeasure`, so the theorem demonstrably rules
something out rather than holding for want of a subject.

**What this is not.** It does not move the ledger — still **6 distinct open obligations, 9 open rows,
243 axioms pinned**. It does not touch `LeadingMonomialFloor`, which is where
`decayFloor_of_heightModel` is actually stuck: lemma (1) was always free and lemma (2) is the whole
problem. It sharpens a bound and explains an obstruction. Neither is progress on the obligation, and
the ledger correctly refuses to move.

#### `CLAUDE.md` carried a theorem count nobody can reproduce — for the second time

The file said **8 231 theorems**. No method reproduces it. The correct figure, by the command now
written into the file, is **7 347**:

```bash
find MachLib -name '*.lean' -not -path '*/Discovered/*' -exec grep -hcE '^ *theorem ' {} + \
  | paste -sd+ | bc      # 7 347   (all files: 8 096 — the 749 difference IS Discovered/)
```

That 749 is the cross-derivation: the commit that last set the count recorded "749 more in
`Discovered/`" independently, and it matches exactly, which is what says the method is right rather
than merely different.

**The cause, reproduced live.** `find … -not -path '*/Discovered/*'` **unquoted** lets the shell
expand the glob first, so `-not -path` excludes one matched file and every *other* match becomes an
extra search root — the same files are walked twice. Measured: quoted **7 347**, unquoted **8 839**.
It fails *upward*, which is why it reads as a healthy corpus and survived a review. `8 231` exceeds
`8 097`, the largest count the repo can produce from any file set outside `.lake`, so it was
detectable from inside the document all along.

Both the corrected figure with its command and the glob gotcha are now in `CLAUDE.md`. The lesson for
the Counts policy: **"re-derive it" is not enough if the derivation is a one-liner with a quoting
trap. Write the exact command, and sanity-check any "excluding X" figure against the all-files
total** — an exclusion that exceeds the total is impossible, and that check costs nothing.

Also corrected: 1 056 → **1 057** files, 750/1056 → **751/1057** reachable, 753 → **754** build jobs.

## [Unreleased] — 2026-08-27 (eb)

### The claim auditor's REDUCED rule silently stopped applying — to the rows a cycle keeps open

Sweeping the other tools for `(ea)`'s parser pattern (*"audit every gate's scope, not just the one
you suspect"*) turned up a second `rsplit(":", 1)` in `claim_audit.py`. Chasing it found something
worse than a parse bug.

#### The rule, and why it was not firing

`reduction_state_problems` requires that **an `↔` conclusion mentioning a live obligation must
declare `epistemic_type: "REDUCED"`** — otherwise a reduction is indistinguishable in the registry
from a closure. It asks `open_obligations()` which rows are live, and that read the CHANGELOG mirror
for rows marked `**open**`.

**`DecayFloor`, `GrowthEnvelope` and `EmlGermApproach` are marked `**reduced**`.** They are in a
reduction **cycle** — each reduces to another member, so nothing is reduced away and all three are
open. A `status == "open"` test does not see them.

So from `(dj)` onward, an equivalence on any of those three no longer required `REDUCED` — and **two
such claims were registered without it**, both mine: `decayFloor_iff_growthEnvelope` and
`emlGermApproach_iff_decayFloor`. Registering an equivalence between two open obligations as an
ordinary claim is precisely what the `REDUCED` state exists to prevent.

The docstring of the function that broke says *"a check that silently stops applying is worse than no
check"*, and names staleness as the risk it was guarding against. It stopped applying for a different
reason: **a status change that does not mean closed.**

#### The fix, and where it comes from

`open_obligations()` now imports `parse_rows` and `reduction_cycles` from `obligation_ledger_check`
and takes open rows **∪** cycle members. Imported rather than reimplemented, so the two tools cannot
disagree about which obligations are open — which is the duplicated-state failure one level up, and
the reason this happened at all: **two tools answered "which rows are open" from the same table, and
only one of them was taught about cycles.** If the walk is unavailable it warns on stderr rather than
quietly returning the narrow set.

Both claims are now `REDUCED` with a `reduces_to` the theorem's statement actually contains.

#### On the `rsplit` that led here

`claim_audit.py:671` uses `stmt_h.rsplit(":", 1)[-1]` for the `↔` test — the same non-top-level split
`(ea)` fixed in the ledger gate, and a second, sloppier extraction sitting a few hundred lines from
that file's own carefully depth-tracked `conclusion_of`. **It is left alone deliberately**: with the
`open_obligations` fix the check now fires on the cases that matter, and changing a second extractor
in the same commit would make the verdict diff unreadable. Recorded here so it is not lost —
a bracketed colon *after* an `↔` would still hide it.

**Ledger unchanged: 21 rows / 9 open rows / 6 distinct open.** No Lean changed. Two registry entries
corrected and one check restored to the scope it always claimed.

Gates, every figure read off the gate that produced it: build **753 jobs**, aggregator 750 of 1056,
consistency PASS, claims 478, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36,
hypothesis audit 34.

The first claim-audit run for this entry came back **STALE, exit 1** — its tree-binding noticed the
worktree changed mid-run, because this entry was being written while it went. The gate was right and
the verdict was discarded; the figure above is from a re-run on a quiescent tree. `(dj)` recorded the
same thing happening for the same reason. **Do not read a PASS line without its exit code**, and do
not edit the tree while the auditor is running — the second half of that lesson evidently needed
saying twice.

## [Unreleased] — 2026-08-27 (ea)

### The mirror harness — and it immediately found a parser bug in a shipped gate

`(dz)` found `ValueGapBound` had consumers and no producers, and noted the corpus has a harness for
the *opposite* direction only: `witness_audit.py` watches capstones nobody instantiates; nothing
watched hypotheses nobody satisfies. New measurement harness `tools/hypothesis_audit.py`, built to
the same design — pinned **set**, not count, so the ratchet turns one way.

> A Prop with consumers and no producers is not exercised; it is **assumed**. That is the easy half
> to miss, precisely because the consumers make it look exercised.

**It fires on the real defect, not a synthetic one.** Removing `valueGapBound_zero` from the
declaration set makes `ValueGapBound` reappear, consumed by `nodeDecayBound_of_valueGap` and
`decayFloorUpTo_four_of_valueGap`; putting it back silences it. That is the historical state this was
built for, reproduced exactly.

Four canaries, all synthetic so none can go stale: consumed-never-produced **fires**; adding a
producer **silences**; a Prop with *neither* consumer nor producer stays silent (nothing rests on it —
that is the aggregator's job, not this one's); and an `↔` is **not** a producer, the same rule as the
ledger's canary 9 and for the same reason.

Like `witness_audit` and `closerate`, this is a **measurement harness, not an eighth CI gate**. The
gate set stays at seven.

#### The parser bug it found on its first real run

The audit reported `PIrred` as never produced. `CLAUDE.md` says `pIrred_X` is the corpus's first
`PIrred` construction, and it is — in a *top-level* file, so it was scanned. The fault was in
`obligation_ledger_check.dischargers_of`, which the new tool imports:

```lean
theorem pIrred_X : PIrred ([0, 1] : List Real)
```

Its comment claims the conclusion is "the tail after the last **top-level** `:`". The implementation
was `rsplit(":", 1)`, which is **not top-level aware** — it split at the *type ascription's* colon and
returned `List Real)`, so the corpus's only `PIrred` construction was invisible to a shipped gate.

Fixed by `conclusion_of`, which takes the tail after the **first colon at bracket depth 0**. First,
not last: binders are always bracketed, so the separator is the first unbracketed colon — and a
`∀ x : T,` *inside* a conclusion then cannot be mistaken for it either, which `rsplit` also got wrong.

**The ledger gate's verdicts are byte-identical before and after** — all 21 rows, all 18 canaries —
so this is a latent defect removed, not a behaviour change. It was latent because no ledger row's
discharger happened to contain a bracketed colon. **A gate can be correct on every case it has ever
seen and still have the wrong parser**; what surfaced it was a second tool asking a different question
of the same code.

Baseline: **34 consumed-but-unproduced props**, triaged in the file. Most are correct — named open
obligations (which are *meant* to be here) and definitional predicates like `Lipschitz`, `MonotoneOn`,
`Rounds`, supplied from outside rather than proved. The signal is weaker than `witness_audit`'s and
the baseline says so. What to watch for is the shape `ValueGapBound` had: **a new name that is neither
an obligation you deliberately opened nor a predicate.**

**No Lean changed.** Ledger unchanged: 21 rows / 9 open rows / 6 distinct open.

## [Unreleased] — 2026-08-27 (dz)

### `ValueGapBound` had no specimen — self-audit, and the specimen

An audit of the Props introduced across `(dk)`–`(dy)`, asking of each whether **anything satisfies
it**, found one that nothing does:

```
LadderMeasure          depthMeasure, sizeMeasure          ✓
HeightModel            zeroModel                          ✓ (and its floor property REFUTED for it)
EmlGermApproach        two theorems conclude it           ✓
NodeDecayBound         nodeDecayBound_two                 ✓
LowerEnvBound          lowerEnvBound_two, …_three         ✓
ExpUpperBound          expUpperBound_three                ✓
ValueGapBound          — nothing —                        ✗
LadderInputs           — nothing, correctly: it IS the open thing (ladderInputs_at_two shows the shape)
```

`ValueGapBound` was introduced in `(dw)` §2 and consumed as a hypothesis by
`nodeDecayBound_of_valueGap` and `decayFloorUpTo_four_of_valueGap`. **Nothing satisfied it, at any
depth.** By this corpus's own rule that made both of those unvalidated.

> The `positive_branch_impossible` tell-tale was *"no caller and no specimen"*. This had **callers but
> no specimen** — half the signal, and the half that is easy to miss, because the callers make it look
> exercised. A Prop with consumers and no producers is not exercised; it is assumed.

#### The specimen

`valueGapBound_zero : ValueGapBound 0 0`, at the leaves, with all four shape pairings:

* `const a` / `const b` — the gap is a **fixed** positive constant, so `C = −log (gap)` serves. The
  `b ≥ exp (exp a)` branch is vacuous and the case split must happen **before** `C` is chosen, since
  `C` is committed outside the `∀ x`.
* `const a` / `var` — the guard `x < exp (exp a)` is eventually false; push the ray past
  `exp (exp (exp a))`.
* `var` / `const b` — `exp (exp x)` outruns `b`; `C = 0` and one rung of ray.
* `var` / `var` — `exp (exp x) ≥ x + 1` on the ray, from `exp x > 2x`.

**Two of the four are vacuous by ray, and that is stated rather than hidden.** A specimen whose
branches are mostly empty is weak evidence — this is the weakest form that still counts. What it
rules out is the failure mode where `ValueGapBound j m` is unsatisfiable for *every* `j`, which would
have made all of `(dw)`'s §3–§4 an elaborate way of assuming `False`.

#### What the audit does not cover

It asks "does anything conclude this Prop", which is a *syntactic* question. It cannot see vacuity in
the other direction — a Prop that is satisfiable but whose *hypotheses* are unsatisfiable at the
instances that matter. That is the `positive_branch_impossible` failure exactly, and the only defence
remains a specimen discharging every hypothesis at a concrete point. `valueGapBound_zero` does that
for the leaf case and for nothing above it.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`. Ledger unchanged: 21 rows / 9 open rows / 6 distinct
open.

Gates, every figure read off the gate that produced it: build **753 jobs**, aggregator 750 of 1056,
consistency PASS, claims 478, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dy)

### The capstone: the ladder machinery reaches `DecayFloor` itself — and why depth 4 is different in kind

```
LadderInputs                :  ∀ j, ∃ m, NodeDecayBound j m ∧ LowerEnvBound j m
decayFloor_of_ladderInputs  :  LadderInputs → DecayFloor          ← PROVED
```

Six entries of rungs and steps add up to this: **the whole obligation reduces to the per-depth
inputs, and nothing else is missing.** The step, the base case, the tower arithmetic, the transfer,
the leaf cases — all of it composes by induction on the depth bound into `DecayFloor` itself. No
`evSign_all` anywhere, so the obligation would arrive **footprint-clean** if the inputs did.

It discharges nothing, and it is still worth having explicitly: it converts *"we proved some rungs"*
into *"here is exactly what all the rungs need, uniformly"*, which is the difference between a ladder
and a pile of steps. `ladderInputs_at_two` checks the shape is satisfiable — `Depth3DecayExp` plus
`depth_le_two_lower_on_ray`, which is why depth 3 landed.

#### Deliberately NOT registered as a ledger reduction

`LadderInputs → DecayFloor` is proved; the converse is not, and it hits the same wall as `(dx)`:
`NodeDecayBound`'s positivity hypotheses are **pointwise**, `DecayFloor`'s are **eventual**. So
`LadderInputs` may be *strictly stronger*, and reducing `DecayFloor` to a strictly stronger residue
would read in the open column as progress while being the opposite. **The ledger stays at 21 rows / 9
open rows / 6 distinct open.**

#### Why depth 4 is different in kind — and it is not `(di)`

`(du)` corrected the `(di)` reading: the re-embedding does not bite until depth 8. The real obstacle
is elsewhere, and reading `boundedEmlCellApproachLarge_holds` — the last depth-≤2 cell to fall —
shows it.

`Depth3DecayExp` was proved by a cell enumeration that bottoms out in `depth_le_one_classification`:
the depth-≤1 germs are a short list of closed forms, and the router dispatches over them, splitting
`Q` on structure, then a left dichotomy on whether `exp (P x)` is bounded, then a right dichotomy
leaving `P` and `R` each `const` or `c − log x`.

The depth-4 analogue needs that same enumeration bottoming out at **depth ≤ 2**, where the normal form
is `exp a − log b` with `a`, `b` themselves depth-1 forms — roughly `27 × 27` shape pairings *before*
parameter regimes.

> That is precisely the scale `FRONTIER_BRIEF_3` §4 Q2 measured and called a trap, and its objection —
> **the cost is in the parameter regimes, not the shape count** — applies here with more force, not
> less. **Depth 3 was reachable because someone had already paid that cost one level down.** Nobody
> has paid it at depth 2, and the ladder does not make it cheaper; it makes it the *only* thing left.

So the recommendation, stated plainly rather than left implicit: **do not start the depth-2 cell
enumeration.** It is the one route the arc has already measured and rejected, and the machinery built
over `(du)`–`(dy)` does not change that measurement — it just means a single grind now buys the whole
next rung instead of part of it. Whether that is worth it is a judgement about the value of one more
bounded rung, and bounded rungs do not move the ledger.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **753 jobs**, aggregator 750 of 1056,
consistency PASS, claims 477, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dx)

### The transfer runs both ways — `(dw)` factored nothing, it renamed something usefully

`(dw)` called §3 a factoring. That word says the value-level statement is *easier* than the
node-level one. **It is not obviously so**, and the same substitution shows why for free:

```
value_gap_le_node_mul  :  exp u − q         ≤  (u − log q) * exp u     -- value ⟹ node
node_mul_le_value_gap  :  q * (u − log q)   ≤  exp u − q               -- node ⟹ value
```

The pair brackets the gap between the factors `q` and `exp u` (`value_gap_brackets`). So a node floor
gives a value floor and vice versa, **provided the other factor is bounded** — `exp u ≤ …` one way,
which is `ExpUpperBound` and `(dw)` §4 proves it; `q ≥ …` the other way, which is **a `DecayFloor`
for `B`**, and at depth ≤ 3 that is `decayFloorUpTo_three`, already in hand.

#### Why the converse still does not close, and it is the same distinction as `(dt)`

> `decayFloorUpTo_three` is an **eventual** statement — it needs `B` positive on a **ray**.
> `ValueGapBound`'s `0 < B.eval x` is **pointwise**, inside the `∀ x`. From positivity at one point no
> ray follows, so the converse does not go through as stated.

That is exactly the pointwise/eventual distinction that made `(dt)` work, cutting the other way. The
pointwise form was worth it there — it keeps `evSign_all` and the analytic block out of the **entire**
ladder — and it is worth it here. The price is that §3 cannot be *proved* a genuine reduction, only
observed not to be obviously one.

**So the honest claim is the one about shape.** `ValueGapBound 3 7` is stated where `ExpExpGapBelow`
and the `…CellApproach` family are stated — where the depth-≤2 answers live, and where a depth-≤3
answer would be found. `(dw)` said that too, alongside a word that claimed more. The word is now
qualified in place.

`le_exp_sub_one` is worth noting on its own: `d ≤ exp d − 1` for **every** `d`, no sign hypothesis,
straight from `log_le_sub_one` at `exp d` — where `exp_gt_one_plus_self` would demand `0 < d`. The
corpus's tangent axiom is one-sided; `log_le_sub_one` is not, and the two are the same fact.

**Nothing was reduced, nothing was discharged, and the ledger does not move: 21 rows / 9 open rows /
6 distinct open.** This is a correction plus two lemmas.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **753 jobs**, aggregator 750 of 1056,
consistency PASS, claims 474, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dw)

### The convexity transfer, once, at every depth — depth 4 down to one value-level residue

New module `MachLib/EMLValueGap`. `(dv)` left depth 4 resting on `NodeDecayBound 3 3`. This factors
*that*, the way `(du)` factored the rung.

> **⚠ QUALIFIED by `(dx)` — "factors" claims too much.** The transfer runs **both ways**
> (`node_mul_le_value_gap`), so a node floor gives a value floor and vice versa, provided the other
> factor is bounded. §3 buys **vocabulary, not difficulty**. The claim that survives is the one about
> shape, below.

```
nodeDecayBound_of_valueGap        : ValueGapBound j m → ExpUpperBound j m → NodeDecayBound j (m+1)
expUpperBound_three               : ExpUpperBound 3 7                              ← PROVED
decayFloorUpTo_four_of_valueGap   : ValueGapBound 3 7 → DecayFloorUpTo 4           ← PROVED
```

#### Value level is the vocabulary the corpus already proves things in

`exp (A x) − log (B x) > 0` is exactly `B x < exp (exp (A x))`, so the node's positivity is a
*value-level* statement about `B` staying under `exp ∘ exp ∘ A`. Every discharged piece of
`Depth3DecayExp` — `ExpExpGapBelow`, `BoundedCellApproach`, `BoundedEmlCellApproach`,
`BoundedEmlCellApproachLarge` — is written at that level. `(dv)` searched the discharged column and
found them at the wrong depth; this puts depth 4's residue in the same *shape*, which is the half of
that search that was reusable.

#### The transfer, and the substitution that makes it division-free

The relation wanted is `E − q ≤ node · E` with `E = exp (exp (A x))`, `q = B x` — the corpus calls it
"reverse convexity" inside `depth_three_decayExp_var_left_of_gap`, stated there only for `A = var`.

The clean derivation is not the one that stares at `E`. Put `d = node = u − log q` with
`u = exp (A x)`; then `q · exp d = exp u = E` and the whole claim collapses to

```
exp_sub_one_le_mul :  exp d − 1 ≤ d · exp d
```

which follows from `log_le_sub_one` at `exp (−d)`: `−d ≤ exp (−d) − 1`, hence
`(1 − d) · exp d ≤ exp (−d) · exp d = 1`. **No division anywhere** — which matters in a base that has
`/` but almost no lemmas about it, and which the `E`-first derivation cannot avoid.

#### The growth input is assembly too

`depth_le_three_growth_envelope` gives `A x ≤ exp (exp (exp x + K) + M) + N`, and four applications of
`const_add_tower_le_succ` — one per additive constant, one per `exp` — climb it to `towerFn 6 x`, with
one more `exp` bounding `exp (A x)` by `towerFn 7 x`.

The height `7` is **not sharp and does not need to be**: `ValueGapBound j m` gets *weaker* as `m`
grows, so asking for it at `7` asks for less than at `3`. That asymmetry is worth noticing — the loose
arithmetic makes the residue easier, not harder, so there is no reason to tighten it.

#### The state of the ladder

```
depth ≤ 2   decayFloor_upTo_two               height 0   proved
depth ≤ 3   decayFloorUpTo_three              height 2   proved
depth ≤ 4   decayFloorUpTo_four_of_valueGap   height 8   ONE input: ValueGapBound 3 7
```

Proved and no longer part of the debt: the ladder step, the lower envelope, the growth bound, the
convexity transfer. **What is left is one value-level approach statement at depth ≤ 3** — the same
question `ExpExpGapBelow` and the `…CellApproach` family answered at depth ≤ 2.

Its hypotheses stay **pointwise** throughout, which is what keeps the whole ladder free of
`evSign_all` and the analytic block.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`. `DecayFloor` untouched; ledger unchanged at 21 rows /
9 open rows / 6 distinct open.

Gates, every figure read off the gate that produced it: build **753 jobs**, aggregator 750 of 1056,
consistency PASS, claims 471, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dv)

### Depth 4 now rests on exactly one proposition

`(du)` left depth 4 needing two inputs and flagged the second as unresolved. It is resolved.

```
lowerEnvBound_three            : LowerEnvBound 3 3                       ← PROVED
decayFloorUpTo_four_of_nodeDecay : NodeDecayBound 3 3 → DecayFloorUpTo 4  ← PROVED
```

#### The friction, and which way it had to go

`LowerEnvBound` quantified over all `x ≥ 1` with no per-tree ray. Absorbing
`depth_le_two_growth_envelope`'s tree-dependent `X₀` into the constant would require every EML germ to
be bounded on `[1, X₀]` — presumably true, and **not something this base can prove**: no compactness,
no continuity. So the definition grew the ray, which is what the corpus does everywhere else.

That is a definition changed one commit after shipping it. Worth saying plainly rather than quietly:
the flag in `(du)` was the right call and the resolution was the *other* branch of the two named.

With the ray it is assembly after all — `node_lower_of_right_upper` turns an **upper** bound on the
right child into a **lower** bound on the node, and the depth-2 growth envelope supplies it.

Two details that were not obvious until the proof was written:

* **The envelope's `M` may be negative**, so `E = exp (exp x + K) + M` can fail
  `node_lower_of_right_upper`'s `0 ≤ E` hypothesis. Replacing `M` by `exp M` fixes the sign and keeps
  the bound, since `exp M > M`. A hypothesis that looks like bookkeeping (`0 ≤ E`) turning out to be
  load-bearing against a *negative additive constant* is the kind of thing only writing the proof
  finds.
* **`exp (exp x + K) ≤ towerFn 3 x` is exactly `const_add_tower_le_succ` at `m = 1`** — the lemma
  written for the step does the arithmetic here too, unchanged.

#### The state of the ladder

```
depth ≤ 2   decayFloor_upTo_two          height 0    proved
depth ≤ 3   decayFloorUpTo_three         height 2    proved
depth ≤ 4   decayFloorUpTo_four_of_...   height 4    ONE input: NodeDecayBound 3 3
```

`NodeDecayBound 3 3` is the depth-4 analogue of `Depth3DecayExp`: how small can
`exp (A x) − log (B x)` be, positive, with `A` and `B` at depth ≤ 3. Reading the **discharged** column
first — the habit that paid off in `(dt)` — turns up `ExpExpGapBelow`, `BoundedCellApproach`,
`BoundedEmlCellApproach` and `BoundedEmlCellApproachLarge`, which are the cell decomposition of
`Depth3DecayExp`. **All four are stated at depth ≤ 2**, so they are the machinery for the rung below,
not for this one. The habit is still right; this time it returns nothing, and saying so is the point.

Its hypotheses must stay **pointwise** — that is what keeps the whole ladder free of `evSign_all` and
the analytic block, and it is a constraint on whoever proves it.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`. `DecayFloor` untouched; ledger unchanged at 21 rows /
9 open rows / 6 distinct open.

Gates, every figure read off the gate that produced it: build **752 jobs**, aggregator 749 of 1055,
consistency PASS, claims 466, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (du)

### The rung, as a step — and a correction: `(di)` does not block depth 4

New module `MachLib/EMLDecayLadderStep`. `(dt)` proved `DecayFloorUpTo 3` from two ingredients that
happened to be lying around. This turns that proof into a **general step**, so the next rung costs
one new theorem instead of a fresh argument.

```
decayFloorUpTo_succ :  DecayFloorUpTo j → NodeDecayBound j m → LowerEnvBound j m
                         → DecayFloorUpTo (j + 1)          -- at height m + 1
```

#### It reproduces `(dt)`, height and all

`nodeDecayBound_two` **is** `Depth3DecayExp` (`towerFn 1 x` is `exp x` definitionally);
`lowerEnvBound_two` follows from `depth_le_two_lower_on_ray` since `x ≤ exp x`; and

```
decayFloorUpTo_three_via_step :=
  decayFloorUpTo_succ (j := 2) (m := 1) decayFloorUpTo_two nodeDecayBound_two lowerEnvBound_two
```

comes out at height `2`, matching the hand proof exactly. **An abstraction that does not reproduce
the concrete case it was extracted from is a repackaging** — this one does, so it is not.

#### The correction: `(di)` does not block depth 4, and will not until depth 8

`(dt)`'s summary read `(di)` as blocking depth 4. **That is wrong, and the error is worth naming
because the pessimistic reading costs nothing to believe.**

`posEmbed t` has depth `t.depth + 4`, so the precise statement is that the positive branch at depth
`k` is at least as hard as `DecayFloor` at depth `k − 4`. With depth ≤ 3 now discharged, the branch at
depths **4, 5, 6 and 7** re-embeds only problems that are already solved. **The re-embedding first
bites at depth 8** — and that boundary *moves up by one with every rung proved*. Read carelessly,
`(di)` retires four rungs without an argument.

#### What depth 4 now costs

Two inputs at `j = 3`, and they are not the same kind of thing:

* **`NodeDecayBound 3 m` — the residue.** The depth-4 analogue of `Depth3DecayExp`: how small can
  `exp (A x) − log (B x)` be, positive, with `A` and `B` at depth ≤ 3. Same proposition
  `Depth3DecayExp` was, one rung down.
* **`LowerEnvBound 3 m`** — ingredients exist (`node_lower_of_right_upper` turns the depth-2 *upper*
  envelope into a depth-3 *lower* one, giving `m = 3`), with one friction flagged rather than waved
  at: `LowerEnvBound` quantifies over all `x ≥ 1` with no per-tree ray, while
  `depth_le_two_growth_envelope` holds only past a tree-dependent `X₀`. Either the constant absorbs
  the ray or the definition grows one, and which is cheaper has not been checked.

  > **⚠ RESOLVED in `(dv)`** — the definition grew the ray, and `lowerEnvBound_three` is proved.

The `NodeDecayBound` hypotheses are **pointwise** by design, copied from `Depth3DecayExp` — that is
what keeps the step free of `evSign_all` and the analytic block, and it is a constraint on whoever
proves the depth-4 instance, not an accident of how it is written.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`. `DecayFloor` untouched; ledger unchanged at 21 rows /
9 open rows / 6 distinct open.

Gates, every figure read off the gate that produced it: build **752 jobs**, aggregator 749 of 1055,
consistency PASS, claims 464, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dt)

### `DecayFloorUpTo 3` — the ladder's top moves for the first time in the arc

`(ds)` reduced the depth-3 rung to one residue and called it "a finite case analysis". **It was
already done.** `decayFloorUpTo_three` is now an **unconditional theorem**, and `Depth3NodeFloor` is
deleted rather than left standing as an obligation nobody needs.

#### The residue was a discharged ledger row, one module away

`Depth3DecayExp` — discharged since 2026-08-18 — *is* the hard half of the node case:

```
Depth3DecayExp : ∀ A B, A.depth ≤ 2 → B.depth ≤ 2 → ∃ C X₀, 1 ≤ X₀ ∧ ∀ x ≥ X₀,
    0 < log (B.eval x) → 0 < exp (A.eval x) − log (B.eval x) →
      -log (exp (A.eval x) − log (B.eval x)) ≤ C + exp x
```

The load-bearing detail is that `0 < log (B x)` sits **inside** the `∀ x` — it is a hypothesis *at
each point*, not an eventual one. So the node splits by a **pointwise trichotomy** on the sign of
`log (B x)`, and no eventual-sign machinery is needed:

* `log (B x) > 0` — `Depth3DecayExp` bounds `−log (node)` by `C₁ + exp x` outright.
* `log (B x) = 0` — the node **is** `exp (A x)`.
* `log (B x) < 0` — the node **exceeds** `exp (A x)`.

The last two are floored by `depth_le_two_lower_on_ray` (`A ≥ −C₂ − x`), and `tower_two_dominates`
puts `C₁ + exp x` and `C₂ + x` both under `exp (exp x)`. **Footprint clean** — had that hypothesis
been eventual rather than pointwise, the split would have needed `evSign_all` and with it the whole
analytic block, and it would have looked like a real obstruction.

> **A discharged row is a tool, not a trophy.** `Depth3DecayExp` was closed as bookkeeping for its
> refuted sibling `Depth3DecayHard`; nothing pointed from it to the rung it unlocks. **The ledger
> records status, not applicability**, and the gap between those two is where results go to be
> forgotten. Worth a habit: before naming a new residue, read the *discharged* column, not just the
> open one.

#### What moved

**`decayFloor_upTo_two` has been the top of the ladder for the whole arc.** It is now
`decayFloorUpTo_three`. `(de)` refuted `V₃`, the route meant to lift it, and `(dj)` showed the
reciprocal repair consumes `U 5` to produce `D 3`; the rung came from neither, but from `(di)`'s
`+4` re-embedding **not reaching `j = 3`** and from a row already in hand.

The height is **`2`, not the `1` `(ds)` guessed** — `Depth3DecayExp` gives `C + exp x`, which `exp x`
cannot absorb and `exp (exp x)` can. Against `(dr)`'s bracket depth 3 is now `[0, 2]`, improved from
`[0, 3]`; the conjecture `max (0, d − 3) = 0` is still open here, and `depth3_clamped_floor`'s
height-`1` clamped bound remains the best one-sided evidence for it.

#### Scope

**`DecayFloor` is untouched and the ledger does not move: 21 rows, 9 open rows, 6 distinct open.** A
bounded rung is not the obligation, and `DecayFloorUpTo 3` says nothing about depth 4 — `deepDecay 0`
sits at depth 4 and already defeats height 0 there.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **751 jobs**, aggregator 748 of 1054,
consistency PASS, claims 461, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (ds)

### The depth-3 rung, down to one finite case analysis

`decayFloor_upTo_two` has been the top of the ladder for the whole arc. `(de)` refuted `V₃`, the
route meant to lift it; `(dj)` showed the reciprocal repair consumes `U 5` to produce `D 3`, which
nobody has. Depth 3 has stood untouched. New module `MachLib/EMLDepth3Rung`.

#### Why depth 3 specifically is worth attacking

**It is the one place `(di)`'s re-embedding does not reach.** `posEmbed` shows the positive-`B` branch
at depth `j + 4` contains all of `DecayFloor` at depth `j` — which says nothing at `j = 3`, since
`3 − 4 < 0`. So unlike every higher rung, **the depth-3 positive branch is not known to be as hard as
the general obligation.** That asymmetry has been sitting in the corpus since `(di)` and nobody had
read it as an opening.

```
Depth3NodeFloor        the node case at depth 3, both children depth ≤ 2   ← the residue
decayFloorUpTo_three   Depth3NodeFloor ⟹ DecayFloorUpTo 3                  ← proved
depth3_clamped_floor   the clamped half of the residue                     ← proved
```

#### The reduction costs no axioms, and that was a design choice

The obvious way to split the node case is on the eventual sign of `B` — which needs `evSign_all`, and
with it the entire analytic block (`rolle_ct`, `analytic_finite_zeros_compact`,
`eml_tree_analytic_on_interval`). **`Depth3NodeFloor` is stated so no split is needed**: it takes the
node as given and asks only for the floor, so `decayFloorUpTo_three` dispatches on tree *shape*, never
on germ sign. The clamped half then becomes a theorem *about* the residue rather than a step *in* the
reduction.

**Footprint clean** — and this is the first place in the arc where staying clean required arranging
the statement rather than just checking afterwards. The sign split is now paid for only by whoever
finishes the branch.

#### The clamped half, and what its height says

`depth3_clamped_floor` runs on `depth_le_two_lower_on_ray` (a depth-≤2 germ is `≥ −C − x`), so a
clamped node is `exp ∘ A ≥ exp (−C − x)`, and `C + x < exp x` clears the tower. The ray is pushed to
`X₀ + exp C`, past both `X₀` and `C`, since `exp C > C` — which avoids needing a `max` on `Real`, a
thing this corpus does not have.

**It lands at height `1`, not height `0`** — and that is a property of the *route*, not of depth 3.
The linear floor `−C − x` carries an additive constant, and `exp (−C − x) < exp (−x)` whenever
`C > 0`.

> The sharper statement — that a depth-3 clamped node never dips below `exp (−x)` — appears to be
> **true**, and needs the depth-≤1 classification rather than the linear envelope. The largest
> depth-≤1 germ is `exp x + K`, whose log exceeds `x` by `log (1 + K e^{−x})` — **exponentially
> small** — while `exp (P x)` for depth-≤1 `P` decays at worst **polynomially** (`P` bottoms out at
> `≈ −log x`) and therefore dominates it. **That gap between `e^{−x}` and `1/x` is the entire
> margin.**

So the cheap route lands one rung above the conjecture `max (0, d − 3)` from `(dr)`, and the
conjecture survives. **Not proved** — recorded so the next session does not mistake `1` for the true
value, which is exactly the kind of slip a bounded result invites.

#### What is left

One finite case analysis: `A` and `B` both depth ≤ 2, `B` eventually positive, the node eventually
positive, and a floor wanted. `depth_le_two_normal_form` puts both children in the form
`exp a − log b` with `a`, `b` depth-1 forms, so the space is finite. It is also exactly the shape
`FRONTIER_BRIEF_3` warned was a trap at larger scale — **but at depth 3 the parameter regimes are the
four depth-1 closed forms, not an unbounded stratification**, and the trap it warns about is the
regime split, which here is finite too.

`DecayFloor` itself is untouched and the ledger is unchanged: **21 rows, 9 open rows, 6 distinct
open.** A bounded rung is not the obligation.

> **⚠ SUPERSEDED by `(dt)` — the residue was already discharged.** `Depth3DecayExp`, a **discharged**
> ledger row, *is* the hard half of `Depth3NodeFloor`, and its `0 < log (B x)` is **pointwise**. So
> `decayFloorUpTo_three` is now an unconditional theorem at height `2`, and `Depth3NodeFloor` is
> deleted. The reasoning below about why depth 3 is attackable stands and is what led there.

Gates, every figure read off the gate that produced it: build **751 jobs**, aggregator 748 of 1054,
consistency PASS, claims 458, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dr)

### The height reframing, built — and it routes the question rather than answering it

New module `MachLib/EMLHeightInterface`. The instruction was to stop attacking `DecayFloor` and build
the smallest interface under which it becomes almost automatic: a **height filtration** closed under
the grammar's operations, in which subtraction stays inside its layer instead of escaping upward the
way every syntactic measure does. Two lemmas were named — `(1)` EML depth ⟹ bounded height,
`(2)` nonzero bounded-height germ ⟹ leading-monomial floor. **Both are now stated, `(1)` is proved,
`DecayFloor` follows, and no axiom was spent.**

#### `(1)` is free — four lines, and it is what the axioms *say*

`HeightModel` asks for exactly the closure the reframing calls for, on **germs** rather than trees
(a height that reads syntax is a tree measure, and `EMLLadderMeasure` already disposed of those):
leaves cost `0`, `exp` costs at most one, `log` costs nothing, and **subtraction stays in the layer**.
From those alone,

```
HeightModel.eh_le_depth :  M.eh t.eval ≤ t.depth
```

by structural induction, in four lines, for **every** model. That is lemma `(1)` — and it is not an
achievement of transseries. It is the definition of "closed under subtraction, one per `exp`".

#### And the closure half cannot be where the content is

`zeroModel` — height identically `0` — satisfies **every** closure axiom. So satisfying them is no
evidence of anything, and lemma `(1)` is vacuous for it.

`not_leadingMonomialFloor_zeroModel` shows that is not a quibble: for the zero height the floor
property is **outright false**. The refutation is a family `deepDecay m = exp(1 − towerFn (m+1) x)`
of eventually-positive EML germs falling below `exp(−towerFn m x)` for every `m`, so no single tower
height serves them all.

> **The interface exposes a trade-off, not a decomposition.** A *coarse* height makes `(1)` trivial
> and `(2)` false. A height as fine as `depth` makes `(1)` trivial and `(2)` **is** `DecayFloor`,
> circularly. What is wanted is the **coarsest germ-invariant height for which `(2)` is still true**
> — and that, not the closure, is what transseries theory would have to supply.

That is worth having: it **routes** the question. Anyone bringing a height function now has a
mechanical check — satisfy four axioms, then prove the floor — and the corpus says immediately
whether their model is too coarse. `decayFloor_of_heightModel` and `emlGermApproach_of_heightModel`
are the payoff, with no induction on the tree anywhere.

#### The counterexample machine, replaced by a proof

The machine was to enumerate small trees and measure *(depth, exp count, log count, leading-monomial
height)* to decide whether the conjecture should be `h ≤ d`, `h ≤ 2d`, or subtler. `deepDecay`
answers it exactly, so the search is unnecessary: `deepDecay m` has depth **`m + 4`** on the nose and
defeats the height-`m` floor.

```
eh_le_depth                          height ≤ depth
height_m_fails_at_depth_m_add_four   height m FAILS at depth m + 4
```

> **The required tower height is at most `d` and at least `d − 3`. It is `d` up to an additive
> constant** — not `2d`, not `log d`, and certainly not bounded.

Two things follow. The obligation is **not** asking for a bounded height, so an attempt hoping to
find one is misreading it. And the slope is `1`: **one `eml` node buys exactly one tower level of
decay in the worst case** — the same exchange rate `(dj)` found for *growth*, which is what one
expects if `DecayFloor` and `GrowthEnvelope` are one obligation, and is an independent check that
they are. The three-node gap is the wrapper `deepDecay` needs to make its right child positive, the
same `+3`/`+4` constant `posEmbed` and `approachTarget` pay; an artifact of the encoding, not of the
mathematics.

#### What is not claimed

**No transseries were formalised, no embedding constructed, no axiom added.** `M.eh` is an abstract
`Nat`-valued function on germs; nothing here says a transseries height exists, is germ-invariant, or
satisfies the floor. Germ-invariance — the property that separates a real height from `depth` — is
deliberately **not** an axiom, because adding it would leave the structure uninhabited by anything
this corpus can exhibit, and an uninstantiated abstraction is the failure mode already paid for once
(`positive_branch_impossible`).

#### The bracket, as a theorem at both ends

`§6` puts the growth rate into the corpus's usual bounded form, the one `TowerLowerBoundUpTo` uses:

```
decayFloorUpTo_two        depth ≤ 2 is DISCHARGED at height 0 — optimal, 0 being least
decayFloorUpTo_height_ge  depth ≤ m+4 forces height ≥ m + 1
```

The second needs `towerFn` monotone in height (`towerFn_mono`, also new), since a height `k ≤ m`
would yield a height-`m` floor and `deepDecay m` refutes that. So the required height is **`0` for
`d ≤ 2` and at least `d − 3` after**, against the standing upper bound `d`. Every witness the corpus
has sits on the **lower** edge — `decayFast` (depth 3, height 0), `decayFaster` (depth 4, height 1),
`deepDecay m` (depth `m+4`, height `m+1`) — so the conjecture the data supports is `max (0, d − 3)`
exactly.

Nothing here proves the upper half at any `d ≥ 3`; that is `DecayFloor` and stays open. What the
bracket buys is a **falsifiable target**: a proposed construction yielding height `2d`, or even `d`,
is not merely unsharp — it is above a boundary the corpus can now name.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **750 jobs**, aggregator 747 of 1053,
consistency PASS, claims 456, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dq)

### Exponentiating does not create near-cancellation — and the obstruction shows up a third time

The transseries follow-up `(dp)` left open, and one theorem out of it. New `§5` of
`MachLib/EMLGermApproach`. **No axiom spent; no row changed; 243 pinned; distinct-open still 6.**

#### What the literature answered, and what it did not

The question was: *does the exponential **depth** of a term bound the exponential **height** of the
germ, uniformly?* Transseries theory carries both notions — *"the exponential and logarithmic depth
of an exp-log transseries, the maximal numbers of iterations of `exp` and `log` occurring in it, must
be finite"* — and the governing rule is:

> if a function is unbounded, the exponential height of its exponential composition increases by
> `1`; if it is bounded, the height stays the same.

So height tracks `exp`-nesting **for a transmonomial**. It is *differences* that break it:
subtraction can drop height arbitrarily, and at exact cancellation it drops to nothing. **That is
this obligation restated in the literature's own vocabulary** — good evidence the statement is in the
right terms, and not an answer.

#### The theorem it did buy

If `exp` raises height by exactly one, it should not be able to *manufacture* approach — only
inherit it. Provable, and now proved, from the disclosed tangent axiom and nothing analytic:

```
gap_ge_target_mul_log_gap :  C x * (A x − log (C x))  ≤  exp (A x) − C x     (C x > 0)
gap_ge_log_gap_of_one_le  :      A x − log (C x)      ≤  exp (A x) − C x     (C x ≥ 1)
```

> **The multiplicative gap dominates the additive gap, scaled by the target.** Two germs close
> *after* exponentiating were already close *before* it. **Exponentiation is not where approach comes
> from.**

`C x ≥ 1` is the only regime that matters: `approach_gap_ge_exp_of_nonpos` disposes of `C ≤ 0`, and a
target in `(0,1)` has `log C < 0`, so the gap already exceeds `exp (A x)`.

#### A third independent sighting of the same obstruction

`A − log C` sits one depth **above** `A` and `C`, because `log C` costs an `eml` node
(`log C = 1 − (eml (const 0) C).eval`). So peeling an exponential to expose the additive gap moves
**up** the ladder — exactly as `recipTree` does in `(dj)` and `posEmbed` in `(di)`.

**Three constructions that look unrelated, one direction of travel.** `EMLLadderMeasure` is the
reason, and this is its cleanest confirmation yet, because nobody was looking for it: the peeling
lemma was written to record a fact about `exp`, and the depth bookkeeping came out the same way for
the third time.

The bound is genuinely lossy where the germs are large — on `gapTarget n c` the true gap is the
constant `c` while `A − log C` is of order `c · exp(−towerFn n x)`, astronomically smaller. It is a
*floor*, which is what this obligation is about.

#### Honest limit

The transseries follow-up was **also abstracts only**. Three searches have now returned the same
framing and no theorem. **The next step is a specialist, not another search** — the precise question
is in the note, and it is a question about the literature rather than about this corpus.

**Footprint clean** — `exp_gt_one_plus_self` (the disclosed tangent axiom, deliberately) and the
ordinary field/order/`exp` base. No `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **749 jobs**, aggregator 746 of 1052,
consistency PASS, claims 448, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-27 (dp)

### The literature places the obligation: everything but one quantifier is a theorem of 1912

A literature check against `EmlGermApproach`, recorded in
`monogate-research/exploration/germ_approach_literature_2026_08_27/NOTE.md`. New `§4` of
`MachLib/EMLGermApproach`. **No axiom spent; no row changed status; 243 pinned.**

> **The per-pair version of the obligation is a corollary of Hardy (1912). The entire mathematical
> content of what MachLib needs is the position of a single `∃ k`.**

#### Why the per-pair version is classical

Three classical facts compose. EML germs at infinity are germs of Hardy's **logarithmico-exponential
functions** — totalised `log` is first-order definable in `ℝ_exp`, so totalisation does not leave the
class. The LE-functions form a **field**, so where the gap `exp ∘ A − C` is eventually non-zero its
**reciprocal is again an LE-function**. And every Hardy-field germ is `o(exp^∘k)` for **some** `k`.
Compose: `1/gap ≤ exp^∘k` gives `gap ≥ exp(−towerFn (k+1) x)`.

**That is the reciprocal route `(dj)` found from the inside.** `recipTree` *is* the reciprocal of the
field-closure fact, and `(dj)`'s "the grammar already contains `log`, so a reciprocal is two nodes,
`+2` depth" is the syntactic shadow of "the LE-functions are closed under division". The corpus
rediscovered a 1912 argument by walking into it backwards.

#### What is not classical, and two near misses that show why

`EmlGermApproach` puts `∃ k` **before** `∀ A C`, with `k` from the depth bound alone. Nothing found
supplies that.

* **Berarducci–Servi (2004)** prove `ℝ_exp` **effectively o-minimal**: the number of connected
  components of a definable set is bounded *computably in the complexity of a defining formula* —
  exactly the kind of syntactic uniformity wanted. **But it counts components and this needs a
  rate.** The corpus already has the lesson, in `FRONTIER_BRIEF_3`'s correction banner: `exp(−x)` is
  positive on the ray, has **no zeros at all**, and still has infimum `0`. Right kind of theorem,
  wrong quantity.
* The classical **Łojasiewicz inequality** — the standard separation tool, with effective versions
  for polynomials and for Pfaffian functions — is **polynomially shaped**, and that shape provably
  does not extend to o-minimal expansions in which `exp` is definable.

  That last point retro-justifies a choice made before the check existed: this obligation's floor is
  `exp(−towerFn k x)`, a **tower-scale** envelope. **The shape was forced by the structure, not
  chosen** — and it is a third reason "bounded away from zero" was the wrong description.

#### What it changes: where an assumption would be spent

Nothing in the corpus. One thing about the trust boundary: **if an assumption is ever spent it should
be spent on the uniformity alone.** The per-pair half is a theorem of 1912, and importing it would
widen the disclosed surface for nothing. So `§4` states `EmlGermApproachPerPair` — `k` chosen after
seeing the germs, no depth hypothesis, because none is used — and proves
`emlGermApproachPerPair_of_emlGermApproach`. The converse is not proved and nothing here suggests it.
**The gap between those two Props is the entire open problem, and the corpus's whole depth programme
lives inside it.**

Neither version is provable *inside* MachLib either way: `MachLib.Real` is an axiomatised abstract
ordered field with `exp`/`log`, not standard ℝ, so a theorem about the standard reals is not a
theorem about every model of these axioms. Unchanged since the 2026-08-19 note; worth restating
because "it is classical" invites exactly that slip.

#### Honest limits of the search

Web search and abstracts; **no paper read in full**, and the Hardy-field survey failed to decode as
text. **Absence of a citation is not absence of a theorem** — "nothing found supplies the uniformity"
is a claim about a two-hour search. The precise question for a specialist is recorded in the note:
*is the exponential height of an LE germ bounded by the exp-depth of a defining term, uniformly?* The
transseries literature, where exponential and logarithmic depth are standard load-bearing notions, is
the next place to look.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **749 jobs**, aggregator 746 of 1052,
consistency PASS, claims 446, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-26 (do)

### The obligation was under-restricted — by its own criterion

`(dn)` adopted a rule and then failed to apply it fully: *put into the obligation whatever the
downstream proof actually needs, and nothing else.* `EmlNodeSeparation` assumed a general positive
right child `B`. **The downstream proof never supplies one.** Every `B` it hands over is an `eTree`,
because that is how `posEmbed` manufactures a right child positive *everywhere*. So the positivity
was an **assumed hypothesis standing in for a structural fact** — precisely the shape this corpus has
learned to distrust.

Writing `B = eTree C` and cancelling `log ∘ exp` leaves an **approach** question:

```
EmlGermApproach :
  ∀ j, ∃ k, ∀ A C X₀,  A.depth ≤ j → C.depth ≤ j → 1 ≤ X₀ →
    (∀ x ≥ X₀, C.eval x < exp (A.eval x)) →
    ∃ X₁ ≥ X₀, ∀ x ≥ X₁, exp (-(towerFn k x)) ≤ exp (A.eval x) - C.eval x
```

> **An EML germ that stays strictly below `exp ∘ A` on a ray stays below it by an effective
> envelope.**

**One hypothesis fewer** — positivity is now discharged by the shape of the statement rather than
demanded of whoever supplies it — and the depth cost drops from `+3` to `+2`. New module
`MachLib/EMLGermApproach` **replaces** `EMLNodeSeparation`, which is deleted: four names for one
obligation would be worse than three.

#### Still an equivalence, still said out loud

```
Approach j   ⟸ DecayFloor (j+2)     via the tree  eml A (eTree C)
DecayFloor j ⟸ Approach (j+2)       via the target  1 − t x,  with A := const 0
```

Both proved. **Not progress on difficulty.** The three-row cycle stands and the gate still reports
`3 rows, ONE open obligation`.

#### Where cancellation cannot happen

`approach_gap_ge_exp_of_nonpos`: a **non-positive target** leaves the gap at least `exp (A x)`, so
nothing cancels and the floor is a plain lower bound on `A`. **Cancellation requires a positive
target.** That does not shrink the obligation — the positive-target branch still needs the envelope,
and `(di)` showed that branch re-embeds the whole problem — but it is the first thing a counterexample
hunt should stop spending time on.

#### The counterexample hunt

Four probes, and **no counterexample was found**. Stated carefully, because a failed hunt is not
evidence of absence — this corpus has a 12 208-sample grid search in its history that missed a
transcendental witness:

* **exact meeting** — `C = eTree A` matches `exp ∘ A` on the nose, gap identically `0`, strict
  hypothesis fails exactly there. Two EML germs **can** meet; where they do no envelope exists, so
  the hypothesis is load-bearing and cannot be dropped.
* **near-meeting of two arbitrarily fast-growing germs** — `gapTarget n c`: both germs at tower
  height `n + 1`, gap **exactly the constant `c`**, at every `x`, every `n`, every `c`.

  > The germs live at height `n + 1`; the floor their gap needs is height **0**.
  > **Approach is not controlled by growth rate.**

  This is the case a growth-based argument would be expected to handle and cannot even see, and it
  retro-explains why `(dm)`'s germ-height parameter was never the right instrument.
* **a gap that tends to zero** — `approachTarget decayFast` has gap `exp (1 − x)`, infimum `0`, and
  still meets the height-`0` floor. Read as *"bounded away from zero"* the obligation is **false
  here**, on a member of its own class.
* **non-positive target** — no cancellation at all.

What the probes establish is narrower than "it is probably true": the two ways to make the gap small
that a first attempt reaches for — **outrunning the target by growth**, and **driving the gap to
zero** — are both *satisfied instances* rather than counterexamples, and the hypothesis boundary sits
exactly at germs meeting. A counterexample, if one exists, is not of either shape.

#### Still no axiom

The row stays **open**, **243 axioms pinned**. An external mathematical input is not automatically an
axiom; until it is deliberately accepted without proof it is an obligation nobody has discharged.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **749 jobs**, aggregator 746 of 1052,
consistency PASS, claims 445 (7 retired with `EMLNodeSeparation`, 7 registered), obligations
**21 rows / 9 open rows / 6 distinct open** with 18 canaries, discovered 290/294, AxiomLedger
**243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-26 (dn)

### The missing input, named — and it is a separation, not a bound away from zero

New module `MachLib/EMLNodeSeparation`. **No axiom was added and the count of open obligations did
not move.** That is the point of the entry.

> **⚠ SUPERSEDED by `(do)` — this obligation was under-restricted, by the criterion stated below it.**
> Every `B` the downstream proof supplies is an `eTree`, so the assumed `0 < B` was standing in for a
> structural fact. `EmlGermApproach` replaces it with one hypothesis fewer and a `+2` rather than
> `+3` depth cost. Everything else in this entry — the envelope-not-a-constant point, the
> equivalence, the stress cases — carries over unchanged.

#### It is not "bounded away from zero"

The tempting description of the missing input is *"a non-vanishing EML germ is bounded away from
zero"*. **Taken literally that is false, on ordinary members of the class**: `exp (1 − x)` and `e / x`
are positive everywhere on the ray and have infimum `0`. `decayFast_floor` has been in the corpus for
days, flooring one of them.

What `DecayFloor` consumes is not a positive constant but an **effective lower envelope** of one
specific shape — `exp (-(towerFn k x))`, `k` from the depth bound and never from the tree. The
obligation states that and nothing else.

#### Exactly what the downstream proof consumes, and no wider

`DecayFloor` splits on the sign of the right child; the clamped branch is already a theorem
(`decayFloor_clamped`). What is left is the branch where `B` is eventually **positive**, so that
restriction goes *into* the obligation rather than being quantified away:

```
EmlNodeSeparation :
  ∀ j, ∃ k, ∀ A B X₀,  A.depth ≤ j → B.depth ≤ j → 1 ≤ X₀ →
    (∀ x ≥ X₀, 0 < B.eval x) →
    (∀ x ≥ X₀, 0 < exp (A.eval x) - log (B.eval x)) →
    ∃ X₁ ≥ X₀, ∀ x ≥ X₁, exp (-(towerFn k x)) ≤ exp (A.eval x) - log (B.eval x)
```

Same quantifier order as `DecayFloor`, same floor shape. Two germs that **do not meet** on a ray are
separated there by an effective envelope.

#### It is an EQUIVALENCE, and the ledger says so

Both directions are proved, so this is a **third name for one obligation, not a shrink**:

```
Sep j        ⟸ DecayFloor (j+1)     one node
DecayFloor j ⟸ Sep (j+3)            via posEmbed — NO induction
```

The forward direction needs no induction at all: `(di)`'s `posEmbed` already re-embeds every tree
into a node whose right child is positive *everywhere*, so the restricted obligation reaches every
tree. The ledger now carries a **three-row cycle** — `DecayFloor ⇄ EmlNodeSeparation ⇄
GrowthEnvelope` — and the gate reports `3 rows, ONE open obligation`. **The distinct-open count did
not move.** Recording the equivalence, rather than only the useful direction, is what stops a later
session reading this as progress on difficulty. It is not.

What it *is*: the obligation restated in the idiom in which an external theorem could be cited. A
Hardy-field, o-minimal or Pfaffian separation result is a statement about two germs failing to meet;
it is not a statement about tower floors for shallow syntax trees. Nothing in the corpus was shaped
like the thing that would buy it until now. **`GrowthEnvelope` is no longer independently
mysterious** — it, `DecayFloor` and the separation are one object, and the object has a name in
somebody else's literature.

#### Stress cases, shipped with the statement

An obligation nobody has attacked is an obligation nobody has understood.

* **Exact cancellation** — `B = eTree (eTree A)` makes `log (B x)` equal `exp (A x)` on the nose, so
  the node is identically `0`, at every `A` and every `x`. The right child is an `exp`, hence
  positive everywhere, so the pair *satisfies* the `B`-positivity hypothesis and fails only the
  node-positivity one. Two EML germs **can** meet, and where they meet no envelope exists: the
  hypothesis is load-bearing and cannot be dropped.
* **Near-cancellation of two arbitrarily fast-growing germs** — `gapNode_eval`: with
  `A = towerTree n` and `B = eTree (eml (towerTree n) (const (exp c)))`, both `exp (A x)` and
  `log (B x)` grow like an `(n+1)`-fold tower and their difference is **exactly the constant `c`**,
  at every `x`, for every `n` and every `c`.

  > The germs live at tower height `n + 1`; the floor their difference needs is height **0**.
  > **Separation is not controlled by growth rate.**

  That is the case a growth-based argument would be expected to handle and cannot even see — and it
  is why `(dm)`'s germ-height parameter was never going to be the right instrument.
* **A node that tends to zero and still meets the floor** — `posEmbed decayFast` is a positive-`B`
  pair whose node is `exp (1 − x)`, infimum `0`, and it meets the height-`0` floor. Read as *bounded
  away from zero* the statement would be **false here**, on a member of its own class.
* **The totalised-log branch** — excluded by hypothesis, covered by `decayFloor_clamped`, and
  exhaustive with the positive branch by `evSign_all`.

#### Why the row is `open` and not `assumed`

**An external mathematical input is not automatically an axiom.** Right now this is a theorem we need
from outside the machinery we possess; until it is *deliberately* accepted without proof it is simply
an obligation nobody has discharged. `(dm)` repaired the ledger so it can finally represent that
distinction — `open` versus `assumed` — and the first thing to do with the repair is to use the
honest half of it. **243 axioms stay pinned.**

The ordering is worth noting: the moment this corpus first contemplated importing an assumption was
also the moment it discovered the obligation ledger could not tell an assumption from a proof.
Fixing that *before* adding the axiom was the correct sequence, and it was luck rather than design
that the two came up together.

#### Two corrections

**`(dm)` claimed more than was proved.** It ended *"a proof would need something that is not a
well-founded descent on the tree at all."* What `(dk)`–`(dm)` kill is **local scalar growth descent
through the syntax tree** — a `Nat`-valued measure on trees, syntactic or germ-based, descending to
both children. No theorem here excludes every conceivable well-founded relation: a lexicographic
order, an ordinal rank, a well-founded *relation* on germs rather than a function of them, and any
non-structural argument are untouched. `(dm)` carries a correction banner and `EMLLadderMeasure`'s §3
now states the width correctly.

**Counts are now policy, in `CLAUDE.md`.** No count in prose may be written from memory: run the
gate, read its number, paste it. Three remembered counts went into this arc's changelog wrong
(`claims 429` for 431, `claims 439` for 438, and an earlier `5 851 theorems` by an unrecorded
method). The gates were right every time and cost about a second each. A wrong count is worse than a
missing one, because it reads as measured.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates, every figure read off the gate that produced it: build **749 jobs**, aggregator 746 of 1052,
consistency PASS, claims 445, obligations **21 rows / 9 open rows / 6 distinct open** with 18
canaries, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

**The distinct-open count is 6, before and after.** A row was added and nothing was discharged; that
is what an honest ledger looks like when work isolates rather than closes.

## [Unreleased] — 2026-08-26 (dm)

### The germ route closes too — and the obligation ledger finally looks at axioms

Two things, from the two directions `(dl)` left open.

#### 1. The germ route escapes §1 and dies of something else

`(dl)` ended by naming the honest residual: *an induction on the **germ** rather than on the
syntax.* New `§4` of `MachLib/EMLLadderMeasure`. It really does escape — and not for long.

**It escapes.** Every syntactic measure pays `2 * step` for `recipTree` (`recip_ge`). A germ measure
pays **nothing** — it goes *down*. Where `t ≥ 1` on a ray, `recipTree t` is `e / t x`, hence at most
`e`: a constant, tower height `0`, however fast `t` grew (`recipTree_germ_bounded`). The construction
that costs every syntactic measure two steps costs a growth measure **less than nothing**, so a
germ-based parameter is genuinely outside everything `(dk)` and `(dl)` cover.

**And it dies anyway.** Such a parameter must still descend to **both** children — `(dl)` identified
that as the real requirement — and it does not descend to the *right* one. Totalised `log` sees to
it:

```
capNode n = eml (const 0) (towerTree (n+1))        capNode_eval : = 1 − towerFn n x
                                                   capNode_nonpos : ≤ 0 on [1, ∞)
```

The node is **non-positive on the ray**, so it needs no tower height at all, while its right child
*is* the `(n+1)`-tower (`tower_height_does_not_descend_right`). The gap is not a constant to be
absorbed — **it is unbounded in `n`.**

> A node can be arbitrarily **flatter** than the child it is built from, because the right child
> enters under a `log`. Growth descends on the left and inverts on the right.

So the two routes fail for **opposite** reasons: syntactic measures grow too fast under `recipTree`;
germ measures do not descend to the right child. That is the pincer, and with it the induction
question is closed on both sides. What survives is narrower still and no longer a matter of choosing
a parameter: a proof would need something that is not a well-founded descent on the tree at all.

> **⚠ CORRECTED in `(dn)` — that last sentence claims more than was proved.** What `(dk)`–`(dm)`
> kill is **local scalar growth descent through the syntax tree**: a `Nat`-valued measure on trees,
> syntactic or germ-based. No theorem here excludes *every conceivable well-founded relation* — a
> lexicographic order, an ordinal rank, a relation on germs rather than a function of them, or a
> non-structural argument are all untouched. The sentence is left unaltered as the record of what
> was written; the correct width is stated in `(dn)` and in `EMLLadderMeasure`'s §3.

`open Real` is scoped to `§4` on purpose — it shadows `max`, which `§2`'s `depthMeasure` needs.

**Footprint clean** — the ordinary field/order/`exp` base only. No `sorryAx`, no
`analytic_finite_zeros_compact`, no `eml_tree_analytic_on_interval`, no `rolle_ct`.

#### 2. The obligation ledger now looks at axioms — a documented precondition, discharged

`exploration/signhardcase_trust_boundary_2026_08_19/NOTE.md` decided how an external assumption may
ever enter this corpus, and recorded a **precondition that had to be fixed first**:

> if someone adds `axiom signHardCase_ax : SignHardCase` plus a one-line theorem concluding it, the
> obligations ledger will report the row as **discharged** — indistinguishable from a proof. The
> axiom ledger would separately surface the new axiom as footprint drift. But **no gate joins those
> two facts**, and the misleading one is the one a reader reaches for.

That was accurate: until now `obligation_ledger_check.py` contained no reference to axioms,
footprints or `sorryAx` at all. Both halves of *discharged* are now checked — that a theorem
concludes the proposition, **and that the theorem is a proof rather than a restatement of an
assumption**:

* `footprints` reads `#print axioms` for **every cited witness in one `lake env lean` run** (~1 s for
  all fourteen), and `axiom_types` reads the type of every axiom that turns up.
* `sorryAx` anywhere in a witness's footprint fails the row.
* An axiom **whose type IS the obligation** fails the row: that is a disclosed assumption, not a
  proof, and it must be marked with the new `assumed` status — which in turn must *name* the axiom,
  the way a `reduced` row must name its residue.
* A footprint that could not be read is **UNAVAILABLE, exit 2**. A gate that read a failed Lean run
  as an empty axiom set would report every row as pristine exactly when it knows least.

The gate now prints `witness footprints: 14 of 14 read, 75 distinct axioms, no sorryAx` **even when
nothing is wrong** — a check that is silent on success is indistinguishable from a check that did
not run, and this one was absent entirely until today.

Four canaries, all on synthetic footprints and types passed in as arguments, so each specimen owns
its whole world and none can go stale as the corpus improves:

* **15** — an axiom typed as the row is not a proof.
* **16** — a `discharged` row resting on `sorryAx`.
* **17** — discrimination, both ways: an *ordinary* axiom in the footprint must stay silent (nearly
  every discharged row here depends on `MachLib.Real` and would otherwise fail), and a correctly
  marked `assumed` row that names its axiom must stay silent too, or the new status would be
  unusable the moment it was introduced.
* **18** — an unread footprint is UNAVAILABLE, not clean.

**Canary 17 earned its keep immediately**: it failed on the first run, because the backticked-name
regex used everywhere else in the file stops at a dot, so a row citing `` `MachLib.canary_ax` ``
matched nothing. The check would have accepted no correctly-marked `assumed` row at all. A
discrimination specimen catching a bug in the check it discriminates is the whole argument for
writing the silent half.

**No axiom was added.** The interface itself stays parked — that note's own doctrine is to prefer the
narrowest surface and to weigh the trust boundary deliberately, and *"adding the axiom first and the
status later would be the exact shape of error the ledger exists to prevent."* This removes the
blocker; it does not spend it. `SignHardCase` was in any case later discharged outright
(`d7b8d28c`), so the parked interface was never needed.

Gates: build 748 jobs, aggregator 745 of 1051, consistency PASS, claims 438, obligations 20 rows /
8 open rows / 6 distinct open with 18 canaries, discovered 290/294, AxiomLedger 243 pinned,
sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-26 (dl)

### "Grammar-respecting" was not a restriction — it is the condition for a structural induction

`(dk)` proved the reciprocal transfer costs `2 * step` for every measure in a class it called
grammar-respecting, and that reads as a theorem about a *class*, inviting the reply **"then use a
measure outside the class"**. This closes that reply. There is nowhere to go.

A structural induction on an EML tree recurses into its children, and the ladder step recurses into
**both** — left for the envelope, right for the floor. A `Nat`-valued measure supporting that must
strictly descend to both children. And any measure that does **is** a `LadderMeasure` with
`step = 1`, *definitionally*: `Nat.lt n m` is `n + 1 ≤ m`, so the two descent hypotheses are the two
structure fields verbatim, with no proof at all (`LadderMeasure.ofStrictDescent`).

```
recip_not_at_one_step_of_strict_descent
  (∀ A B, m A < m (eml A B)) → (∀ A B, m B < m (eml A B)) → ¬ (m (recipTree t) ≤ m t + 1)
```

The `LadderMeasure` packaging drops out; what remains is a statement about **any** `Nat`-valued
measure on trees that descends to both children.

#### The escape route of `(dk)`'s own scope note, closed by contraposition

That note left open *"a parameter that can decrease under `recipTree`"*.
`no_structural_induction_of_cheap_recip` disposes of it: a measure pricing `recipTree t` within one
step of `t` **does not strictly descend to both children**, so there is no induction left for it to
be the parameter of.

> **Cheap reciprocals and structural descent cannot be had together.** One tree priced cheaply
> refutes descent everywhere, which is why the statement needs only a single `t`.

Both sides are exercised rather than asserted. `depth_strict_descent` shows the descent hypothesis
is satisfiable, so the theorem is not about an empty class; and `const_measure_not_descending`
**fires** the contrapositive on the constant measure — which does price every reciprocal at `0`, and
what comes back is that it descends nowhere. A transfer no measure satisfies would prove nothing.

#### The residual, stated honestly

What is genuinely untouched is a parameter that is **not** a `Nat`-valued measure on the tree: a
lexicographic pair with an unbounded second component, an ordinal, or an induction on the **germ**
rather than on the syntax. That is where a proof would now have to come from, and it is a materially
narrower opening than `(dk)` left. `GrowthEnvelope` stays open, unchanged, still one obligation with
`DecayFloor`; nothing here bounds or discharges anything.

**Footprint clean** — the same `[propext, Real, Quot.sound, Real.oneR, Real.zeroR]`, and
`ofStrictDescent` needs only `[Real]`.

Gates: build 748 jobs, aggregator 745 of 1051, consistency PASS, claims 434, obligations 20 rows /
8 open rows / 6 distinct open, discovered 290/294, AxiomLedger 243 pinned, sorry-audit 1 allowlisted,
witness audit 36.

## [Unreleased] — 2026-08-26 (dk)

### The ladder fails for **every** grammar-respecting measure — and the open count was 7, not 6

Two things, and the second is the one that will matter in a month.

#### 1. Reaching for size does not help

`(dj)` proved `DecayFloor ↔ GrowthEnvelope` and closed with a sentence rather than a theorem:
*"any proof must find an induction parameter that is not depth."* The obvious next reach is
**size** — `EMLSizeCost` already prices trees that way, `two_mul_depth_succ_le_size` bridges the
two, and `T38-NNP` prices silicon that way. New module `MachLib/EMLLadderMeasure`: that reach fails,
and it fails for every measure of the kind at once rather than one at a time.

A measure **respects the grammar** if an `eml` node costs at least `step > 0` more than *either*
child. That one hypothesis generates both halves of the picture:

```
step_children  μ (eml A B) ≤ j + step  →  μ A ≤ j ∧ μ B ≤ j      one step buys one node
recip_ge       μ t + 2 * step  ≤  μ (recipTree t)                the reciprocal spends two
```

and hence

```
recip_not_at_one_step : ¬ (μ (recipTree t) ≤ μ t + step)
```

> **The route consumes the envelope one full step above the level it delivers, for every measure in
> the class.** Not a fact about depth — a fact about the step spending one `eml` node while
> `recipTree` spends two.

**Both specimens meet `recip_ge` with equality**, so the class is inhabited and the bound is sharp
rather than merely true — an abstract bound no real measure meets proves nothing, and this corpus
has paid for that lesson once already:

```
depthMeasure   step = 1    (recipTree t).depth = t.depth + 2      = 2 * step
sizeMeasure    step = 2    (recipTree t).size  = t.size  + 4      = 2 * step
```

The size column is the answer to the question that prompted the file, and `size_ladder_fails` states
it in the form a session reaching for size would want: `¬ ((recipTree t).size ≤ t.size + 2)`. It is
not a coincidence that the numbers double — one `eml` node costs `1` depth and `2` size (the node
and the leaf it needs), so **every** construction in `EMLDecayFloorIsGrowth` costs exactly twice as
much in size as in depth, the converse route included at `+3` and `+6` (`recipTree_eTree_size`).

**Where the escape hatch is, and why it is not one.** The hypothesis doing the work is `step_pos`.
A measure pricing an `eml` node at `0` evades `recip_ge` — and then `step_children` returns `μ A ≤ j`
from `μ (eml A B) ≤ j` with no decrease, so there is no induction left to carry. The hypothesis that
makes the obstruction bite is the same one that makes the ladder a ladder; the two facts have one
source, which is exactly why changing the measure does not help. That last sentence is prose, not a
theorem: *"no induction terminates"* is not a proposition this corpus can state and is not claimed
as one.

**Scope.** Bounds nothing, discharges nothing. `GrowthEnvelope` stays open, unchanged, still one
obligation with `DecayFloor`. It does not say no proof exists — only that no induction whose
parameter is a grammar-respecting measure can run the reciprocal transfer as its step. A parameter
that can *decrease* under `recipTree`, or that is not a function of the tree at all, is untouched.
This is the fourth route-closure in the arc and, like the other three, it cost a fraction of what
the positive results cost.

**Footprint clean** — `[propext, Real, Quot.sound, Real.oneR, Real.zeroR]` and nothing else. No
`sorryAx`, no `analytic_finite_zeros_compact`, no `eml_tree_analytic_on_interval`, no `rolle_ct`.

#### 2. The open count was overstated by one, and no gate could see it

`(dj)` built `reduction_cycles` so that two rows reducing to each other would not leave the open
column together. A second instance of the same thing was **already in the tree** and went on being
counted twice.

`TowerReducesToSign` is literally `SignHardCase → TowerLowerBound`. `signHardCase_holds` discharged
the antecedent, so `towerReducesToSign_iff_towerLowerBound` (`EMLTowerAfterSign`, since `b5c9fd53`)
makes the two rows **equivalent** — and that module's own docstring says so, *"two ledger rows that
looked like separate debts are one debt stated twice"*, while the ledger reported two through three
commits, including the one that built the cycle checker.

**It was invisible because two checks each declined to look at it, and both were right to.**
`dischargers_of` skips any conclusion containing `↔`, so that `foo : P ↔ Q` cannot read as a proof of
`P` (canary 9) — and `EMLTowerAfterSign` states the equivalence as an `Iff` *on purpose*, citing that
rule. `reduction_cycles` walks the residue edges of **reduced** rows, and two rows marked **open**
contribute no edge. So the theorem fed into nothing at all.

> **A rule that says what a theorem does *not* establish must also say what it *does*, or the
> theorem leaves the checker's field of view entirely rather than merely leaving one column of it.**

`obligation_ledger_check.py` now has `proved_equivalences` (unconditional `↔` between two rows),
`check_equivalences`, and `open_units`, which groups the open rows into obligations across *both*
routes — cycles and equivalences. Corrected:

```
open rows: 8
distinct open obligations: 6        (was reported as 7)
```

The debt was **overstated**, not understated, which is why nothing failed and why it survived. Three
canaries, all on synthetic declarations so they cannot go stale the day the corpus improves — the
way canaries 5 and 10 each broke once:

* **12** — an `↔` between two open rows collapses them, *and* the same rows without the equivalence
  must stay two, or the check would only be saying that open rows are suspicious.
* **13** — an `↔` to a **discharged** row marks the other side `STALE`. Same blind spot, in the
  direction that *understates* the corpus: before this, a row proved equivalent to a discharged one
  read as a perfectly good open row.
* **14** — a **conditional** `(h : X) : a ↔ b` collapses nothing until `X` is discharged, but is
  reported rather than dropped, since a silent skip is the defect being removed.

The self-test's closing line no longer counts itself. It said *"all ten convict specimens"* while
eleven ran, because a literal in a message is a snapshot that trains you to edit it rather than to
re-derive it.

Gates: build **748 jobs**, aggregator 745 of 1051, consistency PASS, claims 431, obligations **20
rows / 8 open rows / 6 distinct open**, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1
allowlisted, witness audit 36.

## [Unreleased] — 2026-08-26 (dj)

### `DecayFloor` **is** the growth envelope — and the ledger grew a cycle

`(di)` showed the positive-`B` branch of `DecayFloor` contains the whole problem. This says what the
whole problem *is*: the **at-infinity growth envelope**, which is the tool the depth ladder uses to
attack it.

#### The ladder step, and the repair that does not repair it

`depth_le_three_growth_envelope` is built exactly as the programme intends — it opens with
`depth_le_two_growth_envelope` for the left child and `depth_le_two_decay_on_ray` for the right, i.e.
`U (j+1) ⟸ U j ∧ V j`, literally. `(de)` proved **`V₃` is false**. `DecayFloor` is the repair:
`V`'s log-scale floor replaced by a tower-scale one.

The hope is that the repaired `D` restores the ladder. **It does not.**

#### The reciprocal is an EML tree, at `+2` depth

```
recipTree t = eml (eml (const 0) t) (const 1)          (recipTree t).eval x = exp (1 − log (t x))
                                                       (recipTree t).depth = t.depth + 2
```

which is `e / t x` wherever `t x > 0`. Nothing clever: **the grammar already contains `log`**, so a
reciprocal costs two nodes. (Not the `4` that `d(1/x)` costs — that four pays for pinning the
constant to exactly `1`, which an envelope never needs.)

Two transfers follow, both division-free and neither inspecting the shape of `t`:

* `floor_of_recip_upper` — a ceiling on `recipTree t` is a floor on `t`, at the **same** tower height.
* `upper_of_recip_floor` — a floor on `recipTree t` is a ceiling on `t`, one `+1` up.

Hence `decayFloor_iff_growthEnvelope : DecayFloor ↔ GrowthEnvelope`, with `GrowthEnvelope` the
at-infinity tower-form ceiling stated in `DecayFloor`'s own vocabulary. `GrowthEnvelope → DecayFloor`
costs `+2` depth and height `k`; `DecayFloor → GrowthEnvelope` costs `+3` and height `k+1`.

> ```
> U (j+1)  ⟸  U j ∧ D j     the step the corpus actually performs
> D j      ⟸  U (j+2)        this entry
> U j      ⟸  D (j+3)        this entry
> ```
> **The repaired step consumes the envelope two levels ABOVE the one it produces.**

`D` and `U` are not two obligations of which one might discharge the other. They are **one
obligation written two ways**, and the map rewriting either into the other moves *up* the depth
ladder both times. Any proof must find an induction parameter that is not depth.

#### The converse costs no axioms, because of where it is routed

The first draft proved `DecayFloor → GrowthEnvelope` by splitting on `evSign_all`, and paid the whole
analytic block for it — `rolle_ct`, `analytic_finite_zeros_compact`, `eml_tree_analytic_on_interval`.
Routing instead through `eTree` removes the split entirely: `recipTree (eTree t)` is `exp (1 − t x)`,
positive **everywhere** for every `t` of any sign, so it is a legal input to `DecayFloor` with no sign
analysis at all. One extra rung of depth, zero axioms. `#print axioms` on the `↔` shows only the
field/order/`exp` base.

#### Both transfers are exercised

Each transfer takes hypotheses, and a transfer no tree satisfies proves nothing. Both are fired on
`decayFast` (`(de)`'s depth-3 witness): its reciprocal is `exp` **on the nose**, since
`1 − log (exp (1 − x)) = x`, so the ceiling is met with equality. `decayFast_floor` already gives that
tree a *better* floor than the transfer returns — the specimen shows the machinery fires, not that it
improves a bound.

#### Ledger: a **reduction cycle**, and a gate that can see one

Both rows are now legitimately **reduced**, each to the other, and every per-row check passes on
both — the cited theorem concludes the proposition, it does assume the residue, and the residue is a
tracked row. **And nothing has been reduced.**

That is a defect in the *graph*, not in any row, so no per-row check could see it. The gate now walks
the residue graph (`reduction_cycles`) and reports cycles, with **canary 11** as the specimen —
required to fire on a 2-cycle and to stay silent on a legitimate linear chain, or it would be saying
only that reductions are suspicious. The count is now printed twice on purpose:

```
open rows: 6 marked open + 2 in 1 reduction cycle(s) = 8
distinct open obligations: 6 + 1 (each cycle is ONE obligation written several ways) = 7
```

**Seven is the number that did not move.** It was seven before this entry and it is seven after.
Without the cycle check the ledger would have shown the open column losing a row for a result that
closed nothing.

#### Scope

Bounds nothing, discharges nothing. `DecayFloor` stays open; so does `GrowthEnvelope`; they are the
same open question. It does not make `DecayFloor` harder either — the two were always the same
thing, and only now is that on the record.

`decayFloor_upTo_two` proves the half that was previously only asserted in prose: `V₂` is a
*log-scale* floor, strictly stronger than tower-scale, and converting it gives **every**
eventually-positive tree of depth ≤ 2 the floor `exp (−x)` — tower height `0`, whole depth class, not
two hand-picked witnesses. So `D 0`–`D 2` were in hand before this entry. The reciprocal route, fed
the corpus's `U 3`, would reach only `D 1`, and `U 3` is stated in explicit-constant form
(`exp (exp (exp x + K) + M) + N`) rather than `towerFn` form, so even that needs a conversion nobody
has written. **The route buys no new rung either way.**

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates: build **747 jobs**, aggregator 744 of 1050, consistency PASS, claims 425, obligations **20
rows / 7 distinct open**, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted,
witness audit 36.

## [Unreleased] — 2026-08-26 (di)

### `DecayFloor`'s open branch is not a corner case — it contains the whole problem

`(dh)` proved the clamped half and left the positive-`B` branch open. The natural next move is to
treat that branch as a special case and attack it separately. **That reading is wrong.**

**Every tree re-embeds into a positive-`B` node at `+4` depth.** With `eTree t = eml t (const 1)`
computing `exp ∘ t` (the `log 1 = 0` identity `expTree_eval` already uses):

```
posEmbed t = eml (const 0) (eTree (eml (const 0) (eTree t)))
```

unwinds to `1 − (1 − t x) = t x`, and its right child is `exp (1 − t x)` — **positive everywhere**,
not merely eventually, so it is a genuine instance of the open branch rather than a boundary case.
`posEmbed_depth` is `t.depth + 4` on the nose.

`floor_transfer_via_posEmbed` draws the consequence: a floor for the embedded node **is** a floor for
the original tree, verbatim.

> Solving the positive-`B` branch at depth `j + 4` solves `DecayFloor` at depth `j`.

So the branch is *at least as hard* as the general obligation, up to a depth shift of 4. There is no
route that disposes of it as a special case, and an attempt that reasons only about
"nearly-cancelling" nodes is reasoning about **every** node in disguise.

### Why this is worth a commit

It closes off a plausible line of attack before anyone spends a session on it — the same service
`(de)` performed for "make the pair iterate". Three of this arc's results are of that kind, and they
have been cheaper than the positive ones every time.

It also sharpens what `(dh)` said. The clamped/positive split is **not** a decomposition into an easy
half and a hard half; it is a decomposition into a half that reduces to the envelopes and a half that
is the original problem re-stated. The first is genuinely disposed of; the second was never a piece
of the problem, it *is* the problem.

**What this does not do:** it bounds nothing. It is a statement about where the difficulty lives, not
a step toward removing it, and should not be quoted as progress on `DecayFloor`.

`DecayFloor` stays **open** — the gate confirms *"open, no theorem concludes it"* — 19 rows unchanged.
**Footprint clean**: no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates: build **746 jobs**, aggregator 743 of 1049, consistency PASS, claims 422, obligations 19 rows,
discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-26 (dh)

### The third quantity, named — `DecayFloor`, ledger row 19

`(dg)` showed the pair was split along the wrong seam and that **decay** — distance from zero *from
above* — is a third quantity neither envelope controls. `(de)`/`(df)` showed it grows with depth.
This states it as a **named obligation**, the corpus's device for committing a partial result without
overstating it, and proves the half that needs no cancellation.

```
DecayFloor : ∀ j, ∃ k, ∀ t, t.depth ≤ j → (eventually positive) →
                             eventually  exp (-(towerFn k x)) ≤ t.eval x
```

**`k` depends on the depth only, not on the tree.** That is the whole content: quantified per tree
the existential could be chosen after seeing the germ and the statement would evaporate. Stated
against the corpus's own `towerFn` — the same object `towerTree` realises — so the obligation lives in
the depth programme's existing vocabulary rather than beside it.

### What is proved

`decayFloor_clamped` — the **clamped** branch. A non-positive right child totalises its `log` to `0`,
so the node *is* `exp ∘ A` and the floor is exactly a **lower bound on `A`**. Composed with
`(dg)`'s `node_lower_of_right_upper`, this is the branch that inherits from the envelopes, with no
cancellation anywhere.

Both witnesses are checked against the obligation: `decayFast_floor` (depth 3) sits above the
height-**0** floor, `decayFaster_floor` (depth 4) needs height **1**. So it is satisfiable where it
has been tested, and the height demonstrably grows — the two facts a named obligation should come
with, rather than being asserted into the ledger unexercised.

### What is open, precisely

The **positive-`B`** branch: `exp (A x) − log (B x) > 0` with `B` eventually positive, where the node
can be tiny because `exp (A x)` nearly cancels `log (B x)`. That is an *approximation* question — how
closely one EML germ can approach another without meeting it — and nothing built this session speaks
to it. In particular `evSign_all` gives eventual **non-vanishing**; this asks to be **bounded away**
from zero, which is strictly more.

### Ledger

**19 rows** (was 18): 7 open, 1 refuted, 11 discharged. `DecayFloor` enters as **open** and the gate
confirms *"open, no theorem concludes it"* — `decayFloor_clamped` concludes a statement about the
clamped branch, not the obligation.

Note the arithmetic: `SignHardCase` left the open column and `DecayFloor` entered it, so the count is
unchanged at 7. That is the honest bookkeeping — this session discharged one obligation and isolated
a new one, and the ledger should show both.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates: build **746 jobs**, aggregator **743 of 1049**, consistency PASS, claims 422, obligations
**19 rows**, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit
36.

## [Unreleased] — 2026-08-25 (dg)

### What *does* iterate — the pair was split along the wrong seam

`(de)` and `(df)` are negative. This is the positive counterpart, and it explains both.

> **`node_lower_of_right_upper`** — a node's **lower** bound follows from an **upper** bound on its
> **right child alone**.

```
(eml A B).eval x = exp (A x) − log (B x)  ≥  −log (B x)  ≥  −E x     when B x ≤ E x
```

`exp (A x) > 0` does all the work; `log y ≤ y` finishes it (`log_le_self_ge_one`, proved here from
`exp_gt_two_x` and `exp_log`). **The left child is never inspected** — the exact mirror of
`evSign_of_hard`'s observation about signs, and for the same reason: one side of an `eml` node is
structurally inert for one kind of question.

So `upper_j ⟹ lower_{j+1}` needs **no** cancellation analysis, **no** sign stability, and **no**
depth classification.

### Which retro-explains `V₂`

`V₂`'s clamped case is `depth_le_one_lower_on_ray` — a *lower* bound one level down, wearing decay's
clothes. It worked because it was never a decay statement. That is why it did not generalise, and why
`(de)`'s three-node witness broke the generalisation so easily.

### The seam

The pair was posed as **growth vs decay**. The evidence says the real split is **growth vs
lower-bound**, and those two iterate into each other cleanly. What does not iterate is *decay* —
distance from zero **from above** — a **third** quantity that neither envelope controls and which
`(de)`/`(df)` show grows with depth.

> Conflating the lower envelope with decay is what made `V_j` look inductive.

Three quantities, not two. Two of them compose; the third is the open problem. That reframing is the
result — it does not bound decay, and nothing here should be read as progress on that.

**Footprint clean** — no `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`. `TowerLowerBound` stays open, no ledger row moves.

Gates: build **745 jobs**, aggregator 742 of 1048, consistency PASS, claims 422, obligations 18 rows
unchanged, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit
36.

## [Unreleased] — 2026-08-25 (df)

### The decay rate grows with depth — a depth-3/depth-4 separation

`(de)` refuted `V₃` and suggested the repair was a bigger right-hand side. This shows the repair
cannot be a **fixed** one.

```
expXplus1   = eml var (const (exp (-1)))   exp x − log(exp(−1)) = exp x + 1   depth 1
expExpX1    = eml expXplus1 (const 1)      exp(exp x + 1) − log 1             depth 2
negExpX     = eml (const 0) expExpX1       1 − (exp x + 1) = −exp x           depth 3
decayFaster = eml negExpX (const 0)        exp(−exp x) − log 0                depth 4
```

`-log (decayFaster.eval x) = exp x`, so **`not_linear_decay_bound_depth_four`** rules out every bound
`C + x`. And **`decayFast_linear_bound`** shows `(de)`'s depth-3 witness *does* satisfy that bound,
with `C = 0`.

> Depth 3 satisfies the linear decay bound. Depth 4 does not.

That is a genuine **separation**, not another failure. Both depths are `by decide`.

### The mechanism, and what it forces

Each extra `eml` node buys one more `exp` in the decay exponent, and for the same two reasons as
before: `log 0 = 0` turns `eml A (const 0)` into `exp ∘ A`, and `eml (const 0) (expTree s)` into
`−s`. Note `const` takes an **arbitrary real**, so `const (exp (-1))` is legal and `exp x + 1` is a
*depth-1* tree — that is what keeps the whole ladder one rung shorter than it looks.

So the decay rate at depth `j` is a tower whose height grows with `j`, and:

> **Any correct `V_j` must be depth-indexed** — `-log (t x) ≤ E_{f(j)}(x)` with the height growing in
> `j`, not one envelope serving all depths.

That is sharper than `(de)`'s note, which only said "let the bound grow with depth". The two
witnesses jointly establish *that it must*, and rule out the cheapest reading of the repair.

**Still not proved:** that a depth-indexed form iterates. This constrains the shape of a solution; it
does not supply one, and should not be quoted as if it did.

`TowerLowerBound` stays **open**, no ledger row moves, and both new results are **footprint-clean** —
no `sorryAx`, no `analytic_finite_zeros_compact`, no `eml_tree_analytic_on_interval`, no `rolle_ct`.

Gates: build **745 jobs**, aggregator 742 of 1048, consistency PASS, claims 422, obligations 18 rows
unchanged, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness audit
36.

## [Unreleased] — 2026-08-25 (de)

### The decay bound does not iterate: `V₃` is false

`(dd)` discharged the *crossing* half of `V_j` at every depth and reported the **rate** half as
untouched. It is worse than untouched.

> **`not_decay_on_ray_depth_three`** — the rate statement, generalised one rung from where it is
> proved, is **FALSE**.

So the programme `EMLCertifiedSynthesis` names for `TowerReducesToSign` — *"proving the growth/decay
pair iterates at every depth — `U_j` and `V_j` for all `j`"* — cannot succeed in that form.

### The witness is three nodes

`depth_le_two_decay_on_ray` is `V₂`; `V₃` is the same with `≤ 3`.

```
expVar    = eml var (const 1)         exp x − log 1      = exp x        depth 1
oneSubX   = eml (const 0) expVar      exp 0 − log(exp x) = 1 − x        depth 2
decayFast = eml oneSubX (const 0)     exp(1−x) − log 0   = exp(1−x)     depth 3
```

`decayFast_depth` is `by decide`: depth **exactly** 3, one rung above where `V₂` holds — so `V₂` is
untouched. `decayFast` is positive everywhere, so the guard `0 < t.eval x` never protects it, and
`-log (decayFast.eval x) = x − 1`, which outruns `C + log x` for every `C`. The proof takes
`x := exp y` with `y ≥ max (C+1) X₀` and closes on the unconditional `exp_gt_two_x`.

**Footprint: clean.** No `sorryAx`, no `analytic_finite_zeros_compact`, no
`eml_tree_analytic_on_interval`, no `rolle_ct`. The refutation stands entirely independently of
`(dc)`'s discharge and its new axiom — it would have been true before this session started.

### Where the statement went wrong

Nothing exotic is involved, and that is the point. `log 0 = 0` makes `eml A (const 0)` compute
`exp ∘ A`; `eml (const 0) (expTree var)` computes `1 − x`; composing them gives a positive tree
decaying like `e·exp(−x)`. **Three nodes and the totalisation convention** — not the asymptotic
cancellation the watch-list expected to be the depth-3 obstruction.

`V_j`'s right-hand side `C + log x` is a **log-scale** bound: it says `t x ≥ e^{−C}/x`, i.e. *no
positive tree decays faster than a constant over `x`*. True through depth 2, false at depth 3 —
because depth 3 is exactly where a tree can put a **linear** function inside an `exp`.

That is the fourth time in this arc the totalisation convention has been the active ingredient, and
the first time it has worked *against* the programme rather than for it.

### What survives, and the shape a repair would take

`decayFast` has `-log t x = x − 1`, comfortably inside a **tower-form** envelope. So the natural
repair is to let the decay bound grow with depth — `-log (t x) ≤ envelope k M x` rather than
`C + log x` — mirroring what `EMLGrowthEnvelope` already does on the growth side. **Nothing here
proves such a form iterates.** It is recorded as the shape the evidence points at, not as a result,
and the next session should not read it as one.

`TowerLowerBound` stays **open** and no ledger row moves — `V_j` was never a row, it is the route the
ledger's note describes. What changed is that the route is now known to be closed off, which is worth
more than another session spent making it work.

Gates: build **745 jobs**, aggregator **742 of 1048**, consistency PASS, claims 422, obligations 18
rows unchanged, discovered 290/294, AxiomLedger **243 pinned**, sorry-audit 1 allowlisted, witness
audit 36.

## [Unreleased] — 2026-08-25 (dd)

### What the discharge did to the tower — and what it did not

Two consequences of `(dc)`, both small, both worth stating so the ledger reads correctly.
`EMLTowerAfterSign`.

### The two tower rows are one row

`TowerReducesToSign` is literally `SignHardCase → TowerLowerBound`. Its antecedent is now a theorem,
so

> **`towerReducesToSign_iff_towerLowerBound : TowerReducesToSign ↔ TowerLowerBound`**

Two ledger rows that looked like separate debts are one debt stated twice. Stated as an `Iff` on
purpose: a theorem whose bare conclusion is `TowerLowerBound` would read to
`obligation_ledger_check.dischargers_of` as an unconditional discharge of an open row — the shape
canary 5 exists to catch. The gate skips `↔`, and confirms both rows still read *"open, no theorem
concludes it"*.

### The crossing obstruction is discharged

`depth_le_two_decay_on_ray` reads `∃ C X₀, ∀ x ≥ X₀, 0 < t.eval x → -log (t.eval x) ≤ C + log x`, and
the guard is not decoration: near a zero crossing from above `t → 0⁺`, so `-log t → +∞` and no fixed
`C` survives. The statement is rescued only by pushing `X₀` past the last crossing — *finiteness of
sign changes*, which this corpus recorded as the **binding** obstruction to an all-depth theory.

`evSign_all` supplies it at every depth, and `decay_on_ray_of_positive_ray` cashes it:

> the guarded decay statement follows from the unguarded one **on a positivity ray**, for every tree
> at every depth

Both branches of `evSign_all` are used — on the positive branch the hypothesis applies with no
crossings to avoid; on the non-positive branch the guard is unsatisfiable and the conclusion is
vacuous. No classification, no hand analysis. `decay_on_ray_specimen` fires it on `var` so the
reduction is not vacuous.

### What it does not buy, stated plainly

**The rate.** `V_j` is quantitative and sign-definiteness supplies the ray, not the bound. At depth
≤ 2 the rate comes from the depth-≤1 classification, by hand; for general `j` there is still no
classification and nothing here supplies one.

So `TowerLowerBound` stays **open**. One of the two ingredients `V_j` needs is now free; the other is
untouched. `EMLCertifiedSynthesis`'s own note that the reduction "is not a formality" remains
correct — this narrows the gap, it does not close it, and it should not be quoted as if it did.

### Trust

All three results inherit `(dc)`'s footprint: 69 axioms including `eml_tree_analytic_on_interval`,
`analytic_finite_zeros_compact` and `rolle_ct`. Anything downstream carries the same disclosure.

Gates: build **744 jobs**, aggregator **741 of 1047**, consistency PASS, claims 422, obligations 18
rows (`TowerLowerBound` and `TowerReducesToSign` both still open), discovered 290/294, AxiomLedger
**243 pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-25 (dc)

### `SignHardCase` is discharged

> **`signHardCase_holds : SignHardCase`** — `EMLAnalyticDischarge`

The obligation the whole depth programme has been reduced to is proved, and the ledger row moves from
**open** to **discharged** for the first time. `evSign_all : ∀ t : EMLTree, EvSign t.eval` follows
unconditionally: **every EML tree is eventually of constant sign, at every depth.**

Read the trust cost before the result.

### ⚠ It rests on a new axiom, added deliberately

`AxiomLedger` goes **242 → 243**. The addition is

```
axiom eml_tree_analytic_on_interval (t : EMLTree) (a b : Real) :
    LogArgPos t a b → ∀ a' b', a < a' → b' < b → IsAnalyticOnReals t.eval (Icc a' b')
```

the **interval-localised twin** of the existing `eml_tree_analytic_on_pos`, which states the same fact
with the domain fixed to `(0, ∞)`. Declamping supplies log-argument positivity per *interval*, never
on all of `(0, ∞)`, which is why the existing form could not be used. It is registered in
`knownAxioms` and `disclosedUnwitnessed` (8 disclosed inert, was 7), and deliberately **not** added to
`trustedFootprint` — no headline cites it, and widening what headlines may cite was not the point.

**The alternative was rejected as unsound.** The other route — transport analyticity from the
encoder's barrier to `t.eval` along pointwise equality — needs an `IsAnalyticOnReals` congruence. But
`IsAnalyticOnReals f (Icc a b)` depends on `f` *near* each point, not only on `[a,b]`, so a plain
set-congruence is false in any faithful model. Choosing the port over the congruence was a deliberate
call, not a convenience.

Full footprint of `signHardCase_holds`: 69 axioms, of which the three that matter are
`eml_tree_analytic_on_interval`, `analytic_finite_zeros_compact` and `Real.rolle_ct`. **No `sorryAx`,
no `zero_count_bound_classical`, no `Khovanskii`, no `Fbasis`.**

### The argument

Four steps, each a separate theorem.

1. **An open interval is infinite** — `not_realSetFinite_of_contains_interval`. A bisection sequence
   strictly inside `(p,q)`, strictly decreasing, yields arbitrarily long nodup lists. Pure arithmetic,
   26 axioms, no analyticity.
2. **The identity theorem** — `eq_zero_on_Ioo_of_zero_on_subinterval`, the contrapositive of
   `analytic_finite_zeros_compact`: analytic on `Icc a b` with a zero set containing an interval
   forces `f ≡ 0` on `Ioo a b`.
3. **Vanishing propagates to a ray** — `evZeroF_of_zero_on_interval`. Widen the interval past any
   target point, re-run (2) on the **declamped** tree there, transfer the value back. Note that no
   analyticity is ever transported: the identity theorem runs entirely on `declamp t a' b'`, and only
   *values* cross to `t`, by `declamp_eval`. That is what makes the missing congruence irrelevant.
4. **The node** — `signHardCtsStable_holds`. Either the node value is eventually zero, and then it is
   eventually `≤ 0` so `EvSign` holds outright; or it is not, and (3) gives `(da)`'s non-vanishing
   input, `(da)`'s assembly turns that into a uniform zero bound, the ray bridge into eventual
   non-vanishing, and continuity plus the IVT finish it.

Both ingredients the obligation receives — eventual continuity and eventual log-argument stability —
are used, and neither is assumed of the caller: `(db)`'s induction manufactures both. That is what
`(db)` was for, and it is why this is not circular: `signHardCtsStable_holds` cites nothing from the
induction it feeds.

### The ledger

**6 open, 1 refuted, 11 discharged** (was 7/1/10). `SignHardCase`'s row now cites `signHardCase_holds`
with its three analytic axioms named in the row itself, so the trust cost travels with the claim.

`TowerLowerBound` and `TowerReducesToSign` were recorded as reducing to `SignHardCase`; whether they
now fall out is not checked here and no row was touched but `SignHardCase`'s.

Gates: build **743 jobs**, aggregator **740 of 1046**, consistency PASS, claims 422, obligations 18
rows (`ok SignHardCase: discharged by signHardCase_holds`), discovered 290/294, AxiomLedger **243
pinned**, sorry-audit 1 allowlisted, witness audit 36.

## [Unreleased] — 2026-08-25 (db)

### `EMLSignInductionV2` — the induction rewritten so the hard node is self-contained

The arc built three things the depth induction can manufacture — eventual continuity, eventual
log-argument stability, and through them a coherent Pfaffian encoding — but assembled them in **two
passes**: the induction ran first, conditional on `SignHardCase`, and stability was derived afterwards
from its output (`logArgStable_of_evSign (evSign_of_hard h)`).

That layering is what blocks any attempt to *discharge* the hard node. Anything proved from it already
assumes `SignHardCase`, so feeding it back proves `SignHardCase → SignHardCase`.

`EvLogArgStable` is now a **third conjunct of the induction's own motive**:

```
evSignContStable_of_ctsStable : SignHardCtsStable → ∀ t, EvSign t.eval ∧ EvCont t.eval ∧ EvLogArgStable t
```

**Why the children suffice.** `LogArgStable (eml A B) a b` needs stability inside `A`, stability
inside `B`, and the sign disjunction for `B` itself — `ihA.2.2`, `ihB.2.2`, `ihB.1`. Every node of
`eml A B` is either the node itself or a node of a structurally smaller tree, so nothing about the
node's own value is used. That is precisely why there is no circularity, and `evLogArgStable_eml`
isolates the step (14 axioms, no analyticity).

`SignHardCtsStable` is `SignHardCase` with **two** extra hypotheses, so it is implied by it
(`signHardCtsStable_of_hard`) and nothing is strengthened. What changes is the call site: an argument
at the hard node may now use eventual continuity *and* eventual log-argument stability of the whole
node without re-entering the induction.

Footprints are **clean again** — 41 axioms, citing no `analytic_finite_zeros_compact` and no
`rolle_ct`, unlike `(da)`'s assembly. The restructuring costs nothing in trust.

### ⚠ The next step is blocked on an axiom, not on a proof

The intended use of the rewrite was to discharge the hard node from analyticity: an EML value that is
identically zero on a sub-interval and analytic there is identically zero on the whole interval, so
`¬ EvZeroF` would give `(da)`'s non-vanishing input. The identity theorem is available —
`analytic_finite_zeros_compact` contraposed says analytic on `Icc a b` with an infinite zero set forces
`f ≡ 0` on `Ioo a b`.

**What is missing is the analyticity of `t.eval` itself**, and both routes to it fail:

* `enc_coherent_and_hAnalytic` gives `IsAnalyticOnReals (pfaffianChainFn … r).eval (Icc a b)`, which is
  *pointwise equal* to `t.eval` there by `enc_eval` — but `IsAnalyticOnReals` is an opaque `axiom`
  with closure rules (`analytic_add/sub/mul/comp/exp/log_pos/…`) and **no congruence along pointwise
  equality**. The same shape of obstruction as `HasDerivAt` in `(cu)`.
* `eml_tree_analytic_on_pos` gives analyticity of `t.eval` directly, but requires
  `EMLLogArgPosOnIoi t` — log-argument positivity on **all of `(0, ∞)`**, where declamping supplies it
  only per interval.

So closing this needs a **new axiom** (an `IsAnalyticOnReals` congruence, or an interval-localised
tree-analyticity port). That is a decision about the `AxiomLedger`, not a proof step, and it is not
taken here. Recording it as the precise blocker rather than working around it.

`SignHardCase` stays `open`, 18 rows unchanged, nothing registered.

Gates: build **742 jobs**, aggregator **739 of 1045**, consistency PASS, claims 422, obligations 18
rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness
audit 36.

## [Unreleased] — 2026-08-25 (da)

### The per-interval bound already existed; only non-vanishing is left

`(cz)` left the route needing *"per-interval bounds on the trees `declamp` actually produces"*. Those
bounds are already in the corpus, and this is the **fourth** time this session a "what remains" turned
out to be built.

`EMLExplicitBound.enc_combinedBound` takes an `EMLTree`, a context chain and `LogArgPosOn t (Icc a b)`
and returns an **explicit** bound

```
combinedBoundE (len t N) (enc t chain).1 (encTags t chain tags) p
```

which mentions **no interval** — a function of the tree and barrier alone, so already uniform in the
sense `eventually_nonzero_of_uniformZeroBoundFrom` needs. Unlike `eml_eval_boundedZeros` it carries no
`hdescent` hypothesis: the explicit mixed descent is unconditional.

So the remaining input collapses from *"bound the zeros"* to

> **`t.eval` is not identically zero on any interval beyond the ray.**

That is `enc_combinedBound`'s own `hne`, and the route needs it regardless — a function vanishing on
an interval has infinitely many zeros there and no bound of any kind.

### ⚠ Axiom disclosure — this entry is the first in the arc to pay

Every previous entry in this arc reported *"no footprint cites `analytic_finite_zeros`"*. **That
changes here.** `encBound_bounds`, `uniformZeroBoundFrom_of_nonvanishing` and
`eventually_nonzero_of_nonvanishing_of_hard` each cite

* `MachLib.analytic_finite_zeros_compact`
* `MachLib.Real.rolle_ct`

Both are inherited from `enc_combinedBound`, both are already pinned in the `AxiomLedger` (242,
unchanged), and neither is the deleted `zero_count_bound_classical` — `analytic_finite_zeros_compact`
is the **non-uniform, strictly weaker** analyticity axiom, which is why it survived the 2026-07-15
deletion. Still: results downstream of this module are no longer axiom-clean in the sense the earlier
sign work was, and anything quoting them must say so. No `sorryAx`, no `Khovanskii`, no `Fbasis`.

### The endpoint shift, a third time

`enc_combinedBound` wants positivity on the **closed** `Icc a b`; `declamp_logArgPos` supplies it on
the **open** `(a', b')`. So the declamping runs on `(a − 1, b + 1)` and the bound is applied on
`(a, b)`, strictly inside it — and the ray starts at `X₀ + 1`. Same shape as `ray_shift_nbhd` and the
`R + 1` seed in `EMLZeroBoundRay`: **third** place in this arc where a closed/open mismatch costs
exactly one unit. Worth expecting now rather than rediscovering.

Widening keeps the finiteness argument intact — `declamp t (a−1) (b+1)` is still in
`declampVariants t`, so the maximum is over the same finite list.

### The route, with one input

```
SignHardCase → EvSign everywhere → LogArgStable on a ray → LogArgPos (declamp t)
             → LogArgPosOn (Icc a b) → enc_combinedBound → explicit interval-free bound
             → max over finitely many variants → UniformZeroBoundFrom
             → eventual non-vanishing
```

`eventually_nonzero_of_nonvanishing_of_hard` states the whole thing: **on the existing obligation, a
tree that never vanishes identically on a far-out interval is eventually non-vanishing outright.**

What that does *not* do is close `SignHardCase`, and the reason is worth being exact about. The
non-vanishing hypothesis is supplied per tree, and for the hard node it is precisely the statement the
obligation is stuck on. The arc has moved the difficulty, not dissolved it: the residue is now a
single clean condition on one function rather than a demand for zero-counting machinery, and it sits
where a Hardy-field or o-minimality argument would apply.

`SignHardCase` stays `open`, 18 rows unchanged, nothing registered.

Gates: build **741 jobs**, aggregator **738 of 1044**, consistency PASS, claims 422, obligations 18
rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness
audit 36.

## [Unreleased] — 2026-08-25 (cz)

### A variant can be identically zero while its node never vanishes

`(cy)` shipped the finiteness reduction and flagged one thing as undecided: whether some variant of a
node can be eventually zero while the node itself is not. It can, and here it is.

```
witInner = eml (const 0) (const 1)              value  exp 0 − log 1       = 1
witB     = eml witInner (const (exp 1))         value  exp 1 − log (exp 1) = exp 1 − 1
witT     = eml (const 0) witB                   value  1 − log (exp 1 − 1)   ≠ 0
witV     = eml (const 0) (eml witInner (const 1))
                                                value  1 − log (exp 1)     = 0
```

`witV` is `witT` with `witB`'s right child clamped to `const 1`, so `witV_mem_variants` puts it in the
list. `witV_eval_zero` — identically `0`. `witT_eval_ne_zero` — never `0`, because
`log (exp 1 − 1) = 1` would force `exp 1 − 1 = exp 1`, i.e. `0 = 1`.

> **`variant_can_be_evZero`** — `∃ t v, v ∈ declampVariants t ∧ EvZeroF v.eval ∧ ¬ EvZeroF t.eval`

So a node's non-vanishing does **not** transfer to its variants. That closes the door `(cy)` left ajar:
a per-variant demand cannot be conditioned on the node alone.

### The consequence lands on `(cy)`'s own corollary

`variantBounds_hypothesis_unsatisfiable` — there is **no** `F` giving
`UniformZeroBoundFrom v.eval 1 (F v)` for every `v ∈ declampVariants witT`, because it would have to
bound `witV`, and an identically-zero function is not eventually non-vanishing. The all-variants form
shipped in `(cy)` is a true theorem with a hypothesis nothing can supply for such trees.

**Reachability is exactly what separates the two.** `witV` arises only by clamping at a node whose log
argument is the constant `exp 1 > 0` — a node `declamp` never clamps. So the identically-zero variant
is *in the list* but is *never produced*.

`uniformZeroBoundFrom_of_reachableBounds` is therefore now the primary statement: it demands bounds
only on trees `declamp` really produces,

```
hF : ∀ a b, X₀ ≤ a → a < b → UniformZeroBoundFrom (declamp t a b).eval X₀ (F (declamp t a b))
```

and still concludes one `N` for the whole ray, because `declamp t a b` is always *in* the finite list
even though not everything in the list is reachable. The `(cy)` corollary is kept and derived from it,
with its docstring now saying when it is useless.

### What this run of the pattern cost, and what it should cost next time

Fourth time this arc a demand had to be conditioned, and the first time the *conditioning I had
already applied* turned out to be insufficient rather than absent. `(cv)`'s lesson was "condition on
`¬ EvZeroF`"; the refinement is that **the condition has to sit on the object the hypothesis
quantifies over**, not on a related one. Conditioning the node says nothing about its variants,
because a variant is a different function.

The general form: when a hypothesis ranges over derived objects, check satisfiability *for the derived
objects*, not for the thing they were derived from.

### Scope

`SignHardCase` stays `open`, 18 rows unchanged, nothing registered. The remaining input is unchanged
in substance — per-interval bounds on the trees `declamp` actually produces — but is now stated
against the right set.

Gates: build **740 jobs**, aggregator 737 of 1043, consistency PASS, claims 422, obligations 18 rows,
discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness audit
36. `variant_can_be_evZero` cites 29 axioms; no footprint cites `sorryAx`,
`zero_count_bound_classical`, `analytic_finite_zeros`, `Khovanskii`, `Fbasis` or `rolle`.

## [Unreleased] — 2026-08-25 (cy)

> **ANSWERED IN `(cz)` BELOW.** The question this entry leaves open — whether a variant can be
> eventually zero while its node is not — is settled **yes**, by an explicit tree. The
> consequence is that `uniformZeroBoundFrom_of_variantBounds`'s hypothesis is *unsatisfiable*
> for some trees; use `uniformZeroBoundFrom_of_reachableBounds` instead.

### `EMLDeclampUniform` — the tree varies, the maximum does not

`(cx)` closed the coherence gap and left one objection: `declamp t a b` is a **different tree per
interval**, so a zero count taken through it is per-interval and cannot feed
`eventually_nonzero_of_uniformZeroBoundFrom`, which needs one `N` for every interval beyond a ray.

The variation is bounded. `declamp` only ever replaces a right child by `const 1`, so every tree it
can produce lies in a list computed from `t` alone:

```
declampVariants (.eml t1 t2) =
  (declampVariants t1).flatMap fun v1 =>
    (declampVariants t2).map (fun v2 => .eml v1 v2) ++ [.eml v1 (.const 1)]
```

`declamp_mem_variants` proves membership for every `(a,b)` — 10 axioms. So a bound **per variant**
gives a bound for `t`: on each interval the zeros of `t` are the zeros of `declamp t a b` (they agree
there, by `declamp_eval`), that tree is one of finitely many, and the maximum over the list serves
every interval at or beyond the ray. `uniformZeroBoundFrom_of_variantBounds`, 18 axioms.

`uniformZeroBoundFrom_of_evSign_variantBounds` discharges the stability hypothesis from
sign-definiteness at every node — the form the depth induction already supplies — joining the ray
`logArgStable_of_evSign` produces with the one the bounds come on, via the new
`uniformZeroBoundFrom_mono`.

So the interval-dependence is real and harmless: **the tree changes, the maximum does not.**

### Deliberately a reduction, not an obligation

No `Prop` is registered here and the per-variant demand is **not** promoted, because the naive form
is false and the module proves it so.

> **`not_all_variants_bounded`** — it is not the case that every variant of every tree admits a
> uniform bound on some ray.

Same witness as `(cv)`: for `B := expExpTree A` the node `eml A B` has value identically `0`; nothing
in it is clamped, so it is its own variant (`declamp_eq_self_of_logArgPos`); and an identically-zero
function is not eventually non-vanishing, so by `eventually_nonzero_of_uniformZeroBoundFrom` it admits
no bound on any ray. Node-level `¬ EvZeroF` conditioning — which `SignHardUniformZeroBound` already
carries — excludes exactly that witness.

**What is not settled**, and is the reason this stops at a reduction: whether some *other* variant can
be eventually zero while the node itself is not. A variant is a genuinely different function from `t`
— they agree only on the interval whose clamping pattern selected it — so the node's non-vanishing
does not transfer to its variants for free. Promoting the per-variant demand to an obligation before
deciding that would be stating something possibly vacuous, which is the step `(cv)` had to retract.

Discrimination the other way: `variantBounds_specimen` fires the reduction on `var`, whose single
variant is itself and which has no zeros at or beyond `1`. A reduction that only ever applied to
degenerate trees would prove nothing.

### Where the route stands

```
SignHardCase → EvSign everywhere → LogArgStable on a ray → LogArgPos (declamp t)
             → coherent, analytic Pfaffian encoding                      (cx)
             → per-variant zero bounds → one uniform bound for t         (cy)
             → eventual non-vanishing → SignHardNonzeroOrClamped → SignHardCase
```

Every arrow is a theorem except the per-variant bounds, which nothing supplies. That is the whole
remaining input, and it is now a statement about **finitely many fixed trees per node** rather than
about a tree that changes with the interval.

`SignHardCase` stays `open`, 18 rows unchanged, nothing registered.

Gates: build **740 jobs**, aggregator **737 of 1043**, consistency PASS, claims 422, obligations 18
rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness
audit 36. No footprint cites `sorryAx`, `zero_count_bound_classical`, `analytic_finite_zeros`,
`Khovanskii`, `Fbasis` or `rolle`.

## [Unreleased] — 2026-08-25 (cx)

### `EMLDeclampEncoder` — rewrite the tree, not the encoder

`(cw)` located the live mismatch: `enc_isCoherentOn` needs `LogArgPos` — the log argument **positive**
at every node — while the depth induction produces *positive or clamped*. This closes it, and the
closure is smaller than the gap looked.

**The clamped branch has no logarithm in it.** `log y = 0` for `y ≤ 0`, so a clamped `eml t1 t2`
evaluates to `exp (t1 x)` — and `exp ∘ t1` is itself an EML node with a *positive* argument,
`eml t1 (const 1)`, because `log 1 = 0` (`expTree_eval`, in the corpus since `(cs)`). So the node the
encoder cannot accept computes a function the encoder accepts in a different spelling.

`declamp t a b` performs that spelling change: replace every clamped node's right child by `const 1`.

```
declamp_eval        : LogArgStable t a b → ∀ x ∈ (a,b), (declamp t a b).eval x = t.eval x
declamp_logArgPos   : LogArgStable t a b → LogArgPos (declamp t a b) a b
```

The first is where the work is — on the clamped branch both sides reduce to `exp (t1.eval x)`, one via
`log_nonpos`, the other via `log_one`. The second is then immediate: kept nodes keep a positive
argument (their values are unchanged), rewritten nodes have argument `1`.

`enc_isCoherentOn` applies unchanged. **No change to the encoder, and no new axioms** —
`declamp_eval` cites 18, `logArgStable_of_evSign` 14.

### The hypothesis is exactly what the induction produces

```
LogArgStable (.eml t1 t2) a b := LogArgStable t1 a b ∧ LogArgStable t2 a b ∧
                                 ((∀ x ∈ (a,b), 0 < t2.eval x) ∨ (∀ x ∈ (a,b), t2.eval x ≤ 0))
```

`LogArgPos` with each node's positivity replaced by the **disjunction** — the same move `(cu)` made
for continuity, now made for coherence. `logArgStable_of_logArgPos` records that it is genuinely
weaker, and `logArgStable_of_evSign` supplies it on a ray from `EvSign` at every node, by structural
induction with the three rays joined at each step.

Note what it is **not**: not `EMLNoCrossingAt`. A node whose argument sits at exactly `0` throughout
is stable — it takes the non-positive branch and `declamp` sends it to `const 1`. The condition rules
out *crossings inside the interval*, not zeros. That is the third time in this arc the totalisation
has turned a rejected case into a free one.

### The chain, end to end

```
SignHardCase → ∀ t, EvSign t.eval        (evSign_of_hard)
             → LogArgStable t on a ray    (logArgStable_of_evSign)
             → LogArgPos (declamp t) ∧ same values on (a,b)
             → enc (declamp t) coherent on (a,b)     (enc_declamp_isCoherentOn)
```

`eventually_coherent_encoding_of_hard` states it in one theorem: **on the existing obligation, every
EML tree is eventually computed by a tree whose Pfaffian encoding is coherent — hence analytic — on
every interval far enough out.** That is what the log-Khovanskii arc consumes.
`eventually_coherent_encoding_of_uniformBounds` is the same on the zero-control obligation.

### What it does not close, stated precisely

`declamp` depends on `(a,b)`: it is a **different tree per interval**, chosen by a `Classical` test at
each node. Harmless for coherence on a fixed interval, which is all `enc_isCoherentOn` asks — but it
means no single tree serves every interval, so a zero count obtained this way is *per interval* and
still has to be made uniform before `eventually_nonzero_of_uniformZeroBoundFrom` can consume it.

That is now the whole remaining gap on this route, and it is a uniformity question rather than a
representability one: the tree varies, but only across finitely many shapes (`declamp` only ever
replaces right children by `const 1`, so every variant is a sub-selection of the same node set).
Whether that finiteness gives a uniform bound is not proved here and is not assumed.

`SignHardCase` stays `open`, 18 rows unchanged, nothing registered, and no `UniformZeroBound` of
either strength is supplied for any EML node value.

Gates: build **739 jobs**, aggregator **736 of 1042**, consistency PASS, claims 422, obligations 18
rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness
audit 36. No footprint cites `sorryAx`, `zero_count_bound_classical`, `analytic_finite_zeros`,
`Khovanskii`, `Fbasis` or `rolle`.

## [Unreleased] — 2026-08-25 (cw)

### The bridge's hypothesis, at its point of use — and two corrections

Two things happened while trying to take the next step named at the end of `(cv)`. One is a small
theorem. The other is that **the step named there was already done**, and so was the one named after
it. Both were asserted from memory of the corpus rather than checked against it.

### Correction 1 — the quantifier reordering is not outstanding

`(cv)` closed with: *"the Khovanskii statements would first have to quantify `N` before the
interval"*. That reordering was performed in the `(cs)` arc.
`MachLib.ChainExp2Capstone.chain2_khovanskii_bound_uniform` already reads

```
∃ N : Nat, ∀ (a b : Real), a < b → ∀ zeros, … → zeros.length ≤ N
```

— `N` in front of `a b`, exactly the shape `eventually_nonzero_of_uniformZeroBound` consumes. The
note quoted in `EMLZeroBoundRay`'s docstring predates that module and is stale where it is quoted.

### Correction 2 — the `EMLTree → chain` encoder exists

`(cv)`'s successor claim, that no encoder from `EMLTree` to a Pfaffian chain existed, is also wrong.
`MachLib.EMLEncoder` ships `enc` (state-threaded via `chainExtend`), `enc_eval` (the barrier
evaluates to `t.eval`) and `enc_isCoherentOn` (the produced chain is coherent on `(a,b)`), with no
new axioms.

Both corrections came from grepping the corpus before building on the claim. Neither would have been
caught by any gate: a stale "what remains" sentence in a changelog is not a proposition anything
checks. The pattern is the same one that produced the vacuous obligation in `(cv)` — reasoning from a
remembered state of the corpus instead of the corpus.

### What actually remains, checked

`enc_isCoherentOn` is gated on `LogArgPos`:

```
LogArgPos (.eml t1 t2) a b := LogArgPos t1 a b ∧ LogArgPos t2 a b ∧ (∀ x ∈ (a,b), 0 < t2.eval x)
```

Positivity of the log argument at **every** node, throughout the interval. That is the same demand
`EMLNoCrossingAt` made and that `(cu)` replaced for the continuity route — and the sign induction
does **not** supply it. `evSignCont_of_cts` gives each node's argument *positive or clamped*; on the
clamped branch the argument is `≤ 0`, `LogArgPos` fails, and the node's value is `exp (A x)` with no
real logarithm in it at all.

So the live mismatch is neither the reordering nor the encoder. It is that **the encoder wants
positivity where the induction produces a disjunction** — the same tension `(cu)` resolved for
continuity, unresolved for coherence. A clamped-aware encoder (encode a clamped node as its `exp`
factor, since that is what it evaluates to) is the shape that would close it. Not attempted here.

### The small theorem: `UniformZeroBoundFrom`

`UniformZeroBound f N` demands the bound on **every** interval.
`eventually_nonzero_of_uniformZeroBound` inspects exactly one, `(pickZero 0 − 1, pickZero N + 1)`,
and the milking argument may place it as far out as it likes, because the zeros it draws on are
cofinal by construction. Intervals near or below any chosen base are never consulted.

```
UniformZeroBoundFrom f R N := ∀ a b, R ≤ a → a < b → ∀ zeros, … → zeros.length ≤ N
```

`eventually_nonzero_of_uniformZeroBoundFrom` proves the bridge from it, seeding the milking at
`R + 1` — **not `R`**, because the interval starts one unit *beneath* its first zero, the same
closed-ray/two-sided off-by-one `ray_shift_nbhd` handles in the sign arc. Seeding required threading
an explicit seed through the private `pickZero`/`zlist` machinery; the change is mechanical and the
seed defaults to the old behaviour at `R = 1`.

`uniformZeroBoundFrom_of_uniformZeroBound` recovers the weaker form from the original and
`eventually_nonzero_of_uniformZeroBound` is now a **corollary** rather than a second proof — the
weakening subsumes its predecessor, as `singleExp_khovanskii_bound_at_reduct` did. Footprint
unchanged at 22 axioms, and the registered claim on it still resolves.

### The fourth instance of one pattern

| hypothesis | stated over | used at |
| --- | --- | --- |
| `IsKhovanskiiReducible` side condition | the whole reduction closure | one reduct, `(cs)` |
| chain-2 bound's `N` | after the interval | one `N` for all, `(cs)` |
| `SignHardCase`'s obligation | every tree pair | one node, `(cu)` |
| `UniformZeroBound` | every interval | one far-out interval, here |

`SignHardUniformZeroBound` now demands only `UniformZeroBoundFrom … X₀ …`, on the ray its own
positivity hypothesis controls. Asking for zero control below `X₀` was asking the producer for
information the statement never gives it.

### Scope

`SignHardCase` stays `open`, 18 rows unchanged, nothing registered. No `UniformZeroBound` — of either
strength — is supplied for any EML node value.

Gates: build **738 jobs**, aggregator 735 of 1041, consistency PASS, claims 422, obligations 18 rows,
discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness audit
36. No new footprint cites `sorryAx`, `zero_count_bound_classical`, `analytic_finite_zeros`,
`Khovanskii`, `Fbasis` or `rolle`.

## [Unreleased] — 2026-08-25 (cv)

### `EMLSignZeroProducer` — the producer wired, and the obligation it kills on the way

Step six: connect the corpus's zero-counting bridge to the hard node. It connects — and in the
process **refutes `SignHardNonzero`**, the pure-non-vanishing obligation `(cu)` shipped one commit
earlier under all nine green gates.

### The counterexample

`exp ∘ exp ∘ t` is again an EML tree — `expExpTree_eval`, already in `EMLSignReduction` since the
`(cs)` arc. So for **any** left child `A`, taking `B := expExpTree A` gives

```
B.eval x = exp (exp (A.eval x)) > 0                    for every x
exp (A.eval x) − log (B.eval x) = 0                    for every x
```

The positivity hypothesis holds on the whole line and the node value is *identically zero*. A
function that is everywhere zero is never eventually non-vanishing. `not_signHardNonzero` closes it
in 23 axioms.

So `signHardCts_of_nonzero`, `evSign_of_nonzero`, `evCont_of_nonzero` and
`nonzeroOrClamped_of_nonzero` are **vacuous** — true, and useless. They are kept as the record of the
step with their docstrings corrected in place, and `(cu)` now carries a correction banner.

**This is the failure mode `EMLZeroBoundRay` had already documented**, in its own words: the
unconditioned form of `bipolyNoOscillation`'s hypothesis is false because `N = []` has an
identically-zero germ and therefore no bound. The same sentence, transposed to EML trees, was sitting
in the file the producer had to import. The lesson generalises past both: **an obligation demanding
non-vanishing must be conditioned on not being eventually zero**, or its identically-zero member
refutes it.

Worth being exact about what `(cu)` got wrong. It reasoned about the *direction* of the implication
and stopped there. Direction is not satisfiability: a false sufficient condition is not a stronger
obligation, it is no obligation. Checking that `SignHardCase ↛ SignHardNonzero` is not a substitute
for instantiating `SignHardNonzero`.

### What the disjunct was for

`SignHardNonzeroOrClamped` is untouched. The identically-zero germ satisfies its **second** disjunct
(`≤ 0` on a ray) instead of falsifying it — `expExpTree_witness_is_clamped` records that. The disjunct
that made the form debt-neutral is the same disjunct that absorbs the counterexample; it was
load-bearing, not decorative.

### The chain, closed

```
SignHardUniformZeroBound → SignHardNonzeroOrClamped → SignHardCts → ∀ t, EvSign t.eval ∧ EvCont t.eval
```

`SignHardUniformZeroBound` demands a zero bound uniform **in the interval** (`K` before `a b`) at the
hard node, conditioned on `¬ EvZeroF` — the same shape *and the same conditioning* as
`bipolyNoOscillation_of_uniformBounds`. `signHardNonzeroOrClamped_of_uniformBounds` sends eventually
zero germs to the clamped disjunct and everything else through
`eventually_nonzero_of_uniformZeroBound`.

**The shared frontier is now a shared lemma.** `oneQueryDichotomy_of_uniformBounds` and
`evSign_of_uniformBounds` call the same bridge, `eventually_nonzero_of_uniformZeroBound` — pure order
and combinatorics, no analyticity, no Pfaffian chain. Not an analogy between two prose descriptions.

### Two specimens, because the repair could have emptied the statement

* `counterexample_is_conditioned_out` — the refuting witness *is* `EvZeroF`, so
  `SignHardUniformZeroBound` demands nothing there. That is why §1 does not refute it too.
* `signHardUniformZeroBound_specimen` — `A = const 0`, `B = const 1` has `B > 0`, is **not**
  eventually zero, and carries the uniform bound `0`. So there is a pair where the demand is real and
  satisfiable, and the conditioning repaired the statement rather than vacating it.

### Scope

No `UniformZeroBound` for any EML node value is supplied here; that is the open work, and
`EMLZeroBoundRay`'s note applies verbatim — the Khovanskii statements would first have to quantify
`N` **before** the interval. `SignHardCase` stays `open`, 18 rows unchanged, nothing registered.

Two claims registered (**422**, was 420), binding this entry's prose to the artefacts:
`not_signHardNonzero` and `continuousAt_log_comp_of_nonpos_nbhd` — the two results here that carry no
hypothesis or are already instantiated. The conditional capstones (`evSign_of_uniformBounds`,
`evCont_of_hard`, `signHardNonzeroOrClamped_of_uniformBounds`) are deliberately **not** registered:
each takes a hypothesis nothing in the corpus supplies, which is exactly what the witness audit
exists to report, and padding a pinned set with known-uninstantiated capstones would weaken it.

Gates: build **738 jobs**, aggregator **735 of 1041**, consistency PASS, claims **422**, obligations
18 rows (`SignHardCase` open), discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit
1 allowlisted, witness audit 36 (pinned set unchanged). New footprints cite no `sorryAx`, `zero_count_bound_classical`,
`analytic_finite_zeros`, `Khovanskii`, `Fbasis` or `rolle`; `not_signHardNonzero` needs 23 axioms.

## [Unreleased] — 2026-08-25 (cu)

> **CORRECTED BY `(cv)` BELOW.** This entry reads `SignHardNonzero` as a *sufficient*
> condition, stronger than `SignHardCase`. The direction was right; the value was not.
> `SignHardNonzero` is **false** — `not_signHardNonzero` refutes it — so every theorem here
> that assumes it is vacuous. `SignHardNonzeroOrClamped`, `evCont_of_hard` and the skeleton
> are unaffected. Read `(cv)` before using anything in the paragraph beginning *"It is
> strictly a sufficient condition"*.

### `EMLEventualContinuity` — the induction manufactures its own continuity

The previous entry left one question: read `evSign_of_hard`'s use site and ask what eventual
sign/zero/branch information the depth induction *already* has for every nested log argument. The
answer is the middle of the three outcomes — enough for a **weaker continuity lemma** than
`EMLNoCrossingAt`, not enough to build the ray at the call site unchanged.

**What is actually in scope at the invocation.** At `EMLDepthTameness.lean:2643` the context holds
exactly one verdict, `ihB : EvSign B.eval` — the top-level log argument — and `ihA` is bound to `_`.
Nothing nested, in either child. That is forced by the motive: `EvSign t.eval` is a statement about
the root value, so a structural IH cannot carry anything about a child's interior.

**But the nested verdicts are not missing — they are produced at their own nodes.** Every nested log
argument is the right child of some `eml a b` the same induction visits, and there its own `ihB` *is*
the branch verdict for it. Nothing has to be transported to the root. So continuity can ride along as
a second conjunct of the induction's own conclusion, proved from immediate-children hypotheses alone.

### The two branches are continuous for different reasons

| branch | why `log ∘ B` is continuous | `EMLNoCrossingAt` |
| --- | --- | --- |
| `0 < B.eval` on the ray | `log` is continuous at positive points; the verdict is used at the single point `x` | implied (`> 0` gives `≠ 0`) |
| `B.eval ≤ 0` on the ray | `log ∘ B ≡ 0` there, hence *locally constant*; the verdict is used on a whole ball | **fails** at any `B.eval x = 0` |

The clamped row is the one that matters. Totalisation makes `log ∘ B` constant, so exact zeros of `B`
are harmless, and a condition phrased as non-vanishing rejects a case that is perfectly well behaved.
`continuousAt_log_comp_of_nonpos_nbhd` is the whole of the new analysis and its footprint is 17 base
`Real` axioms — **no differentiability of `g` anywhere**.

There is no derivative twin, and the reason is structural: `MachLib.Real.HasDerivAt` is an opaque
`axiom` with no local-congruence rule, so `HasDerivAt (fun _ => 0) 0 x` cannot be transferred across
an agreement neighbourhood. The existing derivative-based node lemma
`eml_hasDerivAt_away_from_crossing` therefore *cannot* serve the clamped branch at all. `EvCont`
carries `ContinuousAt` because that is the only thing available, not merely the cheaper option.

### The endpoint shift, kept explicit

`EvSign` and `EvCont` rays are closed (`X₀ ≤ x`); `ContinuousAt` is two-sided. At `x = X₀` the clamped
branch's local-constancy argument has no left neighbourhood and is false as stated. `ray_shift_nbhd`
states the fix once — the radius-`1` ball about any `x ≥ X₀ + 1` stays inside `[X₀, ∞)` — and the node
lemma's conclusion is a ray at `X + 1`. Named rather than inlined; a silently dropped endpoint is a
failure mode this corpus has already paid for.

### What the skeleton buys, and what it costs

`evSignCont_of_cts` advances `EvSign` and `EvCont` together. Its hypothesis `SignHardCts` is
`SignHardCase` **plus** a continuity hypothesis at the node — more hypotheses, same conclusion, so it
is *implied by* `SignHardCase` (`signHardCts_of_hard`) and nothing is strengthened to route through
it. `ihA`, discarded in `evSign_of_hard` because the left child's sign is genuinely irrelevant, is
used here for the left child's **continuity**.

Immediate consequence, on the *existing* obligation with nothing added:

> **`evCont_of_hard : SignHardCase → ∀ t : EMLTree, EvCont t.eval`**

Continuity was never a second mathematical frontier. It is internal bookkeeping, and the corpus can
now say so with a theorem.

### The zero-control instance, and an asymmetry worth stating plainly

`SignHardNonzero` — pure eventual non-vanishing, the shape a zero-counting engine produces and the
same shape `OneQueryDichotomy` needs — feeds the skeleton through
`evSign_of_continuous_nonzero_on_ray`, giving

> **`evSign_of_nonzero : SignHardNonzero → ∀ t : EMLTree, EvSign t.eval`**

the drop-in analogue of `evSign_of_hard` with the sign obligation replaced by a zero-control one.

**It is strictly a sufficient condition, not a reduction.** `SignHardCase` does **not** give
`SignHardNonzero` back: `EvSign`'s second disjunct is `≤ 0`, which tolerates a function with
infinitely many zeros. So any zero-control route to `SignHardCase` *over-delivers*, and adopting
`SignHardNonzero` as the obligation would **enlarge** the debt rather than shrink it. That is the
opposite of the `signHardCase_iff_compareExpExpPos` case, where the residue was equivalent; here it is
stronger, which is worse in debt terms, and the row must not move on the strength of it.

`SignHardNonzeroOrClamped` is the debt-neutral form — the same statement with the clamped case
restored as a disjunct. It feeds the skeleton (`signHardCts_of_nonzeroOrClamped`) *and* is implied by
`SignHardCase` (`nonzeroOrClamped_of_hard`), so it neither strengthens nor weakens the obligation. It
is the honest spelling of "all that is missing is zero control, on the branch where zero control is
what is missing".

### Ledger

**No row moves. `SignHardCase` stays `open`, 18 rows unchanged**, and the gate confirms it: *"ok
SignHardCase: open, no theorem concludes it"*. Neither `SignHardCts`, `SignHardNonzero` nor
`SignHardNonzeroOrClamped` is registered — the producer is not connected, and a sufficient condition
with no producer is not progress in debt terms.

Deliberately, **no theorem in this module concludes `SignHardCase`** — and both halves of that
sentence were checked rather than assumed. The theorem *is* writable: `SignHardNonzero → SignHardCase`
follows from `evCont_of_nonzero` applied to `A` and `B`, then `evCont_eml_of_evSign_right`, then
`signHardCts_of_nonzero`; it elaborates clean (kept out of the corpus, not out of reach). And it
*would* have fired: feeding that signature to `dischargers_of` returns
`['probe_signHardCase_of_nonzero']` and `check_rows` reports **`STALE SignHardCase: marked open but
discharged by …`**, because binder-stripping removes only binders of the obligation's *own* type — a
consumer of `SignHardNonzero` concluding `SignHardCase` passes straight through. The three shipped
shapes (`… : SignHardCts`, `… : ∀ t, EvSign t.eval`, `… : SignHardNonzeroOrClamped`) return `bad = 0`
against the same row. The capstones are stated at their real use site (`∀ t, EvSign t.eval`), which is
where `evSign_of_hard` states its own.

### What changed in the dependency graph

Before: two open mathematical frontiers, sign-definiteness and zero-counting, with continuity an
unresolved third thing. After: one zero-counting frontier plus continuity as internal plumbing —

```
eventual non-vanishing ──┬── OneQueryDichotomy
                         └── + IVT + (manufactured) eventual continuity ── SignHardCase
```

with the caveat above that the left edge into `SignHardCase` is a sufficient condition, not an
equivalence, unless it is taken in the `…OrClamped` form.

Gates: build **737 jobs**, aggregator **734 of 1040**, consistency PASS, claims 420, obligations 18
rows (`SignHardCase` open), discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1
allowlisted, witness audit 36 (pinned set). New-module footprints cite no `sorryAx`, no
`zero_count_bound_classical`, no `analytic_finite_zeros`, no `Khovanskii`, no `Fbasis`, no `rolle`.

## [Unreleased] — 2026-08-25 (ct)

### `EMLSignFromNonzero` — a general topology bridge, and the second ingredient the pipeline needs

`EMLZeroBoundRay` turns a uniform zero bound into **eventual non-vanishing**. This turns eventual
non-vanishing into **eventual constant sign** — what `SignHardCase` asks for.

```
evSign_of_continuous_nonzero_on_ray {f : Real → Real} {R : Real}
  (hR : 1 ≤ R) (hne : ∀ x, R ≤ x → f x ≠ 0) (hcont : ∀ x, R ≤ x → ContinuousAt f x) : EvSign f
```

The mathematics is one line: a continuous function that took both signs would have to cross zero.

**Deliberately generic.** The statement mentions no EML tree, no Pfaffian chain, no `Fbasis`, and no
zero-counting theorem; the footprint cites no `Khovanskii`, no `zero_count_bound_classical`, no
`analytic_finite_zeros`, and no `Fbasis`. It decouples *how* non-vanishing was obtained from *what*
it buys, so any future zero-counting engine can feed it while none appears in its statement. Worth
having as a general topology bridge in this corpus regardless of what consumes it.

Two mechanical details: `EvSign`'s second disjunct is `f x ≤ 0` rather than `< 0`, so the strictly
negative case lands in it with no packaging work; and `intermediate_value` has a single orientation
(`f a < 0` then `0 < f b`), so rather than assume a mirrored version exists, the positive case
applies the same theorem to `fun x => -(f x)` through `continuousAt_neg`.

### The specialization does NOT close, and that is the informative half

Continuity of `EMLTree.eval` comes from `eml_continuousAt_of_no_crossing`, gated on

```
EMLNoCrossingAt (.eml t1 t2) x := EMLNoCrossingAt t1 x ∧ EMLNoCrossingAt t2 x ∧ t2.eval x ≠ 0
```

which is **recursive over the whole tree** — every log argument at every node, nested arbitrarily
deep in both `A` and `B`. `SignHardCase` supplies `0 < B.eval x`: the **top-level** log argument and
nothing else.

**Stated carefully:** this does *not* show `SignHardCase` is under-hypothesised. It shows it is
under-hypothesised **for the `EMLNoCrossingAt` → continuity → IVT route**. `EMLNoCrossingAt` is
plausibly stronger than continuity actually requires — a log argument that is eventually *clamped*
sits stably on the totalised branch, and demanding literal non-vanishing there would reject cases
that are perfectly well behaved on the ray. So it should not be promoted into the public statement
of the obligation, and no obligation was modified here.

### The second ingredient, and why it is not optional

The generic bridge makes a failure mode explicit that was easy to overlook: **a jump can change sign
without ever taking the value zero.** So eventual non-vanishing alone cannot deliver `EvSign` for an
arbitrary function — zero-counting is genuinely insufficient, and some form of eventual continuity or
branch stability is *mathematically necessary* rather than merely convenient.

The unified pipeline is therefore two ingredients, not one:

```
uniform zero control  +  eventual continuity / branch stability  ⟹  EvSign
```

That is sharper than the position one step earlier, where continuity looked like plumbing.

### The next question, scoped

Read `evSign_of_hard`'s use site and ask what eventual sign/zero/branch information the depth
induction *already* has for every nested log argument at the point `SignHardCase` is invoked. Three
outcomes: the induction already knows enough (build the ray at the call site, change nothing); it
knows enough for a **weaker continuity lemma** than `EMLNoCrossingAt` (eventual branch stability ⟹
eventual continuity — closer to the totalised log's actual semantics); or it knows nothing about
nested crossings, in which case a new induction invariant is the honest answer. **Do not strengthen
`SignHardCase` before that inspection.**

Gates: build **736 jobs**, aggregator **733 of 1039**, consistency PASS, claims **420**, obligations
18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted,
witness audit 36 (pinned set).

## [Unreleased] — 2026-08-25 (cs)

### Coordinate 3 — the reducibility side condition, at its point of use

The chain-2 bound's antecedent quantifies over **every** 0-chain reduct reachable by
`IsKhovanskiiReducible` — a four-constructor inductive (`refl`/`reduce`/`drop`/`trim`) of unbounded
depth. Discharging it for a concrete `p` would mean reasoning about the entire reduction closure.

It is applied **exactly once**. `se_reduces p` produces one specific `(g, k)`, and the proof calls
`terminal_nonzero g k hg0 hwit` at that pair and nowhere else.

```
singleExp_khovanskii_bound_at_reduct (p : MultiPoly 1) :
  ∃ g k, g.n = 0 ∧ IsKhovanskiiReducible ⟨1, SingleExpChain, p⟩ g k ∧
    ((∃ x, g.eval x ≠ 0) → ∃ N, ∀ a b, a < b → …)
```

Exposing the reduct turns the obligation from *"reason about the reduction closure"* into
**"exhibit one `x` where one polynomial is nonzero"**.

`singleExp_khovanskii_bound_uniform_of_at_reduct` recovers the strong form as an instance, so this
**subsumes** rather than sits beside — the same discipline `(cb)`–`(cd)` used with `Pr := True`, and
for the same reason: a weakening that leaves its predecessor derivable has nothing to reconcile.

### The third instance of one pattern

This is now the **third** hypothesis in this corpus found to be quantified far beyond its use:

| hypothesis | stated over | used at |
| --- | --- | --- |
| `hmin` (`S > 0` arc) | all germ-coefficient lists | the derived relation and its `dropLast`s |
| `hchar` (pole layer) | all `r : Nat` | successors only — index `0` never consumed |
| `terminal_nonzero` | the whole reduction closure | one reduct from `se_reduces` |

Two of the three were actively harmful — `hchar`'s extra index made the flagship **vacuous**, and
`hmin`'s extra scope capped the arc at `m = 0`. The third merely made an obligation look
intractable. Worth searching for deliberately rather than stumbling on, though that is its own
exercise.

### No trust cost

Cites no `zero_count_bound_classical` and no `analytic_finite_zeros`.

### Where the three coordinates now stand

| coordinate | before | after |
| --- | --- | --- |
| quantifier order | `N` bound after the interval | **closed** (cr) |
| chain shape | totalised `log`, wrong chain | **open**, structurally |
| reducibility | ∀ over the reduction closure | **one non-vanishing witness** |

`OneQueryDichotomy` remains **open**. The remaining obstacle is the one that is not bookkeeping: the
totalised `log` makes the germ **change form at a sign boundary** — Pfaffian where `S > 0`,
identically `exp(S)` where `S ≤ 0` — while Pfaffian chain machinery assumes a fixed chain on a fixed
domain. The ray must be split *before* any chain argument, using the regimes `EMLGermSign` already
establishes.

Gates: build **735 jobs**, aggregator **732 of 1038**, consistency PASS, claims **419**, obligations
18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted,
witness audit 36 (pinned set).

## [Unreleased] — 2026-08-25 (cr)

### `ChainExp2Uniform` — the quantifier reordering, and one of three coordinates closed

(cq) measured `OneQueryDichotomy`'s distance to closure in three coordinates: **quantifier order**,
**chain shape**, **reducibility transport**. This closes the first.

```
chain2_khovanskii_bound_uniform (p : MultiPoly 2) :
  ∃ g k, degreeY g = 0 ∧
    (terminal-nonvanishing → ∃ N, ∀ (a b : Real), a < b → ∀ zeros, … → zeros.length ≤ N)
```

`N` now precedes the interval — the shape `eventually_nonzero_of_uniformZeroBound` consumes.

### It is a restatement, and establishing that was the work

The existing statements bind `N` *inside* `a b`, so they license only the weaker, interval-dependent
reading. Reading the construction shows the bound never depended on the interval. At the bottom of
the stack:

```
obtain ⟨g, k, hg0, hwit⟩ := se_reduces p
refine ⟨MultiPoly.degreeX g.poly + k, ?_⟩
```

`N = degreeX g.poly + k`, with `g`, `k` from `se_reduces p` — **a function of the polynomial alone**.
The interval enters only afterwards, to apply `khovanskii_bound_full`. One level up,
`chain2_reduces_to_y1free` already quantifies `a b` *inside* its conclusion. So each proof here is
the original with `intro a b hab` moved after the witness is supplied.

The bounds were uniform all along; the statements did not say so, and every downstream use inherited
the weaker reading.

### Why it was checked rather than asserted

"Khovanskii bounds are uniform in nature" is true, and is not a proof. Writing that sentence at the
start would have been correct and would have licensed nothing. The distance turned out to be one
`intro` — which is only learnable by reading the construction, not the intuition. Same discipline
that killed the growth-regime detour in (cp).

### No trust cost

`chain2_khovanskii_bound_uniform` cites **no `zero_count_bound_classical` and no
`analytic_finite_zeros`**, inheriting the unconditional route's footprint. Closing this coordinate
did not spend any of the axiom budget — which matters, because `analytic_finite_zeros_compact` sits
in the ledger's *disclosed-but-not-trusted* list, so a headline routed through it would fail the
`AxiomLedger` gate outright rather than merely being frowned upon.

### Scope, stated plainly

Chain-2 only. The terminal non-vanishing side condition is carried unchanged, not discharged. This
does **not** close `OneQueryDichotomy`: the remaining coordinates are **chain shape** — the germ
`N(x, F(P/Q))` involves `x`, `exp(S)` *and* a totalised `log(S)`, whose `log y = 0` for `y ≤ 0`
convention forces a sign split, so the germ is only Pfaffian on the ray where `S > 0` — and
**transporting reducibility** to the relevant `FCtx` expression. Both untouched.

Gates: build **735 jobs**, aggregator **732 of 1038**, consistency PASS, claims **417**, obligations
18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted,
witness audit 36 (pinned set).

## [Unreleased] — 2026-08-25 (cq)

### `EMLZeroBoundRay` — the missing bridge, and `OneQueryDichotomy`'s debt in one statement

(cp) established that `OneQueryDichotomy` is a **zero-counting** question, and that the corpus's
zero-counting arc has the wrong statement shape. This supplies the bridge and states the residue
exactly.

### The shape mismatch, precisely

`chain2_khovanskii_bound_unconditional` and its siblings read

```
∀ (a b : Real), a < b → … → ∃ N, ∀ zeros, zeros.Nodup →
  (∀ z ∈ zeros, a < z ∧ z < b ∧ f z = 0) → zeros.length ≤ N
```

`N` is quantified **inside** `a b`, so as written the bound may depend on the interval — and
`BipolyNoOscillation` needs non-vanishing on a **ray**. A per-interval bound does not give that:
zeros could accumulate towards infinity with finitely many in each compact piece.

### Uniformity is the entire difference

```
eventually_nonzero_of_uniformZeroBound : UniformZeroBound f N → ∃ Y, 1 ≤ Y ∧ ∀ x, Y ≤ x → f x ≠ 0
```

If one `N` works for *every* interval, a function that keeps returning to zero can be milked for
`N + 1` distinct zeros — and they all sit inside a single interval, contradicting the bound. The
proof builds that sequence explicitly (`pickZero`, strictly increasing by construction) and the
witness list by recursion, since `List.Nodup.map` does not exist without Mathlib.

**It is chain-independent.** The footprint cites **no `HasDerivAt`, no `Real.log`, no `Real.exp`** —
pure order and combinatorics, nothing about `f` beyond the bound. So it cannot be wrong for
chain-shape reasons, which is exactly the property wanted after (cp)'s regime-split misfire.

### The whole debt, in one statement

```
oneQueryDichotomy_of_uniformBounds :
  (∀ N P Q, ¬ EvZeroF (N(x,F(P/Q))) → ∃ K, UniformZeroBound (N(x,F(P/Q))) K)
    → OneQueryDichotomy, for every FCtx
```

So the residue is **one precisely-shaped antecedent**: for germs not eventually zero, a zero bound
with `K` quantified *before* the interval. That is one quantifier reordering away from what the
unconditional chain results already prove — a statement-level gap, not a gap in the mathematics,
since Khovanskii bounds are uniform in nature.

### Two vacuity traps, both avoided rather than discovered

**The naive composite is false.** *Every* such germ having a uniform bound fails immediately at
`N = []`, whose germ is identically zero and has no bound at all. Stated that way the theorem would
have been **vacuous** — the exact defect this session spent most of its length repairing elsewhere.
Conditioning on `¬ EvZeroF` is what makes the antecedent satisfiable: the germs that admit a bound
are precisely the ones not eventually zero.

**`UniformZeroBound` needed a firing specimen**, or the bridge could be a theorem about an empty
hypothesis. `uniformZeroBound_specimen` gives `x − 1` — one genuine zero, bound `1` — and
`specimen_eventually_nonzero` fires the bridge on it.

### Still open

`OneQueryDichotomy` remains **open**, and no `UniformZeroBound` is proved here for any germ of the
form `N(x, F(P/Q))`. What changed is that the debt is now a single named antecedent instead of "apply
Khovanskii somehow", and its distance from the existing results is measurable: a quantifier
reordering, a chain shape that includes a totalised `log`, and a reducibility side condition.

Gates: build **734 jobs**, aggregator **731 of 1037**, consistency PASS, claims **415**, obligations
18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted,
witness audit 36 (pinned set).

## [Unreleased] — 2026-08-25 (cp)

### CORRECTION — `OneQueryDichotomy` is zero-counting, not transcendence

(cm) and (cn) said the residue of `OneQueryDichotomy`, after the normal form, was "an
algebraic-relation question about `F ∘ (P/Q)` and nothing else". **That is wrong**, and the error was
mine in prose I had just published. Corrected in place in both the module docstring and the (cm)
entry, and recorded here rather than quietly edited away.

### The first correction was itself too weak

The obvious repair is "it is transcendence **plus** a finite-zeros statement", because the second
disjunct of `BipolyDichotomyAlong` is *eventual non-vanishing*. That is closer, and still wrong.

`EvZeroF f ∨ (eventually f ≠ 0)` has a **decidable first branch**. By excluded middle the entire
content sits in the second: *if `f` is not eventually zero then `f` is eventually nonzero* — no
infinite oscillation through zero. Transcendence, non-algebraicity and `Fbasis_not_algebraic` play
**no role in it whatsoever**.

```
bipolyDichotomy_iff_noOscillation : BipolyDichotomyAlong ↔ BipolyNoOscillation
```

Stated as an equivalence so the redirection is checkable rather than a matter of assertion.

### Why it was easy to get wrong

The level-0 analogue reads like an algebra theorem. `pev_dichotomy` concludes `EvZeroF ∨ EvDom`, and
`EvDom` sounds like "the leading coefficient wins". But what `EvDom` *buys* is eventual
non-vanishing, and a polynomial earns that from having **finitely many roots**. The level-1 statement
needs exactly that for `N(x, F(P/Q))`.

### What this changes about where the work goes

A three-regime split of the bivariate question by growth — `deg P > deg Q` routing to
`not_algebraic_of_dominates_exp`, `deg P < deg Q` to `no_rational_logarithm`, `deg P = deg Q` left
over — was drafted and **abandoned before being built**. Every engine in it is a transcendence
engine, and the obligation is not a transcendence statement.

`OneQueryDichotomy` belongs to the **zero-counting** arc: `AnalyticFiniteZeros`,
`AnalyticFiniteZerosReal`, `ExpRationalKhovanskii`, `InnerKhovanskiiExp`, `FiniteZeroPacket`. That is
a link between two arcs this project has been running separately, and it is worth more than the split
would have been.

### The habit that caught it

Checking that the four engines *existed* was not what saved this — they all do. What saved it was
checking the **model**: reading what `BipolyDichotomyAlong`'s second disjunct actually demands
instead of what its level-0 analogue's name suggests. A decomposition that is plausible, cites real
lemmas, and targets the wrong arc is not distinguishable from a correct one by any gate here.

Gates: build **733 jobs**, aggregator **730 of 1036**, consistency PASS, claims **412**, obligations
18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted,
witness audit 36 (pinned set).

## [Unreleased] — 2026-08-25 (co)

### `REDUCED` — a reduction may no longer read as a closure

Two obligations acquired clean equivalent forms in one day (`SignHardCase` → a growth comparison,
`OneQueryDichotomy` → bivariate vanishing) and **nothing in the claim registry distinguished that
from closing them**. A dashboard counting green claims would have read a reduction campaign as a
closure campaign. `REDUCED` is the state that keeps them apart, and check (H) gives it teeth:

* an **equivalence** whose conclusion mentions a **live** obligation must declare
  `epistemic_type: "REDUCED"`;
* a `REDUCED` claim must carry `reduces_to`, and that residue must actually occur in the cited
  theorem's statement — so "reduced to X" cannot name something the theorem never mentions.

`signHardCase_iff_compareExpExpPos`, `oneQueryDichotomy_divFree_of_bipoly` and
`oneQueryDichotomy_of_bipoly` are marked accordingly.

### The trigger is read from the ledger, and fails closed

Open rows come from the CHANGELOG mirror — the same table `obligation_ledger_check.py` gates, so the
two cannot disagree silently. A pinned list would go stale the moment a row closed, and the self-test
**fails if it parses empty**: a check that quietly stops applying is worse than no check.

### The rule shipped with two bugs of its own, and the registry caught both

Worth recording rather than quietly fixing, because one of them is a repeat.

**Substring matching.** `TowerLowerBound` is a prefix of `TowerLowerBoundUpTo`, so the honest partial
results `tower_lower_bound_upto_{two,three,four}` were flagged as claiming the open theorem they
explicitly do **not**. That is exactly the defect found earlier the same day in
`obligation_ledger_check.dischargers_of`, reintroduced by the person who had just fixed it. Now
word-boundary matched.

**A dropped condition.** Refactoring the rule into a pure function lost the `↔` requirement, so it
fired on any *mention* of an open obligation. A theorem may name one in a hypothesis
(`evSign_of_hard`) or prove a bounded instance (`TowerLowerBoundUpTo 4`); neither is a reduction.

The three claims that failed were the *honest partial results for an open obligation* — precisely
what this state exists to protect. A rule that punished them was backwards.

**Canary 15** unit-tests the rule on six specimens with no Lean round-trip: unmarked equivalence
FIRES, absent residue FIRES, honest form SILENT, plain characterisation SILENT, prefix-of-an-open-row
SILENT, non-equivalence mention SILENT.

### The witness ratchet turned

`no_rational_exponential` — twelve hypotheses, the largest in the pole layer and the one that most
resembled `positive_branch_impossible` before its repair — is now witnessed at `q = x`, `P = 1`,
`Qt = 1`, `r = 0`, `k = 1`. Baseline **37 → 36**.

### The 37 were triaged, and the number overstated the risk

`hypotheses_count` counts **all** top-level binders, so a computation lemma `foo (x : Real) : …`
lands in the list with arity 1 and zero vacuity exposure. Annotated per entry:

| category | n | can it be vacuous? |
| --- | --- | --- |
| computation (value binders only) | 12 | no |
| generalisation receipt (`Pr := True`) | 5 | no — terminal by design |
| internal case-absurdity | 7 | no |
| review queue | 12 | **yes** |

So the genuine review queue is **12, not 37**. Driving the count to zero would have meant writing
ceremonial witnesses for computation lemmas, which is worse than an honest list.

Gates: build **733 jobs**, aggregator **730 of 1036**, consistency PASS, claims **411** (self-test:
fifteen canaries), obligations 18 rows (nine convict specimens), discovered 290/294, AxiomLedger
**242 pinned (unchanged)**, sorry-audit 1 allowlisted, witness audit **36** (pinned set).

## [Unreleased] — 2026-08-24 (cn)

### `div` finished — a rational normal form, and the reduction for arbitrary contexts

(cm) handled the div-free fragment, where a context *is* a `Bipoly` and no side conditions arise.
Division needs them: `div_def` carries `hb : b ≠ 0`, so an identity `C.eval = N/D` can only hold
where the denominators are denominators. `ctxFrac_eval` states it multiplied out —

```
C.eval x y · bipev D x y = bipev N x y
```

— and carries **one nonvanishing condition per `div` node**, which turns out to be all that is
needed.

### Why the side condition is that small

For `add`/`sub`/`mul` the denominator is `da·db`, so the *top* denominator being nonzero already
forces both children's, and nothing extra is asked. Only `div` breaks the pattern: its denominator is
`da·nb` while `db` moves into the **numerator**, so `db ≠ 0` has to be requested. Everything else is
derived — including `b.eval ≠ 0`, which falls out of `b.eval · db = nb` together with `nb ≠ 0`
rather than being assumed.

`DivDenomsOK` is that predicate, and it asks for nothing at the non-`div` nodes.

### The reduction now covers every context

```
oneQueryDichotomy_of_bipoly : BipolyDichotomyAlong → (the dichotomy, for EVERY C)
```

with the two `div` side conditions evaluated along the curve. For a div-free `C` they are vacuous and
this collapses to (cm)'s statement. So `OneQueryDichotomy` is now reduced, on the whole of `FCtx`, to
one question with no context syntax in it: **can a nonzero bivariate polynomial vanish identically
along `y = F(P(x)/Q(x))`?**

### Discrimination

`ctxFrac_div_specimen` fires the normal form on a context that actually contains a division, with
both side conditions discharged — so `ctxFrac_eval` is not a theorem about div-free contexts in
disguise, and `DivDenomsOK` is not an unsatisfiable predicate. That check is the direct lesson of the
`hcharN` defect: a side condition nobody has ever satisfied is indistinguishable from a false one.

### Still open, and still only reduced

`OneQueryDichotomy` remains **open**. What (cm) and (cn) together establish is that its difficulty is
entirely the bivariate vanishing question — not the context grammar, not the totalised `log`, and not
the division. That is a reduction, not a theorem, and the ledger row is unchanged.

Gates: build **733 jobs**, aggregator **730 of 1036**, consistency PASS, claims **411**, obligations
18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted,
witness audit 37 (pinned set).

## [Unreleased] — 2026-08-24 (cm)

### `EMLOneQueryNormalForm` — the div-free fragment of `OneQueryDichotomy` is bivariate algebra

`OneQueryDichotomy` asks whether a one-query *context* `C(x, F(S x))` is eventually zero or
eventually nonzero, for `S = P/Q` rational. `EMLGermSign` already recorded the reason to expect it to
turn on **representation** rather than transcendence: sign-definiteness for `C₀` was easy precisely
*because `C₀` has a normal form*, and the level-1 question is hard exactly where none is available to
read the answer off.

This supplies the normal form for the fragment where one exists outright.

`FCtx` is `hole | const | var | add | sub | mul | div` — a **rational** function of `x` and the hole.
Drop `div` and it is a **polynomial** in the hole with polynomial-in-`x` coefficients: a `Bipoly`.
`ctxPoly` is that translation, and `divFree_eval` proves it evaluates correctly — **unconditionally,
with no side conditions at all**.

```
oneQueryDichotomy_divFree_of_bipoly : BipolyDichotomyAlong → (the dichotomy, for every div-free C)
```

On this fragment the obligation contains **no context syntax and no `FCtx`**. What is left is whether
a bivariate polynomial can vanish identically along the curve `y = F(P(x)/Q(x))` — an
algebraic-relation question about `F ∘ (P/Q)` and nothing else. **[CORRECTED in (cp): the residue
is that question *plus* a finite-zeros statement — see below.]** Same move as `EMLSignReduction`:
strip the representation until the residue is growth or algebraic dependence, then name it.

### Why `div` is excluded deliberately

Division needs its denominator nonzero to mean anything — `div_def` carries `hb : b ≠ 0` — so a
*rational* normal form must carry a nonvanishing condition for **every intermediate denominator**,
and that bookkeeping is a separate piece of work. The div-free fragment needs none of it, which is
exactly what makes it worth isolating rather than bundling.

### Discrimination

`divFree_specimens` exhibits two div-free contexts with real structure (`x·y` and `y² − 1`) and shows
`div` is genuinely excluded, so the normal form is not a theorem about an empty or trivial class.
`ctxPoly_mul_var_hole` checks the translation computes: the `Bipoly` denoted by `mul var hole` really
is `x · y`.

### What is **not** claimed

`OneQueryDichotomy` stays **open** and the `div` case is untouched. Nothing here shows a bivariate
polynomial cannot vanish along that curve — that is the residue, and for `F = exp + log` composed
with a *rational function* it is transcendence input the corpus does not yet have in this form.
`Fbasis_not_algebraic` is the corresponding statement for the **identity** argument (`F x`), not for
`F (P/Q)`.

Gates: build **733 jobs**, aggregator **730 of 1036** modules reachable, consistency PASS, claims
**409**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**, sorry-audit
1 allowlisted, witness audit 37 (pinned set).

## [Unreleased] — 2026-08-24 (cl)

### `witness_audit.py` — the signal that was there and unread, made into an artifact

`positive_branch_impossible` was vacuous for weeks under seven green gates. The one thing that would
have caught it — **nobody had ever supplied its hypotheses** — was visible the whole time as "this
theorem has no caller and no specimen anywhere in the corpus". Nothing measured it.

Now something does. `tools/witness_audit.py` reports every registered claim-theorem that takes at
least one hypothesis and is referenced nowhere else in `MachLib/`.

### A set, not a count

The baseline (`tools/witness_baseline.json`, **37 entries**) pins the explicit names. A count would
be a lossy proxy — it can sit flat while one entry gets witnessed and another regresses. Pinning the
set makes the ratchet turn one way: a **new** uninstantiated capstone fails the audit, and a
**witnessed** one must be removed from the list.

### Its scope, stated rather than assumed

* **No-caller is not a defect.** A capstone is legitimately terminal, which is why this is a ratchet
  against a pinned set and not a pass/fail on zero.
* **It cannot see vacuity, only drift.** A theorem concluding `False` is *meant* to have an
  unsatisfiable hypothesis set; the real question there is whether everything *except* the existence
  hypothesis discharges, and only a specimen can answer that.
* `∀ r, P r → Q r` is not vacuous because `P 0` is false — it stays usable at every `r ≥ 1`.

Two convict specimens, both verified to discriminate: a synthetic uninstantiated capstone is
reported, and a witnessed one (`pIrred_X`) stays silent. The ratchet was tested by unpinning an entry
— the audit goes RED and names it.

**Not wired into CI.** The gate set is deliberately exactly seven and adding an eighth is an owner
decision, so this sits with `closerate.sh` and `sorry_audit.lean` as a harness to run, not a gate.

Gates unchanged by this commit: build **732 jobs**, aggregator **729 of 1035**, consistency PASS,
claims **407**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)**,
sorry-audit 1 allowlisted. Witness audit: **37, exactly the pinned set**.

## [Unreleased] — 2026-08-24 (ck)

### The vacuity sweep, and two more capstones witnessed

A sweep over the corpus for the two defect shapes that made the `S > 0` branch vacuous, plus a pass
over every registered capstone that has never been instantiated.

### Both defect shapes are gone

* `∀ r : Nat, P r` where `P` mentions `pnsum` — the `r = 0` trap, since `pnsum 0 _ = []` and every
  polynomial divides the zero polynomial: **1 site**, `hkd` in `GermClearedDescent`, already stated at
  `r + 1` and discharged by the specimen.
* `PNormal` applied to a **constructed** object — the canonicity trap, since `pderiv` is
  length-preserving and always leaves a trailing zero: **0 sites**.

Other `∀ n : Nat` hypotheses were checked at their edge index and are false positives:
`npow n r` is `rⁿ`, so the Weierstrass bound at `n = 0` reads `|mult 0| ≤ C`;
`WitnessResidualConvexZeroBoundClosure`'s hypothesis is guarded by `1 ≤ k`; and the recurring-target
meta-lemma is instantiated (4 and 2 references).

### The criterion was wrong for impossibility theorems, and this corrects it

**A theorem concluding `False` is *supposed* to have an unsatisfiable hypothesis set** — that is what
an impossibility statement *is*. So "are the hypotheses satisfiable?" is the wrong question for
`proper_relation_impossible` and its neighbours, and applying it would have condemned every one of
them.

The right question is whether everything **except** the relation-existence hypothesis can be
discharged. If it cannot, the theorem says *"these side conditions never hold"* rather than *"no
relation exists for this germ"* — and that distinction is exactly what
`positive_branch_impossible` got wrong, since its `hchar` alone yielded `False`.

Likewise, `∀ r, P r → Q r` is **not** vacuous merely because `P 0` is false: it stays usable at
every `r ≥ 1`. Vacuity needs the hypothesis set contradictory under *every* instantiation, which is
why a `∀` *inside* a hypothesis was the dangerous shape and a `∀` *over* an implication is not.

### Two more capstones witnessed, by the same pole data

`proper_relation_impossible` and `germ_relation_impossible` take exactly the pole data the `q = x`,
`P = 1`, `Q = x` specimen already discharges, so both are now witnessed with **nothing assumed about
the pole**:

```
proper_relation_impossible_inv_x : ProperRel (1/x) Ls → False
germ_relation_impossible_inv_x   : EvEqF S (1/x) → ProperRel S Ls → False
```

`ProperRel S Ls` is a polynomial relation in `exp (S x)` with a non-vanishing top coefficient, so
what these say concretely is that **`exp (1/x)` is transcendental over `ℝ(x)`** — and now with no
pole hypotheses left standing between the statement and a reader.

### What the sweep leaves open

Of 405 registered claim-theorems, **38 carry hypotheses and are still referenced nowhere else** — no
caller, no instantiation, no specimen. None matches a known-bad pattern, and the two shapes above are
eradicated, so this is a standing item rather than a live defect. The list is dominated by
`EMLSizeNineShape`, `EMLGrowthEnvelope`, `EMLCertifiedSynthesis` and `EMLUnaryBasis`; the pole and
relation layer is now largely witnessed.

Gates: build **732 jobs**, aggregator **729 of 1035** modules reachable, consistency PASS, claims
**407**, obligations 18 rows (self-test: nine convict specimens), discovered 290/294, AxiomLedger
**242 pinned (unchanged)**, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (cj)

### `EMLSignReduction` — `SignHardCase` is a growth comparison, with no logarithm in it

`SignHardCase` is the last cancellation obligation and, via `evSign_of_hard`, the whole remaining gap
in the depth programme: is `exp (A x) − log (B x)` eventually of constant sign when `B > 0`?

**`log 1 = 0`, so `eml t (const 1)` evaluates to `exp (t.eval x)`** — `exp ∘ t` is itself an EML tree
(`expTree_eval`), and hence so is `exp ∘ exp ∘ t`. On a ray where `B > 0` the logarithm is strictly
monotone, so

```
exp (A x) − log (B x) > 0   ⟺   exp (exp (A x)) > B x
exp (A x) − log (B x) ≤ 0   ⟺   exp (exp (A x)) ≤ B x
```

and both sides of the right-hand comparison are EML tree values. So

```
signHardCase_iff_compareExpExpPos : SignHardCase ↔ SignCompareExpExpPos
```

where `SignCompareExpExpPos A B` is eventual sign-definiteness of `exp (exp (A.eval x)) − B.eval x`.
**An equivalence, not a one-way reduction** — the positivity hypothesis is consumed by the direction
that needs it and reappears in the other, so the obligation is *the same*, not merely implied.

### Why the equivalence and not the stronger form

Dropping `B`'s positivity gives `SignCompareExpExp`, which is strictly *stronger* — reformulating the
difficulty without lowering it. Both are recorded and the difference is stated, because a reduction
to a stronger statement is easy to mistake for progress. `treeComparable_imp` notes that full
pairwise comparability of EML germs (the Hardy-field property) gives the stronger form.

What the equivalence buys is that the **totalised `log` is removable, not merely avoidable**. The
convention `log y = 0` for `y ≤ 0` is why `SignHardCase` carries a positivity hypothesis at all and
why its two branches behave so differently; after the reduction none of that is present and the
content is a pure growth comparison. `signHard_of_le_one` marks where the difficulty is *not*: if
`B ≤ 1` eventually the node is positive for free, so the whole problem lives on the ray `B > 1`.

**`SignHardCase` remains `open`.** Nothing here discharges it.

### The ledger: an equivalence is not a reduction

The first attempt marked `SignHardCase` **reduced** to `SignCompareExpExpPos` and registered the
residue as a new row. The gate accepted it — and it was wrong. `reduced` means the debt got
*smaller*; here it moved to an **equivalent** unproved statement, so the row would have claimed
progress that did not happen. Reverted to `open`, 18 rows, and both directions are now folded into
the `Iff` so that **no named theorem's conclusion is `SignHardCase`**.

### Two defects in the obligations gate, found by this

**An `↔` was read as a discharge.** `dischargers_of` matches the conclusion by *prefix*, so
`foo : P ↔ Q` counted as concluding `P` — a reduction reading as a solution. Guarded, with a new
**canary 9** that unit-tests the matcher on synthetic declarations. Verified by perturbation: with
the guard removed the canary goes SILENT and the self-test FAILS.

**A canary specimen named a live obligation.** Canary 5 marked `SignHardCase` as `refuted`, which
fires only while *no* theorem concludes it — so it went silent the moment a reduction theorem did,
taking the whole gate down. Its specimen is now synthetic.

The reasoning recorded beside canary 9 said the other statuses were stable because "discharged and
refuted rows do not revert". That is **wrong**, and this is the counterexample: the stable property
is not the status label but that the named proposition stays *unconcluded* — a fact about the corpus.
No canary specimen may name a live obligation, whatever status it carries. Comment corrected in
place.

Gates: build **732 jobs**, aggregator **729 of 1035** modules reachable, consistency PASS, claims
**405**, obligations 18 rows (self-test: nine convict specimens), discovered 290/294, AxiomLedger
**242 pinned (unchanged)**, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (ci)

### VOID / scope correction — the disclosure, in short

The previously registered `S > 0` flagship was **vacuous**. Two of its hypotheses were unsatisfiable
for *every* `q`:

* `hchar : ∀ r : Nat, DerivCoprime q r` — false at `r = 0`, since `pnsum 0 _ = []` and every
  polynomial divides the zero polynomial.
* `hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q))` — false at **every `r ≥ 1`**, since `pderiv` is
  length-preserving and therefore always leaves a trailing zero, so its output is never canonical.

**The Lean proof was valid for its formal statement.** Nothing accepted an invalid derivation. What
failed is that the statement did not certify the advertised case: with a contradictory hypothesis
set, the theorem carried no information about any germ, while its registered prose asserted that
`log(P/Q)` satisfies no minimal relation with coefficients in `R(x)[e^(P/Q)]`.

Both hypotheses are corrected — the first weakened to `r + 1`, the second **deleted** as unnecessary
— and the replacement proves the intended result directly, with no auxiliary hypothesis:

```
proper_relation_impossible_inv_x : ProperRel (1/x) Ls → False
```

i.e. **`exp(1/x)` is transcendental over `ℝ(x)`**, every pole hypothesis discharged at `q = x`,
`P = 1`, `Q = x`.

**Not to be confused with the `m = 0` finding.** `MinimalityScope` separately established that `hmin`
caps the arc at `m = 0`. That is a *scope* limitation, disclosed earlier and of a different kind: it
narrows what the theorem covers, it does not make it vacuous.

**The process lesson.** This defect was not detectable from build status or claim registration.
`False → P` is provable, cites no forbidden axiom, and discharges any obligation, so the build, the
claim auditor and the obligation ledger were all structurally blind to it. It was found by asking
what a universal hypothesis asserts at arguments the proof never supplies.

### VOID — `positive_branch_impossible` was **vacuous**, and so was everything built on it

**Object of this void:** the registered claim `positive-branch-closed-changelog`, and every
statement in this changelog and in `CLAUDE.md` that reads `positive_branch_impossible` as having
established `log(P/Q) ∉ R(x)(e^(P/Q))`. It did not. It is a true theorem with a **contradictory
hypothesis set**, so it carried no information about any germ.

This was found by trying to build a satisfiability specimen — not by any gate. Two hypotheses were
unsatisfiable:

**1. `hchar : ∀ r : Nat, DerivCoprime q r` — false at `r = 0`, for every `q`.**
`DerivCoprime q 0` unfolds to `¬ Pdvd q (pnsum 0 (pderiv q))` = `¬ Pdvd q []`, and every polynomial
divides the zero polynomial. Machine-checked: `False` follows from `hchar` alone.

**2. `hcharN : ∀ r : Nat, PNormal (pnsum r (pderiv q))` — false at every `r ≥ 1`, for every `q`.**
`pnsum 1 Z = Z`, so at `r = 1` this asserts `PNormal (pderiv q)`. But `pderiv` is
**length-preserving** (`pderiv_length`), and a derivative drops degree — so `pderiv` always pads with
a trailing zero and is never canonical. `pderiv [a,b] = [b, 0]`. Machine-checked at
`q = x`, `x²+1`, `x³+x²+x+1`.

Neither is detectable by any gate here. The claim auditor pins axiom footprints; the obligation
ledger pins open/discharged rows; the build checks provability. **A vacuous theorem passes all
three.** The one thing that would have caught it — instantiating the hypotheses — had never been
done: `positive_branch_impossible` had no caller and no specimen in the entire corpus.

### The repairs

**`hchar`: weakened to `∀ r, DerivCoprime q (r + 1)`.** Proof-neutral. Every consumption site
already applied it at a successor (`hchar (r+1)`, `hchar (c+1)`, `hchar (r'+1)`); index `0` was
consumed nowhere; `PolyDerivShort` only ever *produces* `DerivCoprime q (k+1)`. 18 binder sites, 7
application sites, whole corpus rebuilds unchanged.

**`hcharN`: deleted outright.** Not weakened — *deleted*, because it was never needed.
It fed exactly **one** `euclid_lemma` call, as the `PNormal a` argument. `euclid_lemma'` drops that
side condition entirely:

```
euclid_lemma' (hq : PIrred q) (hnd : ¬ Pdvd q a) (hab : Pdvd q (pmul a b)) : Pdvd q b
```

proved by applying `euclid_lemma` to `pnorm a`. Sound because `Pdvd` is *defined* through `pnorm`
and `pnorm_pmul_left` says `pmul` sees only the normal form of its left argument — so the statement
was already invariant under normalising `a`, and the canonical case implies the general one. 18
binder sites removed across 15 files, nothing else changed.

The hypothesis was not just unsatisfiable, it was **decorative**.

### The specimen — what makes the arc non-vacuous

`GermClearedSpecimen` exhibits `q = x`, `P = 1`, `Q = x`, hence `S = 1/x` and the germ `log(1/x)`,
and discharges every surviving hypothesis:

* `pIrred_X : PIrred [0,1]` — the **first `PIrred` construction in the corpus**. `PEq` is
  `pnorm`-equality and both sides are canonical, so the factorisation is a literal list equation and
  `pmul_length` closes it: `2 = a + b − 1` with `a, b ≥ 1` forces a constant factor.
* `derivCoprime_X` — `pderiv [0,1] = [1+0, 0]`, the very trailing zero that made `hcharN`
  unsatisfiable, normalises to the constant `1`; so this reduces to `q ∤ (r+1)·1`, already proved by
  `not_Pdvd_pnsum_one'` from irreducibility alone.
* the rest by evaluation (`pev [0,1] x = x`, `pev [1] x = 1`).

```
no_proper_cleared_relation_inv_x :
  ClearsToExp (1/x) fs → GProperRel (log(1/x)) fs → False
```

**No pole hypotheses at all** — they are discharged, not assumed. This is the artifact that makes
the whole arc say something, and it is a standing gate: if a future edit makes a hypothesis
unsatisfiable again, this file stops compiling, which is exactly what did not happen for the two
defects above.

### Step 5, and the degree-`d` result

`GermClearedBranch` threads `Pr` through the last two layers still taking the unrestricted `hmin`
(`relCoeffs_nil_ratLog`, `positive_branch_impossible`) — transcription, since neither inspects it.
`GermClearedDescent` then assembles: `exists_minimal_hmin` produces a shortest relation *in the
class*, `exists_expCoeffs_of_clears` replaces it by an `expCoeffs` image of the same length, and the
existing `m`-general sweep finishes. `no_proper_cleared_relation` takes **no `hmin`, no `Cs`, no
split and no degree bound**.

Two facts the assembly needed and the corpus lacked: `two_le_length_of_gProperRel` (a one-element
proper relation `[c]` asserts `c x + u x·0 = 0`, i.e. `c` *is* eventually zero), and `hkd` quantified
`∀ r` rather than at a fixed `m`, since `m` is now derived from the minimal relation's own length.

### Status after this commit

`log(1/x)` satisfies no proper relation whose coefficients clear, over one common non-vanishing
denominator, to polynomials in `x` and `e^(1/x)` — at **any** degree, with every hypothesis
discharged. That statement is new. The degree-one reading that (cf) and (ce) attributed to
`positive_branch_impossible` was never established at all.

Gates: build **731 jobs**, aggregator **728 of 1034** modules reachable, consistency PASS, claims
**403**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + 325
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (ch)

### `GermClearedRatLog` — `hPrd` at the branch's own germs

(cg) discharged `hPrd` against three *abstract* clearing hypotheses. This supplies them for the
germs the `S > 0` branch actually has — `S = P/Q`, `u = log ∘ S` — so nothing about the class is
left parameterised by the time a caller sees it. `clearsToExp_hPrd_ratLog` takes **only**
`¬ EvZeroF (pev Q)` and `¬ EvZeroF (pev P)`, both of which the branch already carries.

The three hypotheses map onto lemmas that already existed:

| abstract hypothesis | discharged by |
| --- | --- |
| `S'·pev QQ = pev Dn` | `ratFn_deriv_cleared`, at `QQ = Q²` |
| `v·pev (W·QQ) = pev Nv` | `ratLogDeriv_cleared`, at `W = P`, `Nv = Q·Dn` |
| `¬ EvZeroF (pev (W·QQ))` | `not_evZeroF_pmul` |

That they line up is not luck — the invariant in (cf) was shaped to match what `RatLogDeriv` and
`BipevRatFn` already prove. `W = P` is **forced**, not chosen: `v` clears by `P·Q²`, `S'` clears by
`Q²`, and `Q²` divides `P·Q²`, so the common denominator is the larger and the surplus `P` rides
along on the `S'` side inside `biscale`.

### The one lemma the corpus was missing

`not_evZeroF_pmul` — a product of polynomials neither of which is eventually zero is not eventually
zero. `pev_dichotomy` and `pev_ne_zero_on_tail` were both present but there was no product form.
Stated through `EvNonvanish`, where it is two lines, rather than by re-running the dichotomy: this
is the second time (cf) `EvNonvanish` has paid for itself, and both times because it is the
formulation that composes under multiplication.

`clearsToExp_hPrd_ratLog` cites no `HasDerivAt`, no `Real.log` and no `sorryAx`.

### What remains for degree `d`

Only threading and assembly, no new invariant. `relCoeffs_nil_ratLog` and
`positive_branch_impossible` still take the **unrestricted** `hmin`, so `Pr` has to be threaded
through those two the way (cb)–(cd) threaded it through the three above them — transcription, since
neither inspects `hmin` beyond passing it down. Then `exists_minimal_hmin` supplies the restricted
`hmin` from the witness, `exists_expCoeffs_of_clears` turns the minimal member into an `expCoeffs`
image, and the existing `m`-general sweep finishes.

Gates: build **728 jobs**, aggregator **725 of 1031** modules reachable, consistency PASS, claims
**400**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + 325
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (cg)

### `GermClearedStep` + `GermClearedDrel` — `hPrd` discharged, and the identity instantiated

(cf) supplied the class and closed `hdrop`; this closes the third and last obligation, and then
instantiates the identity theorem at the class so the composition is gated rather than merely
plausible.

### The denominator does not grow — the step is not symmetric

Going in, the expectation (stated in (ce)) was that `gscaleSub` forms products, so denominators
multiply. They do not. The step's shape is

```
gscaleSub cd dtop cs₀ ds₀     entry j  =  cd·(ds₀)ⱼ  −  dtop·(cs₀)ⱼ
```

and `cd`, `cs₀` come from `expCoeffs` — they are `bipev`s already, denominator `1`. Only `dtop` and
`ds₀` come from `gdrel` and carry a denominator. **Each product has exactly one dirty factor**, so a
single `pev G` clears both terms and comes out unchanged:

```
pev G · (cd·dⱼ − b·cⱼ)  =  cd·(pev G·dⱼ) − (pev G·b)·cⱼ  =  bipev (bisub (bimul A Dⱼ) (bimul Bt Cⱼ))
```

`gsubNum` is that family and `gEvEq_gscaleSub_cleared` is the theorem. This matters for the arc and
not only for the proof: had denominators multiplied, each descent step would raise the `Q`-power and
the class would have needed a denominator *bound* to survive a degree-`d` descent. It needs none.
The `Q`-power is fixed once, by the producer, and never moves again.

### One denominator covers both sources

`gdrel v cs es = gadd es (gscale v (gyd cs))` has two sources of denominator, and they differ:
`es` carries `S'`, cleared by `Q²` (`BipevClearedDeriv.bipev_cleared_deriv_zero`); `gscale v (gyd cs)`
carries `v = (log ∘ S)'`, cleared by `P·Q²` (`RatLogDeriv.ratLogDeriv_cleared`). Because `Q²`
divides `P·Q²`, **one denominator covers both** — no least common multiple is computed anywhere. That
is why the statements are shaped as `pmul W QQ`: the `v` side fixes the denominator and the surplus
factor `W` is absorbed into the `S'` side's numerator by `biscale`.

### The closure obligation is algebra, not analysis

`clearsToExp_hPrd` cites **no `HasDerivAt`, no `Real.log`, no `exp_pos`, no `exp_add`, and no
`sorryAx`** — despite being a statement about a *differentiated* relation. The reason is a design
decision made four modules ago: `dbipevExp` is a **definition**, and `bipev_cleared_deriv` is an
algebraic identity about that definition. The analysis — that `dbipevExp` *is* the derivative — lives
in `hasDerivAt_bipev_exp` and is never invoked here. Registered with the claim auditor.

### Syntactic mirrors, and why they are only `GEvEq`

`gadd`, `gyd` and `gscale` act on germ lists; their numerators need counterparts one level up.
`cadd` and `cyd` mirror the recursions **pattern for pattern**, including `gadd`'s asymmetric
off-length cases, so no length hypothesis appears anywhere below. They do *not* commute with
`expCoeffs` on the nose — `gadd` gives `bipev A x E + bipev B x E` where `cadd` gives
`bipev (biadd A B) x E`, equal pointwise but not definitionally — so every statement is up to
`GEvEq`, which is what the class is stated with in any case.

### The instantiation is a theorem, not a probe

`minimal_expRel_identity_cleared` is `minimal_expRel_identity_in` at `Pr := ClearsToExp S`, with
`hdrop := clearsToExp_dropLast` and `hPrd := clearsToExp_hPrd` supplied. A caller now supplies
**three clearing facts and no closure obligations**: the denominator is not eventually zero, `S'`
clears by `QQ`, `v` clears by `W·QQ`.

This is stated as a theorem deliberately. An abstraction that is never instantiated is not known to
be the *useful* one — a green build says `True`, not "the one you need" — and the composition was
first checked as a throwaway `example`, which gates nothing once the file is deleted.

### What remains

Step 5: take the minimal member, run the descent, and contradict minimality — i.e. assemble a
degree-`d` `positive_branch_impossible` from `exists_minimal_hmin`, `exists_expCoeffs_of_clears` and
this identity. The obligations are discharged; what is left is the assembly and the sweep, which
already exists at `m = 0`.

## [Unreleased] — 2026-08-24 (cf)

### `GermCleared` — the admissible class, and the WLOG that removes the obstruction

(ce) reduced the fourth module to *supply a class, prove it closed under `dropLast` and under the
`gscaleSub` step, and exhibit one proper relation in it*, and named what was left as genuinely hard:
`minimal_expRel_identity_in` wants its relation to be an `expCoeffs` image, and the minimal member of
a class need not be one. This module supplies the class and closes two of the three obligations.

```
ClearsToExp S fs  :=  ∃ D Cs, EvNonvanish D ∧ GEvEq (gscale D fs) (expCoeffs S Cs)
```

**One** common denominator `D` clears the **whole** coefficient vector to an `expCoeffs` image. One
`D` outside the list, not one per entry: `gcancel_top` compares entries against each other, so
per-entry denominators do not survive the leading-coefficient reasoning.

### The obstruction was a scaling lemma, not a construction

`exists_expCoeffs_of_clears` is the module's point. If `fs` is a proper relation in the class then
`gscale D fs` **is** an `expCoeffs` image, has the **same length**, is still a relation
(`gbipev (gscale D fs) = D · gbipev fs`), and is still proper. Same length means it is still minimal
among class members — so a minimal member may be *replaced* by an `expCoeffs` image, and
`minimal_expRel_identity_in` gets the shape it asks for with nothing weakened.

The theorem carries **no analysis**: `exists_expCoeffs_of_clears` cites no `HasDerivAt`, no
`Real.log`, no `exp_pos`, no `exp_add`, and no `sorryAx` — it never differentiates, and uses nothing
about `exp` beyond its being a function. Registered with the claim auditor.

### `EvNonvanish`, and why `¬ EvZeroF` is not enough

The denominator must be non-zero **on a tail**, which is strictly stronger than *not eventually
zero*. Germ multiplication has zero divisors — two germs neither of which is eventually zero can
have an eventually-zero product, by being supported on interleaved tails — and `GProperRel`'s second
clause is `¬ EvZeroF` of the top coefficient. Under the weaker reading, clearing can destroy
properness and every leading-coefficient fact with it. `not_evZeroF_mul` is the one place the extra
strength is spent, and it is false for `¬ EvZeroF`.

Nothing is lost by asking for the stronger form: the denominators that actually arise are `pev`s of
polynomials, and `pev_dichotomy` has no third case, so `evNonvanish_pev` upgrades `¬ EvZeroF` to
`EvNonvanish` for free.

### `hdrop` is discharged; the `gscaleSub` step is not

`clearsToExp_dropLast` closes the first closure obligation — same denominator, one fewer numerator —
and `clearsToExp_expCoeffs` supplies the witness `exists_minimal_hmin` asks for, with `D = 1`.

**Not attempted here:** `hPrd`, the `gscaleSub` step. That is where `S' = (P'Q − PQ')/Q²` enters, and
where the denominator must be shown to *multiply* rather than proliferate — `gscaleSub` forms
products and differences, so a common `Q`-power should survive, but that is a claim about `bimul`
and `bisub` numerators and it is not proved here. It is the one remaining obligation between this
class and a degree-`d` `positive_branch_impossible`.

### The bootstrap the arc had not named

`MinimalityScope.gProperRel_witness` puts `[−u, 1]` — a proper relation of length two — in reach of
*every* germ, and that is what caps the unrestricted arc at `m = 0`. A restricted `hmin` is worth
nothing if the class still contains it, and `clears_witness_forces_algebraic` says exactly what
excluding it costs: `[−u, 1] ∈ ClearsToExp S` forces `D·u` to be a `bipev` in `e^S`, i.e.
`u ∈ R(x)(e^S)`. For `u = log ∘ S` that is what the **already-closed degree-one theorem refutes**.

So the `m = 0` collapse is not an obstacle this class routes around — the degree-one result is the
thing that lifts it. Worth recording because the arc has been treating `m = 0` purely as a defect.

### Not added to the algebra spine, deliberately

`algebraFootprint` is an allow-list that excludes the ordered axioms and everything analytic.
`GermCleared` legitimately cites `leR`/`ltR` — every statement in it is eventual — and `Real.exp`,
via `expCoeffs`. Adding it to `algebraSpineModules` would mean widening that allow-list, which is
the deny-list creep its own docstring warns about. The algebra-spine count stays at 325 for the
right reason, not because the module was overlooked.

Gates: build **725 jobs**, aggregator **722 of 1028** modules reachable, consistency PASS, claims **397**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + 325 algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (ce)

### `ClassMinimality` — `hmin` costs one witness, not a construction

(cb)–(cd) made minimality a parameter. That is worth nothing unless the restricted `hmin` can be
produced, and this says what it costs:

```
exists_minimal_hmin :
  Pr ms → GProperRel u ms →
    ∃ cs, Pr cs ∧ GProperRel u cs ∧ ∀ ns, Pr ns → GProperRel u ns → cs.length ≤ ns.length
```

**Two hypotheses.** Given *any* proper relation in the class, there is a shortest one, and its
minimality statement is `hmin`'s exact shape. `exists_minimal_length'` (`BipevMinimal`) does the
work; the content is applying it to the **conjunction** `Pr ∧ GProperRel` rather than to either
alone.

### Why the conjunction, and not two applications

Minimising `Pr` first and then `GProperRel` inside it gives the shortest member of the class — which
need not be proper — and then a shortest proper relation *among lists of that length*. That is not
the shortest proper member, and it is not what `hmin` compares against. The conjunction is the
statement wanted.

### What this reduces the fourth module to

Before: *supply a class and discharge minimality inside it.* After: **supply a class, prove it closed
under `dropLast` and under the `gscaleSub` step, and exhibit one proper relation in it.** The
minimality obligation disappears — it was never the hard part, it only looked like one.

What remains genuinely hard is the other direction: `minimal_expRel_identity_in` wants `cs` to be an
`expCoeffs` image, and the minimal member of a class need not be one. A class whose members all clear
to `expCoeffs` images over a common denominator would settle it — `gscaleSub` forms products and
differences, so denominators multiply and numerators stay `Bipoly`. **Not attempted here**, and it is
the last thing between the parameterisation and a degree-`d` `positive_branch_impossible`.

### A consistency check falls out

`exists_minimal_hmin_unrestricted` — every germ with a proper relation has a shortest one — sits
against (ca)'s finding that every germ has a proper relation of **length two**. The two agree: the
unrestricted minimum is always exactly 2, which is why the unrestricted `hmin` forced `m = 0`.

Gates: build **724 jobs**, aggregator **721 of 1027** modules reachable, consistency PASS, claims
**395**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (cd)

### `ExpCoeffIdentityClass` — the `R(x)[E]` instantiation, restricted

Third of the four modules (ca) named. `minimal_expRel_identity_in` is `minimal_expRel_identity` with
`Pr` threaded: **nine hypotheses against the original's seven**, the same delta of two as one level
down, and the body is unchanged — the three added hypotheses pass straight to
`minimal_grel_identity_in`. `minimal_expRel_identity_unrestricted` recovers the existing theorem as
the `Pr := fun _ => True` instance.

At the germ layer the split obligation is about `gscaleSub cd dtop cs₀ ds₀`; here `cd` is
`fun x => bipev Cd x (e^(S x))` and `cs₀` is `expCoeffs S Cs₀`, so it is spelled out in those terms
and still quantified over the split.

### Three modules of transcription, and the one with content

All three of (cb), (cc) and (cd) are the same move: add `Pr`, add two obligations, pass them down,
recover the old statement as the `True` instance. Each compiled on the first or second attempt
because nothing about the proofs changed — the hypothesis was always too strong, and weakening a
hypothesis that is used once is mechanical.

**The fourth module is not.** No concrete class has been supplied, and until one is —
germs of the form (rational in `x`)·(polynomial in `E`), with minimality dischargeable inside it —
`positive_branch_impossible` remains a degree-one statement. Three modules of scaffolding buy
nothing on their own; that is worth saying plainly rather than reporting three green bricks as
progress toward a result they do not yet deliver.

Gates: build **723 jobs**, aggregator **720 of 1026** modules reachable, consistency PASS, claims
**393**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (cc)

### `GermIdentityClass` — the weakening carried up to the identity

`minimal_grel_identity_in`: the two-coefficient identity with `hmin` restricted to a class `Pr`, and
`minimal_grel_identity_unrestricted` recovering the existing theorem as the `Pr := fun _ => True`
instance. Twelve hypotheses against the original's ten — the two added are the closure obligation and
the split obligation, and nothing else changed in the proof.

### The closure obligation is stated *at the split*, not abstractly

`minimal_grel_identity` obtains `ds₀` and `dtop` **inside** its proof, by splitting `gdrel v cs es`.
A caller cannot name them, so demanding `Pr (gscaleSub cd dtop cs₀ ds₀)` outright would be
unusable. The hypothesis is universally quantified over the split instead:

```
hPrd : ∀ ds₀ dtop, gdrel v cs es = ds₀ ++ [dtop] → Pr (gscaleSub cd dtop cs₀ ds₀)
```

which a caller discharges without knowing which split occurs, because there is only one. Same
discipline as `BipevRearrange` taking the clearing conditions rather than the model: **say what must
hold of the thing, not which thing it is.**

### Two `private` lemmas restated rather than un-privatised

`split_last` and `evZeroF_congr` are `private` in `GermDerivEntry`. Both are eight lines and both are
restated here. Un-privatising them would widen that module's interface to serve a generalisation
living outside it — the cost of a duplicate is two small proofs; the cost of the alternative is a
permanent interface change made for a caller's convenience.

### Still not done

`minimal_expRel_identity` — the `R(x)[E]`-coefficient instantiation — takes the unrestricted `hmin`,
and **no concrete class has been supplied**. `positive_branch_impossible` remains degree-one until
both land. Two of the four modules named in (ca) are now through.

Gates: build **722 jobs**, aggregator **719 of 1025** modules reachable, consistency PASS, claims
**391**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (cb)

### `GermRelationClass` — minimality restricted to a class, where the obstruction actually sits

(ca) showed `hmin` forces `m = 0`. The cause is that **`hmin` is far stronger than its use**: it is
applied in exactly *one* place — `all_gcoeffs_evZero_of_shorter` — and there only to the derived
relation and its `dropLast` truncations, never to an arbitrary germ list.

So it may be restricted to any class closed under `dropLast`, and the proof is unchanged.
`all_gcoeffs_evZero_of_shorter_in` is that version, with the class a **parameter** `Pr` so the
closure obligation stays with whoever instantiates it.

### Not two versions of one theorem

`all_gcoeffs_evZero_of_shorter_unrestricted` derives the existing statement as the
`Pr := fun _ => True` instance. The general form **subsumes** the specific one rather than sitting
beside it — which is the reason to add a module instead of editing `GermRelation` in place, and the
answer to the standing objection that generalising beside leaves two things and no benefit.

### What this does *not* do, stated plainly

`minimal_grel_identity` and `minimal_expRel_identity` still take the unrestricted `hmin`. Threading
`Pr` through them, and instantiating it at a class for which minimality is *dischargeable*, is the
remaining work. **Until that lands, `positive_branch_impossible` is still a degree-one statement** —
this module removes the obstruction at the only place it sits; it does not by itself widen anything.

For the `S > 0` arc the class that closes is germs of the form *(rational in `x`)·(polynomial in
`E`)* — `R(x)(E)`, not `R(x)[E]`, because the derivative coefficients carry `S'`, which is rational.
`gscaleSub` forms `cd·dⱼ − dtop·cⱼ`, products and differences, so that class is closed under both the
`gscaleSub` step and `dropLast`; and a minimal-length relation within it exists by
`exists_minimal_length` (`BipevMinimal`) and **is** an `expCoeffs` image.

Gates: build **721 jobs**, aggregator **718 of 1024** modules reachable, consistency PASS, claims
**389**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (ca)

### `MinimalityScope` — the arc runs at `m = 0` and nowhere else

`minimal_grel_identity` carries `hmin : ∀ ns, GProperRel u ns → cs.length ≤ ns.length`, with `ns`
ranging over **arbitrary** germ-coefficient lists. That quantifier is far stronger than it looks:
**every germ has a proper relation of length two** — `−u + 1·u = 0`, leading coefficient the constant
`1`. So `hmin` caps `cs.length` at two, and since `cs.length = m + 2` in
`minimal_expRel_identity`'s shape, **`m = 0`**.

Proved, not observed: `gProperRel_witness`, `minimality_forces_length_two`,
`expRel_minimality_forces_m_zero`.

### This narrows the scope and does not weaken the result

Nothing proved becomes false. At `m = 0` the relation is `c₁·L + c₀ = 0` with `c₁` not eventually
zero — i.e. **`log S ∉ R(x)(e^S)`**, which is exactly what the branch needed. Steps 2 and 3 of the
(bf) decomposition are delivered together in one theorem, and (bz)'s headline stands.

What is *not* delivered is the generality the `m` suggests. A reader of `positive_branch_impossible`
would take it to cover relations of every degree; it covers degree one, because **no hypothesis set
containing that `hmin` admits anything else** — the whole `m`-indexed apparatus (`natMul (m+1) 1`,
`relK Q D m`, the `(m+1)` in the identity) is live only at `m = 0`.

### Why the theorems keep the `m`

Removing it would mean restating `minimal_grel_identity` and four modules above it. The generality is
**free** — it costs nothing to carry and the proofs are no harder — and if `hmin` is ever weakened to
range over relations with coefficients in a fixed class, the `m` becomes live with no rewrite.
**Carrying it is cheap; claiming it is not**, which is what this module exists to prevent.

Found by asking whether `positive_branch_impossible`'s hypotheses are dischargeable *before* building
the next brick on top of them — the check that "a green build says TRUE, not the one you need".

Gates: build **720 jobs**, aggregator **717 of 1023** modules reachable, consistency PASS, claims
**387**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (bz)

### `PositiveBranch` — the `S > 0` branch, closed end to end

**`positive_branch_impossible`**: for `S = P/Q` with a pole at the irreducible `q` and positive on a
tail, `log S` satisfies **no** minimal relation with coefficients in `R(x)[e^S]`. Seventeen
hypotheses — the pole data, the branch's positivity, the relation's shape — and it compiled first
try, like the dispatcher before it.

```
GEvRel (log ∘ S) (expCoeffs S Cs)            the hypothesis
      ↓  Cs ↦ Cs.map bitrim                  expCoeffs literally unchanged (bw)
relCoeffs_nil_ratLog (bq)                     every coefficient nil
      ↓  bitrim_split on Cd and Cd₁
sweep_impossible / sweep_impossible_nil_second (bx, by)
```

That is step 3 of the branch's three-step decomposition, opened in (bf): `log S ∈ R(x)(e^S)` +
`e^S` transcendental ⟹ contradiction. Steps 1 and 2 are unchanged and step 1 remains the one that
needs a new representation.

### Properness, and the fifth arm that does not exist

`minimal_expRel_identity` asks for minimality **among proper relations**; it never asks the relation
at hand to be proper. That is deliberate and it suffices for the identity — but **not** for the
sweep: if `Cd` were the zero germ, every coefficient of `relCoeffs` would be nil for trivial reasons
and nothing would follow.

So this theorem takes `¬ EvZeroF` of the top coefficient — `GProperRel`'s second clause — and that
one hypothesis is exactly what makes `bitrim Cd ≠ []`. The fifth arm the sweep would otherwise have
needed is not written because the hypothesis removes it, not because it was overlooked.

### The trim is a rewrite, not a transport

`expCoeffs S (Cs.map bitrim) = expCoeffs S Cs` is an **equality of lists of functions**, so `hmin`,
`hrel`, `hCs`, `hlen0` and `hCd1` all transfer by `rw` and `List.map_append`/`List.getElem?_map`.
Five hypotheses moved across a normalisation without a single congruence lemma. That is the payoff
from (bw)'s decision to trim before the identity rather than after.

### The arc, measured end to end

Nine bricks (bq…bz) from the two clearing conditions to the closed branch. Build **710 → 719 jobs**,
algebra spine **258 → 325** theorems (0 leaking throughout), claims **358 → 385**, AxiomLedger
**242 pinned, unchanged at every step** — the whole branch added no axioms.

`no_rational_exponential`, sized in (bf) as step 2's workhorse and expected to be called once per
coefficient, is called **zero times**: the `a < b` case routes through `cleared_relation_impossible`,
which the *other* branch already had.

Gates: build **719 jobs**, aggregator **716 of 1022** modules reachable, consistency PASS, claims
**385**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (by)

### The fourth arm — `Cd₁` is the zero germ, and the sweep is complete

`relCoeffs_top_of_nil_second` and `sweep_impossible_nil_second`. **All four arms of the sweep now
exist as theorems**: the three degree comparisons (bx) and the case where `Cd₁` trims away entirely.

The subtracted product does **not** vanish when `Cd₁ = []` — `bimul X [] = replicate |X| []` — so it
is a run of `[]` entries of length `a+1` against `T₁`'s `2a+1`:

* `a ≥ 1`: a strict gap, `bisub_concat_left`, top is `α·(K·α)` **exactly**;
* `a = 0`: the two coincide, `bisub_concat_both`, and the top picks up a `pmul [0-1] []` tail.

That tail is `List.replicate 1 0`, so `pnorm_padd_replicate` erases it. Both branches therefore give
a top **`PEq` to** `α·(K·α)` rather than equal to it — and that is enough, because
`top_gt_impossible` consumes `pnorm _ = []`, which is `PEq`-invariant. **The arm costs a reading and
no new landing**, exactly as (bx) predicted from the shape of `bimul_nil_right`.

### The `PEq` was the right output type, and it was decided before the proof

Stating the reading as an equality would have forced the `a = 0` corner to be normalised away inside
the reading — which cannot be done, since `padd X [0] = X` needs `X ≠ []`. Returning a `PEq` moves
that corner to where it costs nothing, because the consumer was already `pnorm`-based. This is the
same decision as (bs)'s readings carrying `pmul [0 - 1]` instead of `psub`: **state what falls out,
and let the consumer's own invariance absorb it.**

Gates: build **718 jobs**, aggregator **715 of 1021** modules reachable, consistency PASS, claims
**383**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (bx)

### `RelCoeffsSweep` — the sweep chooses its case

**`sweep_impossible`**: given a relation whose two top coefficients both survive trimming, the three
readings are selected by `Nat.lt_trichotomy` on `|Bs|` against `|As|` and each is closed by its own
landing. Thirteen hypotheses, and the proof compiled first try — which is the point: every piece it
composes was shaped for exactly this join.

```
Bs.length < As.length   relCoeffs_top_gt  →  top_gt_impossible
Bs.length = As.length   relCoeffs_top_eq  →  top_eq_impossible
As.length < Bs.length   relCoeffs_top_lt  →  top_le_impossible
```

### The side conditions are discharged here, not assumed

Every landing carries its nonvanishing and characteristic-zero inputs as hypotheses so the algebra
could stay inside the spine. This module is outside the spine and pays them:

* `pnorm X ≠ []` from `¬ Pdvd q X` — everything divides the zero polynomial, so a non-divisibility
  hypothesis *already says* the thing is nonzero. One line, and it covers `P` and `(m+1)·1`.
* `pnorm D ≠ []` from `ord_deriv_cross`'s witness `Ec`, which is coprime to `q` and therefore
  nonzero; cancelling `q^r` transfers that to `D`.
* `¬ Pdvd q ((b−a)·1)` from `not_Pdvd_pnsum_one'`, which proves `n·1 > 0` and **costs the order
  axioms** — exactly why the landings did not discharge it themselves.

`expCoeffs_map_bitrim` also lands here rather than in `BipolyTrim`, for the reason (bw) measured: it
mentions `exp`, and the ledger convicts it inside the spine.

### What is still open

`sweep_impossible` assumes **both** top coefficients survive trimming. The remaining arm is
`bitrim Cd₁ = []` — `Cd₁` the zero germ. `bimul_nil_right` is proved here (`bimul X [] =
List.replicate X.length []`), which is the shape that arm needs: the subtracted product does not
vanish, it becomes a run of `[]` entries of length `a+1`. Against `T₁`'s `2a+1` that splits at
`a = 0`, and both sub-cases give a top `PEq` to `α·(K·α)`, so `top_gt_impossible` covers both — but
the reading lemma itself is **not written**. Nothing above depends on it; it is a fourth arm of the
dispatcher, not a gap in the three that exist.

Beyond that: the top-level `S > 0` statement, which instantiates `RatLogRelation`'s caller against
this dispatcher.

Gates: build **718 jobs**, aggregator **715 of 1021** modules reachable, consistency PASS, claims
**381**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (bw)

### `BipolyTrim` — trailing zero coefficients, stripped

The three readings all want `Cd = As ++ [α]` with `pnorm α ≠ []`, and nothing supplies it: `Cd`
arrives through `hCs : Cs = Cs₀ ++ [Cd]`, and properness says only that the **germ** is not
eventually zero, not that the top `E`-coefficient survives.

`biconsN`/`bitrim`/`BiNormal` are `pconsN`/`pnorm`/`PNormal` one level up, with the coefficient
ring's zero test `pnorm _ = []` in place of `_ = 0` — the same transcription `BipolyLead` made from
`PolyMulDegree`. `bitrim_split` is the shape the readings consume; `bipev_bitrim` is why it is free.
Algebra spine 318 → **325** theorems, 0 leaking.

### Trim before the identity, not after

`bipev (bitrim L) = bipev L` pointwise, so `expCoeffs S (Cs.map bitrim) = expCoeffs S Cs` as a list
of **functions** — and `expCoeffs` is exactly a `map` into functions, so the relation, its minimality
and its length transfer untouched. The trim can therefore happen where `Cs` is chosen, before
`minimal_expRel_identity` is ever invoked.

Doing it afterwards would mean transporting the germ identity through the trim: the same fact **plus
a derivative**, since `dbipevExp` would also have to be shown insensitive to a trailing zero
coefficient. Trimming first costs one evaluation lemma; trimming last would cost two, and the second
is about a derivative rather than a value.

### The transfer lemma is deliberately *not* in this module — measured, not assumed

`expCoeffs S (Cs.map bitrim) = expCoeffs S Cs` is two lines, and it mentions `exp`. Putting it here
was tried and the ledger convicted it:

```
error: AxiomLedger: algebra-spine theorem MachLib.expCoeffs_map_bitrim footprint
LEAKS 1 axiom(s) beyond algebraFootprint (field+classical only): [MachLib.Real.exp]
```

So it moves to the assembly, which is outside the spine anyway. Same trade as `BipolyLead` refusing
the `dcoeffs` shape lemmas: the layer stays algebraic and the caller pays one line of transport.

### The ledger's summary line said `OK` while the run failed

Running that specimen surfaced a reporting defect. `AxiomLedger` ends in an **unconditional**
`logInfo "AxiomLedger OK: …"`, so with the leak present it printed

```
AxiomLedger OK: … 326 algebra-spine theorems field-axiom-checked (1 leaking).
```

The exit code was **1** — the gate fails closed, and nothing was ever mis-gated. But the last line,
which is what a human or an agent reads, said `OK` while reporting `1 leaking`. This repo already has
the rule that a clean-looking column can be a broken column; this was the summary version of it.

The verdict is now **read off the message log** — `(← get).messages.hasErrors` — rather than
re-derived from the counters. That matters for more than tidiness: a check added later cannot forget
to update the verdict, because the verdict is not a separate computation. Bound to evidence, not to
a literal.

Demonstrated both ways rather than argued: with the leak, `AxiomLedger FAIL … (1 leaking)`, exit 1;
without it, `AxiomLedger OK … 325 … (0 leaking)`, exit 0.

Gates: build **717 jobs**, aggregator **714 of 1020** modules reachable, consistency PASS, claims
**379**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **325**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (bv)

### `RelCoeffsEqCase` — the third case, and the sweep's three readings are all closed

```
eq_case_identity    the reading, cleared:  P·Q²·(βα' − β'α) ≈ α·K·α
eq_case_reduced     the same after q^(2s) and one Q come off
top_eq_impossible   no_rational_logarithm_scaled closes it
```

**All three top coefficients of `relCoeffs` are now impossible as theorems** — `top_gt_impossible`,
`top_le_impossible` (bt) and `top_eq_impossible` (here). Algebra spine 310 → **318**, 0 leaking: the
whole sweep, both counts included, cites nothing but the field axioms.

### Two cancellations, and the order matters

First `c² = q^(2s)`: it sits on both sides because the cross-difference is homogeneous of degree two
(`peq_cross_common_factor`) and `α²` obviously is. Then a **single** `Q` — the left carries `Q²` and
the right carries `K = (m+1)·Q·D`, so exactly one survives. **That surviving `Q` is what makes the
result `P·Q` rather than `P·Q²`**, i.e. the logarithmic count's shape rather than the exponential
one's. The two counts differ by exactly the `Q` that this case fails to cancel.

### The sign goes on the denominator

`no_rational_logarithm_scaled` wants `(N'·Dd − N·Dd')·(P·Q) ≈ k·D·(Dd·Dd)`; the reduced equation is
`(α₁'β₁ − α₁β₁')·(P·Q) ≈ (m+1)·D·α₁²`. With `Dd = −α₁` the square kills the sign on the right and
`N'·Dd − N·Dd'` flips exactly once on the left. Taking `N = −β₁` instead would have needed `PNormal`
of a scaled polynomial; this way only `hDne` and `hlow` see the scale, and both reduce to
`Pdvd_pscale` — which already existed.

`psub_pscale_neg` is the whole sign argument in one line: negating both sides of a difference **swaps
them**, and it is an *equality*, because `(−1)·(−1) = 1` collapses the double scale and `padd_comm`
does the rest.

### What is left

The three cases are closed; nothing yet *chooses* between them. That needs `Cd` and `Cd₁` written as
`As ++ [α]` and `Bs ++ [β]` with `pnorm α ≠ []` and `pnorm β ≠ []` — a trimming step, since
properness only says the *germ* is not eventually zero, not that the top `E`-coefficient survives —
plus the fourth case where `Cd₁` trims away entirely, which behaves like `a > b`.

Gates: build **716 jobs**, aggregator **713 of 1019** modules reachable, consistency PASS, claims
**377**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **318**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (bu)

### `CrossIdentities` — what the `a = b` case needs that the others did not

```
psub_padd_padd            (A+B) − (C+E) = (A−C) + (B−E)            syntactic
peq_pmul_regroup          the two inner factors of a 4-product swap
peq_dtop_cross            at EQUAL indices the D terms cancel: Q²·(uv' − u'v)
peq_cross_common_factor   W(cA, cB) ≈ c²·W(A,B)
exists_common_ord_split   a common q-power off both, leaving lowest terms at q
```

Algebra spine 301 → **310** theorems, 0 leaking.

### The asymmetry between the two counts, stated once

`cleared_relation_impossible` consumes the two `q`-adic factorisations **separately**;
`no_rational_logarithm_scaled` consumes a fraction **in lowest terms**, because its `q ∣ D` branch
runs `ord_deriv_cross`, which needs one side coprime to `q` to pin the order exactly. A lower bound
is not enough there — with `ord α = a` and `ord β = b` both positive, `ord_cross_lower` gives only
`a + b + r ≤ r + 2a`, i.e. `b ≤ a`, and no contradiction. **That is the entire reason `a = b` costs
this module and `a ≤ b` cost nothing.**

### The `q'` term does not survive

Taking a common factor off means transporting the equation, and the transport is
`peq_cross_common_factor`. Expanding `W(cA, cB)` produces `c·c'·A·B` **twice, with opposite signs**,
and those cancel identically — before any divisibility argument starts. So the transport is an
unconditional identity, not an order estimate, and the split needs no hypothesis about `c` beyond
what `exists_ord_factor` already gives.

### `peq_dtop_cross` versus `coeff_identity`

`coeff_identity` is the `m ≠ j` statement of the same four-term split, and it says what follows when
the difference **vanishes**. The `a = b` case cannot use it — there the difference is not zero, it is
`K·α²`. The lemma needed is the one that says what the difference **is**, and at equal indices that
is `Q²·(uv' − u'v)` with no multiple of `D` left over.

### `Pdvd_pscale` already existed, one brick after the same mistake

`Pdvd_pscale` is at `PolyPoleOrder.lean:88`. I declared it here anyway and **three of my four proof
lines were identical to the original** — the brick immediately after the one whose changelog entry
was about exactly this failure. Knowing the rule did not fire the rule.

So it stops being a rule and becomes a mechanical pre-flight: before the first proof, grep every
identifier the module intends to **declare** — not the ones it intends to use — against the whole
tree, and again before committing. Note what does *not* catch it: `lake build <module>` passes,
because a clash in a module this one does not import stays invisible until the aggregator imports
both. The other six names in this module were checked that way and are unique.

Only the reverse direction was new here (`Pdvd_of_pscale_neg`), and it needs no `1/c`: scaling by
`−1` twice is the identity.

Gates: build **715 jobs**, aggregator **712 of 1018** modules reachable, consistency PASS, claims
**373**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **310**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-24 (bt)

### `RelCoeffsLand` — two of the three top coefficients are impossible

```
a > b   α·(K·α) ≈ 0             four cancellations, and no transcendence lemma at all
a ≤ b   α·(P·β*) ≈ (P·α*)·β     cancel P, then coeff_identity, then the pole count
```

**`a > b` needs nothing.** The top coefficient is `(m+1)·Q·D·α²` with **no `P` in it**, so the whole
case is: a product of nonzero polynomials is not zero. Four `pmul_eq_nil_cancel`s. Worth noticing how
little it costs — the case that *looks* like it should need the hard theorem needs none of it,
because the degree gap already removed every term that could cancel against `K·α²`.

**`a ≤ b` is the other branch's landing, reused verbatim.** Cancelling `P` turns the coefficient into
`coeff_identity`'s hypothesis — the same expression, not a matching one — and that yields exactly
`cleared_relation_impossible`'s `hident`. Nothing about either was built for this case. In particular
`cleared_relation_impossible` takes the two `q`-adic factorisations **separately** rather than a
lowest-terms pair, so `α` and `β` need no common-factor reduction: `exists_ord_factor` is applied to
each independently and the two exponents never have to be compared.

### `a ≤ b`, not `a < b`

`coeff_identity` wants `j ≤ m`; strictness enters only through `¬ Pdvd q ((b−a)·1)`, which is a
hypothesis. So the theorem is stated at `a ≤ b` and the hypothesis does the work honestly — at
`a = b` the multiplier is `pnsum 0 [1] = []`, every irreducible divides it, and the hypothesis is
simply unavailable. Nothing in this module has to know that, which is why `a = b` gets its own
landing rather than a special case inside this one.

### Both landings are field-axiom-only

Algebra spine 296 → **301** theorems, 0 leaking. The two cases that close the transcendence argument
are **algebra**: no `ltR`, no `leR`, no `exp`, no `HasDerivAt`. Every nonvanishing and
characteristic-zero input is carried as a hypothesis rather than discharged — `not_Pdvd_pnsum_one'`
would discharge the last one, but it proves `n·1 > 0` and costs the order axioms, so paying it here
would take the module out of the spine for one line. The assembly pays it, where the order axioms are
already present.

### `[c]·Y ≈ c·Y`, unconditionally

`pmul_singleton` needs `Y ≠ []`. At `Y = []` the two sides are `[0]` and `[]` — different as lists,
equal after `pnorm`. That is exactly the gap `PEq` exists to close, so the `PEq` form needs no
hypothesis, and it is what lets `RelCoeffsLead`'s readings keep carrying `pmul [0 - 1]` instead of
manufacturing a `≠ []` side condition one layer too early. The refusal in (bs) is paid for here, in
one lemma.

Gates: build **714 jobs**, aggregator **711 of 1017** modules reachable, consistency PASS, claims
**369**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **301**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bs)

### `RelCoeffsLead` — the top coefficient, in three cases

`relCoeffs_nil_ratLog` says *every* coefficient of the rearrangement is the zero polynomial. The
argument needs **one** — the coefficient of the highest surviving power of `E` — because that one's
vanishing is an equation between the two leading coefficients. With `a = |As|`, `b = |Bs|` and
`Cd = As ++ [α]`, `Cd₁ = Bs ++ [β]`:

```
a > b   index 2a     α·(K·α)                                K = (m+1)·Q·D
a < b   index a+b    α·(P·β*) − (P·α*)·β
a = b   index 2a     α·(P·β* + K·α) − (P·α*)·β
```

with `α* = Q²·α' + a·D·α` the trailing entry of `dcoeffs`. **These are three different equations,
not three instances of one.** `K·α` reaches the top only when `Cd` is at least as long as `Cd₁`,
which is why `a > b` collapses to a single product and `a < b` never sees `K`.

Each reading is the same three steps — split the inner sum, multiply, subtract — and the only thing
that varies is which `bisub` lemma applies, decided by whether the two products come out the same
length. Four more `Bipoly` shape lemmas were needed for that and went into `BipolyLead`:
`biadd_concat_left` and `biadd_concat_both` (with their `bisub` corollaries). `biadd` recurses on its
first argument, so `_left` is a separate induction rather than a `comm` rewrite, and `_both` is the
equal-length case neither one-sided lemma covers — each of those needs a strict gap.

Algebra spine 278 → **296** theorems, 0 leaking: the readings are pure list arithmetic, so the module
is field-axiom-only even though `relCoeffs` was defined in a module full of `exp`.

### `dtop` is a definition so that two expressions become one

`α*` is written `dtop Q D a α`. Not for brevity — it is *the same expression* as the bracket
`coeff_identity` consumes, `padd (pmul QQ (pderiv v)) (pnsum m (pmul D v))`. Naming it is what makes
the `a < b` reading and that theorem's hypothesis a single term rather than two that have to be
reconciled at the join. This is the second time in the arc that a naming decision has done the work
of a lemma.

### The readings carry `pmul [0 - 1]`, not `psub`

`bisub` produces `padd x (pmul [0 - 1] y)`, and `psub x y` is `padd x (pscale (0 - 1) y)`. The two
agree — `pmul_singleton` — but only for `y ≠ []`, and manufacturing that side condition is exactly
what a shape layer should not do. The readings therefore state what falls out, and the conversion is
paid by the caller that already has `P ≠ []` in hand. Same discipline as `bimul_concat` dropping its
unused nonvanishing pair.

Gates: build **713 jobs**, aggregator **710 of 1016** modules reachable, consistency PASS, claims
**366**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **296**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (br)

### `BipolyLead` — the leading coefficient of a bipoly, syntactically

**`bimul (A₀ ++ [α]) (M₀ ++ [μ]) = D ++ [pmul α μ]`** — the coefficient of the top power of `E` in a
product is `pmul` of the two leading coefficients, as a statement about *lists*. The coefficient
sweep has to read `A_α·B_β` off `relCoeffs`; `Bipoly`'s four evaluation laws cannot do that, because
a value at a point says nothing about which list entry it came from.

Every lemma here is a transcription of its `PolyMulDegree` original with `padd` for `+`, `pmul` for
`·` and `[]` for `0` — `biadd_nil_right`, `biadd_length_le/ge`, `biadd_assoc`, `biadd_concat_right`,
`biadd_nil_singleton`, `biscale_length/concat`, `bishift_*`, `bimul_length`, `bimul_concat_left`,
`bimul_concat`, `bisub_concat_right`. Where the univariate proof rewrites with `add_zero` this one
rewrites with `padd_nil_right`, and that is the whole difference. Algebra spine 258 → **278**
theorems, 0 leaking.

### One hypothesis pair dropped rather than carried

`pmul_concat_normal` carries `α ≠ 0` and `μ ≠ 0` **and does not use them** — the concat shape holds
for any coefficients, and the hypotheses are there because the intended reading is about canonical
polynomials. `bimul_concat` drops them.

The zero-divisor question does not disappear; it moves to the caller, where `pnorm (pmul α μ) ≠ []`
has to be argued from `pnorm α ≠ []` and `pnorm μ ≠ []` — and that is `pmul_eq_nil_cancel`'s job, not
a shape lemma's. Carrying the pair would have looked stronger, proved the same thing, and hidden
which lemma owns the absence of zero divisors. Registered as `hypotheses_count: 0`.

### `dcoeffs_concat` was already written, and the module system said so

Both `dcoeffs` shape lemmas the sweep needs — `dcoeffs_concat` and `dcoeffs_length` — already exist
in `BipevDcoeffsShape`, written for the elimination arc three commits ago. They were re-proved here
verbatim and the duplicate was caught by **`import failed, environment already contains
'MachLib.dcoeffs_concat._proof_1_1'`** — the module system, not review, not the gates.

Worth recording as the cost it was. `BipevDcoeffsShape`'s own docstring says a recursive family gets
its shape lemmas *at the first pairing*, and this is the sweep pairing with `dcoeffs` for the second
time. The lesson is narrower than "search first": the lemmas were filed under the *consumer* that
first needed them (`Bipev…`), not under the family they describe (`dcoeffs`), so a search by family
name found the definition and missed the shape.

Removing them also keeps this module clear of `BipevClearedDeriv`, whose import would have carried
`exp` into a module the algebra spine checks for field axioms only.

Gates: build **712 jobs**, aggregator **709 of 1015** modules reachable, consistency PASS, claims
**363**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + **278**
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bq)

### `RatLogRelation` — the caller, and the coefficients come out nil

**`S = P/Q` and `u = log ∘ S` go in; `pnorm A = []` comes out** for every coefficient of the
rearrangement. Every module from `GermRelation` down to `BipevRearrange` is stated for an *arbitrary*
germ with its clearing conditions carried as hypotheses; this is the only module in the chain that
knows `S` is literally `P/Q`, and it is three `exact`s and the tail bookkeeping between them.

That it *is* only that is the point. The clearing conditions were shaped to compose — `S'·Q² = D`
and `v·(P·Q²) = Q·D` rather than "`S` is `P/Q`" — and this module is the receipt for that shape.

### One positivity hypothesis, not two nonvanishing ones

`ratLogDeriv_cleared` wants `pev Q x ≠ 0` **and** `pev P x ≠ 0`. The branch's defining hypothesis
already gives the second: `0 < P·(1/Q)` forces `P ≠ 0`, since a product with a zero factor is `0`.
So `ratLogDeriv_cleared_on_tail` is bypassed in favour of the pointwise form and `¬ EvZeroF (pev P)`
never has to be supplied — **`evRel_relCoeffs_ratLog` takes 7 hypotheses, not 8**, and the one
removed is the one a caller would have found hardest to produce. Registered as a count, so re-adding
it fails the gate instead of passing unnoticed.

### `MachLib.Real.log` cannot appear in an axiom footprint

Registered yesterday on `ratLogDeriv_cleared` to pin *"the footprint contains no `log`"*. It does not
pin that. `Real.log` is a `noncomputable def`, not an axiom, so the token matches only the unrelated
`log10` axioms. The way `log` actually enters a footprint is through its **definition** —
`Classical.choose (exp_surj x h)` — so **`MachLib.Real.exp_surj` is the token that discriminates**,
and it is now in the forbid list.

Measured both ways rather than argued: `exp_surj` is **absent** from `ratLogDeriv_cleared`'s
footprint (22 axioms) and **present** in `hasDerivAt_ratLog`'s (31). The old list would not have
fired on the one theorem in its own module that violates the claim — a guard that cannot convict its
own specimen.

The neighbouring question, checked at the same time: of **31 distinct forbid tokens across 358
claims**, exactly one other matches nothing in the environment — `zero_count_bound_classical`, in 10
claims. That one is **correct as it stands**: the axiom was deleted on 2026-07-15, and those claims
are retirement guards, which are supposed to match nothing until someone reintroduces it. Checked
before reporting, because a forbid that matches nothing is a defect only when the property it names
can still occur.

Gates: build **711 jobs**, aggregator **708 of 1014** modules reachable, consistency PASS, claims
**361**, obligations 18 rows, discovered 290/294, AxiomLedger **242 pinned (unchanged)** + 258
algebra-spine field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bp)

### `RatLogDeriv` — the two clearing conditions, discharged

**`(S'/S)·P·Q² = Q·D`** — `BipevRearrange`'s second clearing condition, discharged. It follows
from `S'·Q² = D` by one field identity, `(1/(p·(1/q)))·p = q`, and that identity is where the
two nonvanishing hypotheses live. **Both are paid here and neither propagates.**

`hasDerivAt_ratLog` supplies the derivative itself (`HasDerivAt_comp` against `HasDerivAt_log_pos`),
and the two tail forms are what `evRel_relCoeffs` (bo) consumes directly.

### `S > 0` enters **only** at differentiability. `log` is totalised, so it is differentiable only
where its argument is positive — and that is the sole use of the branch's defining hypothesis.
The clearing algebra is sign-blind: `ratLogDeriv_cleared`'s footprint contains no `ltR`, no
`leR`, no `log`, no `HasDerivAt` of any kind.

That is worth pinning rather than merely observing. The branch is *named* for a sign condition, so
the natural expectation is that the sign is load-bearing throughout; it is not. Everything after this
module is sign-blind, and the registry now forbids the order and analysis axioms on
`ratLogDeriv_cleared` so a future proof cannot quietly reintroduce them.

### `conv_lhs` again

`conv_lhs => rw [← key]` — not a tactic here. The fix is the corpus's standing idiom: state the
rewritten form as its own `have` and `rw [← step, key]` through it. That is the second missing-tactic
substitution in this arc and the same shape as the first (`set`, `add_lt_add_right`, `by_contra`):
reach for the equation, not the navigation.

Gates: build **710 jobs**, aggregator **707 of 1013** modules reachable, consistency PASS, claims
358, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 258 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bo)

### `BipevRearrange` — the germ identity becomes a relation in `e^S`

**`relCoeffs` evaluates to `P·Q²` times the identity**, so the identity vanishing on a tail makes
`relCoeffs` a relation there — whatever `P` and `Q` happen to do. That is the input
`all_coeffs_nil_of_relation` consumes.

Two pieces of the identity carry **rational** coefficients: `dbipevExp`, whose coefficients involve
`S'`, and the factor `v = S'/S`. Both clear against `P·Q²`:

```
Q²·c'        = bipev (dcoeffs Q² D 0 C) x (e^S)      -- bipev_cleared_deriv at j = 0
P·Q²·(S'/S)  = Q·D                                   -- since S = P/Q and D = P'Q − PQ'
```

so one factor clears the whole identity, and what remains is `Bipoly` (bn) — three `bimul`, two
`biscale`, one `biadd`, one `bisub`.

### The two hypotheses are the **clearing conditions**, `S'·Q² = D` and `v·(P·Q²) = Q·D`, not the
statement that `S` is literally `P/Q`. **No division is performed here, so none has to be
justified here** — the module carries no nonvanishing side conditions at all.

This is the discipline that made `bipev_cleared_deriv` take `S'·pev QQ x = pev D x` as a hypothesis
rather than constructing `S'`, reused one level up. The caller, which does know `S = P/Q` on a tail,
discharges both — and it is the caller that owns the `pev Q x ≠ 0` obligation, where it belongs.

### The index-0 corner

`bipev_cleared_deriv` carries a correction term `natMul j (pev D x) · bipev Ls`, needed because the
naive form does not induct. At `j = 0` it vanishes, and `bipev_dcoeffs_zero` is that instance —
three lines, and the only place this arc needs the family at all.

Gates: build **709 jobs**, aggregator **706 of 1012** modules reachable, consistency PASS, claims
356, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 258 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bn)

### `Bipoly` — the second level of polynomial arithmetic

**Bivariate polynomial arithmetic** on `List (List Real)`: `biadd`, `biscale`, `bimul`, `bisub`,
with `bipev (bimul A B) x y = bipev A x y * bipev B x y` and its three siblings. The same
construction as `padd`/`pmul`/`psub` one level up — the coefficient ring is `List Real` instead
of `Real`, so `padd` replaces `+` and `pmul` replaces `*`.

Four definitions, four evaluation laws, every proof mirroring its univariate original. Field-axiom
only: `algebraSpineModules` goes 254 → **258**, 0 leaking.

### Why a second set of definitions rather than a coefficient-ring abstraction

`pmul`, `pnorm`, `Pdvd` and the whole Euclid spine are written concretely for `List Real`, not over
an abstract ring — MachLib has no algebraic hierarchy, by design. So a second level means a second
set of definitions.

That is the cheap side of the trade here: **four definitions and four lemmas, against introducing a
ring class and re-instantiating twenty modules.** The rearrangement needs the *arithmetic* and none
of the divisibility theory, so the abstraction would have been paid for and not used. If a third
level ever appears, or if the second level needs `Pdvd`, the trade flips and should be re-made
rather than extended.

### What it is for

The `S > 0` identity `c_d·(c_(d−1)' + v·m·c_d) − c_d'·c_(d−1) ≈ 0` must be rearranged into a
*single* relation in `e^S` before `all_coeffs_nil_of_relation` (bl) can make it syntactic. That
rearrangement is products and sums of `R[x][T]` polynomials, which is exactly this layer — plus one
clearing of denominators by `P·Q²`, since `v = S'/S` and `c'` both carry rational coefficients.

Gates: build **708 jobs**, aggregator **705 of 1011** modules reachable, consistency PASS, claims
354, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + **258** algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bm)

### `GermExpCoeff` — instantiating the identity at coefficients in `R(x)[E]`

**The identity at `R(x)[E]` coefficients.** A minimal relation for `u` whose coefficients are
polynomials in `e^S` forces the same two-coefficient identity, now written entirely in `bipev`
and `dbipevExp` — **no germ variables left in the coefficients.** Seven hypotheses, down from
`minimal_grel_identity`'s ten: three of them (`es`'s split, its length, its entry) are *computed*
here rather than assumed, because the derivative list is `Cs.map dbipevExp` and its shape follows
from `Cs`'s.

### Supplying `GDerivAt` for these coefficients is a **map over a list and nothing more**, because
`hasDerivAt_bipev_exp` already differentiates exactly this shape and `dbipevExp` is its
derivative in value form.

A decision made for brick four pays off here. `dbipevExp` was kept in **value** form rather than as
a coefficient family, on the stated grounds that the differentiated relation's coefficients involve
`S'`, which is rational rather than polynomial, and a `List (List Real)` would hide that. That is
exactly why the instantiation is `Cs.map` and not a re-derivation: the value form composes with an
arbitrary germ-coefficient theorem, the family form would not have.

### What this deliberately does not do

It does not turn the germ identity into a **syntactic** one. That is `all_coeffs_nil_of_relation`'s
job (bl), and it needs the identity rearranged into a relation in `e^S` first — whose coefficients
are products of the `Cⱼ`. That step is polynomial bookkeeping over `R(x)[E]`, not analysis, and it is
the next piece.

Gates: build **707 jobs**, aggregator **704 of 1010** modules reachable, consistency PASS, claims
353, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 254 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bl)

### `BipevAllZero` — the transcendence bridge, six lines

**Every coefficient of a relation in `e^S` is the zero polynomial** — no properness hypothesis,
because the theorem is exactly that properness is impossible. This is "`e^S` is transcendental"
in the shape the `S > 0` sweep consumes: it turns a germ identity in `e^S` into an identity
between the syntactic coefficient polynomials.

### The vacuous minimality

`all_coeffs_evZero_of_shorter` takes `hmin : ∀ Ns, ProperRel S Ns → Ms.length ≤ Ns.length`. With
`proper_relation_impossible` in hand that hypothesis holds **vacuously, for any `Ms` whatever** — so
take `Ms` longer than the relation and the descent runs with nothing to descend against. No new
induction and no new machinery: `List.replicate (Ls.length + 1) []` and `absurd`.

The descent was written to need only a *bound* to descend against, not a genuine minimal element.
That was not foresight — it was the shape the original proof happened to take — but it is why this
corollary is six lines instead of a module.

### Where the generalisation paid back

`GermRelation` (bg) generalised the descent off `pev` for the germ layer. The design note there said
the four descent lemmas never inspect `pev`; **this commit spends that observation in the polynomial
layer it started in**, which is the direction generalisations usually do *not* pay back.

Gates: build **706 jobs**, aggregator **703 of 1009** modules reachable, consistency PASS, claims
351, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 254 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bk)

### `no_rational_logarithm_scaled` — generalised *beside*, and the old one is now a corollary

**`k·S'/S` is not the derivative of a rational function**, for `k·1 ≠ 0`. The count does not
notice the `k` — `k·1` is a unit at `q`, contributing order `0` — which is why this is the
general statement and `no_rational_logarithm` is its `k = 1` instance rather than the reverse.

The `S > 0` coefficient sweep lands on `w' = −m·S'/S` for the relation's degree `m`, not on
`w' = S'/S`, so the `k` is needed. Three extra lines in the proof — one `ord_pmul_norm` per branch —
and `no_rational_logarithm` becomes a three-line corollary discharging `q ∤ 1` via `not_Pdvd_const`.

### The registry caught the consequence, which is the point of `proof_uses`

`poly-no-rational-logarithm-changelog` pinned five direct invocations: `ord_deriv_cross`,
`ord_cross_lower`, `ord_le_of_dvd`, `ord_pmul_norm`, `exists_ord_factor`. After the rewrite the proof
directly invokes **none** of them — only `no_rational_logarithm_scaled` and `not_Pdvd_const`.
`proof_uses` is a *positive* obligation, so all five would have failed. The claim is repointed to
`no_rational_logarithm_scaled`, and the five now sit on the general theorem where they are actually
used.

That is the composition check doing exactly what it exists for: the *statement* did not move,
`hypotheses_count` is still 11, and prose about the statement is still true — but the proof became
someone else's, and the registry insists on knowing.

### Why beside rather than in place

The `k = 1` form is what the analytic argument quotes, so it keeps its own name. The generalisation
went beside it in the same commit as the cleanup — the failure mode recorded earlier in this corpus
is generalising and *deferring* the tidy-up, which leaves two proofs to drift apart. Here there is
one proof and one corollary.

Spine 253 → **254**, 0 leaking; the scaled theorem is field-axiom-only for the same reason as the
original, with `¬ Pdvd q (pnsum k [1])` carried as a hypothesis rather than discharged.

Gates: build **705 jobs**, aggregator **702 of 1008** modules reachable, consistency PASS, claims
350, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + **254** algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bj)

### `GermDerivEntry` — step 1's identity, assembled

**The identity a minimal germ-coefficient relation forces on its top two coefficients:**
`c_d·(c_(d−1)' + v·d·c_d) − c_d'·c_(d−1) ≈ 0`, which rearranges to
`d·v·c_d² = c_d'·c_(d−1) − c_d·c_(d−1)'`. **No division appears anywhere in reaching it.**

`minimal_grel_identity` (`MachLib.GermDerivEntry`), ten hypotheses. With `v = L'` and coefficients in
`R(x)[E]` this is the `S > 0` branch's target identity, and it is reached with no field, no quotient,
no resultant and no monic normalisation.

### The chain, and where each link came from

`gEvRel_gdrel` (bi) differentiates the relation → `gdrel_getElem`/`gdrel_getElem_top` read off the
two entries that matter → `gcancel_top` (bg) drops the degree without dividing →
`all_gcoeffs_evZero_of_shorter'` (bg) kills every coefficient of what is left →
`gscaleSub_getElem` picks out the top one.

### `gyd`'s trailing zero is what keeps `gdrel_length` equal to `cs.length` — the formal `y`-derivative
of a degree-`n` polynomial has degree `n−1`, recorded as a zero in the top slot rather than by
shortening the list. That equal length is exactly `gcancel_top`'s hypothesis.

That is the design paying off twice: the trailing zero was put there so `gdrel` would be
length-preserving, and it is *also* what makes the top entry come out as plain `c_d'` with no
correction term.

### Values, not functions

Every entry lemma concludes `∃ b, … = some b ∧ ∀ x, b x = …` rather than naming the function
literally. Two coefficient germs that agree everywhere are equal only by `funext`, and the caller
needs the *values* — the identity being extracted is a pointwise equation on a tail. Cheaper, and
closer to what is consumed.

### Two small errors, both from the same habit

`List.length_dropLast` left `n + 1 - 1 = n`, which needs `omega` — `Nat` subtraction does not
simplify itself. And `rw [this] at hbt` produced `some dtop = some bt`, so the injection was in the
opposite direction to the one written. Both are the cost of writing the whole assembly before
compiling any of it; both took one line to fix.

Gates: build **705 jobs**, aggregator **702 of 1008** modules reachable, consistency PASS, claims
349, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 253 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bi)

### `GermDeriv` — differentiating a germ-coefficient relation

The remaining structural piece of the `S > 0` branch's step 1.

```
d/dx  Σⱼ cⱼ(x)·u(x)ʲ  =  Σⱼ cⱼ'(x)·u(x)ʲ  +  u'(x)·Σⱼ j·cⱼ(x)·u(x)^(j−1)
```

`gbipev_hasDerivAt` proves it for arbitrary `u` and arbitrary differentiable germ coefficients, by
one lockstep induction over the coefficient list and its derivative list. **The derivative of a relation is a relation, of the same length.** `gEvRel_gdrel`: a relation
vanishes on a tail, so its derivative vanishes strictly inside, and `gdrel_length` gives the
equal length that `gcancel_top` requires.

### The **index** is what is avoidable, not the list. `gydiff (c :: cs) = gbipev cs + y·gydiff cs`
proves the derivative formula with no index anywhere, and the same identity builds the list as
one shift and one addition — no `natMul`, no degree-carrying auxiliary recursion.

So this is a **partial** instance of the arc's recurring "the tool was heavier than needed" pattern,
and the module docstring now says so — the first draft claimed the list itself fell away, which is
wrong: `gcancel_top` consumes lists, and `gyd` is one. Only the index bookkeeping went.

### `GDerivAt` is structural, for the same reason

The coefficient-derivative hypothesis could be stated by index (`cs[j]? = some c → …`). It is stated
by structural recursion on the two lists instead, because the proof is a lockstep induction and an
index-based statement would have to be re-derived into that shape at every step.

### Lengths one-sided, again

`gadd_length_of_le` rather than a `Nat.max` equation — `omega` treats `Nat.max` as opaque, the same
reason `padd_length_le`/`padd_length_ge` exist. `gyd` preserves length (its top entry is the
trailing zero), which is precisely `gcancel_top`'s equal-length hypothesis.

### Step 1's remaining piece

Everything is now in place except identifying `gdrel`'s **entries** — specifically that its top is
`c_d'` and its `(d−1)`-st is `c_{d−1}' + v·d·c_d`. That is what turns `gcancel_top`'s output into the
identity `c_d·W' = c_d'·W`. Bookkeeping, not mathematics, and deliberately not started here.

Gates: build **704 jobs**, aggregator **701 of 1007** modules reachable, consistency PASS, claims
347, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 253 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bh)

### `PolyExpDeriv` — the workhorse of step 2

**No nonzero rational function satisfies `a' = k·S'·a`** (`k·1 ≠ 0`, `S` with a zero or pole at
the irreducible `q`). The solutions are `a = c·e^(kS)`, so this is the transcendence input the
coefficient sweep needs — and it is obtained by an order count, not from the relation theorem,
so the module stays field-axiom-only.

Cleared of denominators: `(N'D − ND')·Q² ≈ k·(P'Q − PQ')·(N·D)`, verified symbolically to be exactly
`(a' − k·S'·a)·D²Q²` before any Lean was written. Thirteen hypotheses; `algebraSpineModules` goes
250 → **253**, 0 leaking.

### Why not route it through the closed theorem

`proper_relation_impossible` already says `e^(kS)` is not a rational germ. Using it would first need
`a' = kS'a ⟹ a = c·e^(kS)` — antiderivative uniqueness, which is analysis plus a constant of
integration to chase. The direct count is cheaper **and lands somewhere better**: it stays inside
`algebraFootprint`, where the relation theorem cannot go (that one needs `exp` and the order axioms).

### The squared denominator is what makes this the easier count

Both branches collapse to `r + 1 ≤ 0`, and the term that does it is the `2(r+1)` from `Q²` against
the right side's `r`. `no_rational_logarithm` carries only `P·Q` there and needs the exact left-hand
order in one branch; this one gets a strict inequality in both. **The algebraically easier of the two
is the analytically harder one** — worth recording, because the intuition runs the other way.

### One direction error, and the shape of it

`ord_le_of_dvd` was applied with the two sides swapped: the right order divides the left, giving
`r + c + 1 ≤ c + 2r + 2` — true, and therefore no contradiction. The larger order is the one that
must be shown to divide, so it is the *left* exact factorisation that goes in. `omega` caught it
immediately; the counterexample it printed named `c` and `r` with no constraints, which is the
signature of a comparison stated in the harmless direction.

### A checking note

An ad-hoc footprint check for the substring `exp` reported a hit — on the theorem's own name,
`no_rational_exponential`. The claim registry does not have this problem because it forbids
**fully-qualified** names (`MachLib.Real.exp`), which cannot occur inside an unrelated identifier.
That is what the convention is for.

Gates: build **703 jobs**, aggregator **700 of 1006** modules reachable, consistency PASS, claims
345, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + **253** algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bg)

### `GermRelation` — the descent over arbitrary germ coefficients

The four descent lemmas **never inspect `pev`** — they use a coefficient only through "is / is
not eventually zero" and through the Horner cons step. So the whole layer restates over an
arbitrary germ coefficient, with the polynomial version recovered by `gbipev_map_pev`. `gbipev`, `GEvRel`, `GProperRel`,
`exists_minimal_grel`, `gevRel_dropLast`, `all_gcoeffs_evZero_of_shorter'`. One module, not the
three-to-four the sizing predicted, and it compiled on the first build.

### The design decision the sizing said to make first, and it dissolved

The sizing pass (bf) flagged monic normalisation as the one non-mechanical part: the descent
differentiates a relation and needs the top coefficient's derivative to vanish, which classically
means dividing by the leading coefficient — legitimate in a field, unavailable here without carrying
a nonvanishing witness with every germ.

**The degree drops with no division.** `c_d·R' − c_d'·R` has `Y^d` coefficient
`c_d·c_d' − c_d'·c_d = 0`, so germ coefficients need no nonvanishing witness and no monic
normalisation. The classical argument *divides* by the leading coefficient; this multiplies,
which needs nothing.

`gcancel_top` is that step: two relations of equal length, combined against each other's top
coefficients, give a relation one shorter. `gscaleSub` is the coefficientwise combination and
`gbipev_gscaleSub` its evaluation law.

**Fifth prediction in this arc that overshot** — and the first where the correction came from *this
repo's own* sizing note rather than from building the heavy thing first. The sizing was right that
it was the decision to make; it was wrong that the decision was expensive.

### One tactic note

`mach_ring` left a pure AC residual across the two `gbipev` atoms —
`y * (a x * G) = a x * (y * G)`. `mach_mpoly` with the seven atoms listed closes it. Same boundary as
recorded before: `mach_ring` normalises the ring structure it can see, and opaque applied terms need
naming.

Gates: build **702 jobs**, aggregator **699 of 1005** modules reachable, consistency PASS, claims
344, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 250 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bf)

### Opening the `S > 0` branch — the bottom step, and it needed nothing new

**`S'/S` is not the derivative of a rational function**, for any `S` with a zero or a pole at an
irreducible `q`. The whole content is one order count: `ord_q(S'/S) = −1` exactly, while
`ord_q(a')` for rational `a` is `ord_q(a) − 1` when `ord_q(a) ≠ 0` and `≥ 0` otherwise — never
`−1`.

`no_rational_logarithm` (`MachLib.PolyLogDeriv`), cleared of denominators: no `N`, `D` satisfy
`(N'D − ND')·(P·Q) ≈ (P'Q − PQ')·(D·D)`. Eleven hypotheses. **Field axioms only** — it joins
`algebraSpineModules`, which goes 244 → 250 theorems, 0 leaking.

### Only one side needs to be exact, again

`q ∤ D`: the right side has order exactly `r`, and the left carries `q^(r+1)` from the `P·Q` factor
alone. A **lower** bound suffices (`ord_cross_lower`), uniformly in `ord_q(N)` — including `0`, where
`Nat` subtraction saturates and the bound comes from `P·Q` rather than from the cross term.

`q ∣ D`: a lower bound gives `b + r ≤ r + 2b`, true for every `b`. The **exact** left order is
required, and `ord_deriv_cross` supplies it. Same asymmetry as `pole_order_contradiction`: two bounds
prove nothing.

### The zero primitive, handled rather than assumed away

`N ≈ 0` would make `S'/S ≈ 0`, i.e. `S` constant — excluded by the pole hypothesis, so it is
tempting to add `N ≠ 0` as a hypothesis. It is not needed: everything divides the zero polynomial, so
`q^1` divides the cross term and the left side outruns the right's exact order by `2`. One extra
branch, one fewer hypothesis, and no wrangling with `pmul`'s definitional unfolding — the `Pdvd`
lemmas already say it.

### Where this sits

The `S > 0` branch decomposes into three steps, all verified symbolically first (see
`monogate-research`, `exploration/positive_branch_2026_08_23/`):

1. `Y = F(S)` algebraic over `R(x)` ⟹ `log S ∈ R(x)(e^S)`;
2. `log S ∈ R(x)(e^S)` + `e^S` transcendental ⟹ `log S ∈ R(x)`;
3. `log S ∈ R(x)` ⟹ **contradiction** — this commit.

Step 2 reduces to `proper_relation_impossible`, already closed. Step 1 is the one that needs a new
representation, and it is sized rather than started.

Gates: build **701 jobs**, aggregator **698 of 1004** modules reachable, consistency PASS, claims
342, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + **250** algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (be)

### The tree-binding was content-blind — fixed, with a firing specimen

`tree_fingerprint` hashed `git rev-parse HEAD` plus a SHA-256 of `git status --porcelain`. That
porcelain text is a list of **names and status letters**. Editing a file that is already `M` leaves
it byte-identical, so the binding would report *"worktree unchanged during the run"* for a tree that
had moved.

It was found by reading the gate **after it fired**, not by it failing: on 2026-08-23 it correctly
went STALE on a mid-run docs edit, and it did so only because that file happened to go clean → `M`.
A second edit to the same file would have been invisible. **A check that fails open reads identical
to one that passes** — the third time that sentence has been written into this changelog, and the
first time it was earned by a gate rather than by a script.

The fingerprint now carries a third line: a SHA-256 over the **contents** of every dirty path,
untracked directories walked rather than named. Nothing is capped or sampled — a truncated digest
would read as full coverage.

### `-z`, because the obvious fix has its own fail-open

Parsing `git status --porcelain` for paths means unquoting: git C-escapes any path with a space or a
non-ASCII byte. A naive unquote then opens a file that is not there, and an unreadable path hashes
to a **constant** — a second fail-open, in the same function, introduced by the fix for the first.
`--porcelain -z` emits NUL-separated, never-quoted paths and the question does not arise. Rename and
copy records carry their origin as a following entry; that is consumed explicitly.

### Canary 14, and the end-to-end check the canary cannot do

Canary 14 builds three trees with **byte-identical porcelain** and requires three different content
digests, plus a repeat on an unchanged tree so the digest is not merely noisy. Both directions, per
this repo's rule that a convict specimen must discriminate.

Separately, and not as a canary: `tree_fingerprint` itself was run against the live repo across a
content-only edit to an already-dirty file. Porcelain identical, old scheme identical, **new
fingerprint moved**. The canary tests the digest function; that test exercises the gate.

Gates: build 700 jobs, aggregator 697 of 1003 modules reachable, consistency PASS, claims 341 (no
new Lean theorem in this commit), obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 244
algebra-spine field-axiom-checked, sorry-audit 1 allowlisted, **claim-auditor self-test 14 canaries
+ the sorryAx injection**.

## [Unreleased] — 2026-08-23 (bd)

### The last stated assumption, discharged

**The germ form.** No relation holds eventually for *any* function agreeing with `P/Q` on a
tail — the germ, not the formula, is what the statement is about. `germ_relation_impossible`
(`MachLib.BipevGerm`) takes `EvEqF S (pev P · (1/pev Q))` and eleven structural hypotheses to
`False`.

### The predicted tool was not merely heavier — it was unnecessary

Every place in this arc that named the germ gap said it would be carried by
`hasDerivAt_of_agrees_on_tail`, the derivative transfer built in `BipevTail`. `hasDerivAt_of_agrees_on_tail` **is not needed**. `EvRel S Ls` mentions `S` exactly once, as
`exp (S x)`, pointwise, so two functions agreeing on a tail have the same relations by
intersecting two tails and nothing else. `evRel_congr`'s footprint contains no `HasDerivAt`
axiom of any kind.

The reason is that the differentiation happens *after* the relation has been moved onto the literal
rational function, where `hasDerivAt_ratFn` already applies. The germ only ever needs to reach that
function, and reaching it is pointwise.

Fourth prediction in this arc that overshot, and the first where the predicted tool was not needed
at all rather than merely oversized. `hasDerivAt_of_agrees_on_tail` remains correct; the arc does
not consume it, and saying so is cheaper than leaving a reader to assume it is load-bearing.

  minimal degree   predicted well-founded recursion  took a `Nat` budget
  nontriviality    predicted a transcendence input   took an order count
  lower coeff      predicted minimality + descent    took `exp_pos`
  germ transfer    predicted a derivative transfer   took two tails

Gates: build **700 jobs**, aggregator **697 of 1003** modules reachable, consistency PASS, claims
341, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bc)

### The top-level theorem

`proper_relation_impossible` (`MachLib.BipevNonzeroCoeff`). **No proper relation exists.** For `S = P/Q` with an irreducible `q` dividing `Q` but not `P`,
there is no eventually-holding polynomial relation `Σ pⱼ·exp(S x)ʲ = 0` whose leading
coefficient is not eventually zero.

Ten hypotheses, all structural: `q` irreducible, the two characteristic-zero conditions on `q`,
`q ∤ P`, `q ∣ Q`, normality, `Q` nonzero as a polynomial and as a germ. No transcendence input
appears anywhere in the chain.

### The predicted proof was heavier than the needed one — third time

The commit that closed the composition predicted this step would divide the relation by `e^S` and
appeal to minimality for a shorter one. It does not need minimality at all.

**Properness alone suffices** — the nonzero lower coefficient needs no minimality. If every
lower coefficient were eventually zero then `bipev (Ls₀ ++ [v]) x t = t^m · pev v x` on the
common tail, and `t = exp(S x)` is positive, so `pev v x = 0` there. That contradicts properness directly.
`exists_nonzero_lower_coeff` never mentions `hmin`, and `proper_relation_impossible` uses
`exists_minimal_rel` only to *reach* a split relation, not to argue about lengths.

Three predictions in this arc, all naming a heavier tool than the proof used: well-founded recursion
(took a `Nat` budget), a transcendence input (took an order count), minimality (took positivity of
`exp`). The common shape is that the prediction is made while looking at the *statement*, and the
lighter tool only becomes visible once the surrounding lemmas exist.

### One import declined

`mul_eq_zero_of_factor_ne_zero` exists twice in the corpus, in `KhovanskiiReduction` and
`SingleExpKhovanskii`. Both would drag the Khovanskii development in for four lines, so it is
re-proved `private` here — the same call made in (ax) after the `RiemannIntegralFTCPart1` import
took a module from 180 to 337 jobs.

Gates: build **699 jobs**, aggregator **696 of 1002** modules reachable, consistency PASS, claims
339, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (bb)

### The composition closes

`minimal_relation_impossible` threads every link into `False`: the relation on a tail, the
cleared differentiated relation, elimination and descent, eventually-zero-is-zero, the count's
identity, and the pole-order contradiction. It compiled on the first
build — the only correction was a missing `Decidable` instance, because `pconsN`'s zero test is
`Classical.propDecidable` declared **file-locally** in `PolyCanonical` and therefore not inherited.

Three days ago this section of `what_is_proven.md` said the remaining step "needs a transcendence
input". It did not. It needed a `Nat` budget, an elimination, and a count — and the docstring of
every one of the three steps predicted the wrong tool.

### The second characteristic-zero input, and its price

The count needs `q ∤ (m−j)·1`. Over `Real` the arc's second characteristic-zero input is a **theorem**, not a hypothesis:
`not_Pdvd_pnsum_one'` derives `q ∤ n·1` from `zero_lt_one_ax` and `add_lt_add_left` alone — no
`natCast`, no analysis. Over `𝔽₂` with `m−j = 2` it is false — the same
boundary `DerivCoprime` sits on, reached by a different route. `pnsum_one_pos` is nine lines and its
footprint is nine axioms.

That is why this module, like `PolyEvZero`, stays **outside** `algebraSpineModules`. The spine
proper still never learns that `Real` is ordered: the ledger reports 244 field-axiom-checked
theorems, 0 leaking, unchanged by this commit.

### What the composed theorem assumes, said exactly

Two hypotheses are consumed and not produced: `¬EvZeroF (pev u)` for some coefficient below the top,
and that the relation is about `S` *literally* `pev P · (1/pev Q)` rather than a germ agreeing with
it on a tail. Neither is a transcendence input; both are bookkeeping about which coefficient and
which tail.

### A weak check, named rather than papered over

`conclusion_mentions` is near-vacuous for a theorem concluding `False` — every strength claim lives
in the hypotheses. So this claim leans on `hypotheses_count` (15) and on `proof_uses` naming all six
links. A reviewer should read the `#check` output, not the conclusion field.

`docs/what_is_proven.md` §7's "Still not built" paragraph is deleted, and its stale spine count
(222) corrected to 244.

Gates: build **698 jobs**, aggregator **695 of 1001** modules reachable, consistency PASS, claims
337, obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine
field-axiom-checked (0 leaking), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (ba)

### `BipevElimLink` — links two and three, joined

`evRel_elimCoeffs` takes the relation and the cleared differentiated relation, both holding
eventually, to the **eliminated** relation holding eventually. `bipev_elim_eq_zero` is pointwise, so
it is one tail intersection; the lockstep length condition is `dcoeffs_length_eq` from two commits
ago.

`elim_coeff_vanishes` then joins the descent: for a minimal relation split at its leading
coefficient, the `j`-th eliminated coefficient vanishes eventually. This is the composition's second and third links joined: eliminate, descend, and read
off the coefficient at `j`.

### The shape lemma written first, again

Reaching the `j`-th eliminated coefficient needs to know *what* `dcoeffs` has at index `j`:
`padd (Q²·L') ((i+j)·D·L)` when the family starts at index `i`. `dcoeffs_getElem` says so, and it was written before the theorem that needs it
rather than after a failed application — the second time in three commits, and the rule from (ay)
continues to hold.

### One `rw` over-reach, and it was the predicted kind

`rw [hMs, hsplit] at helim` failed: rewriting `hMs` replaced `Ms` **everywhere**, so `hsplit`'s
pattern `dcoeffs QQ D 0 Ms` no longer matched. Fixed by stating `hsplit` at `Ls₀ ++ [v]` directly
instead of at `Ms`.

That is the fourth `rw` over-reach in this arc and the same fix each time — state the fact in the
form it will be used, rather than in the form it was derived. Between this and the four
`cases h : e` substitutions, eight build rounds in this arc have gone to a tactic touching more of
the goal than intended.

Gates: build 697 jobs, aggregator **694 of 1000** modules reachable, consistency PASS, claims 335,
obligations 18 rows, AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-23 (az)

### `BipevTailNonzero` — the shape lemma written *before* the theorem, and then the theorem

Acting on last commit's pattern rather than just recording it. The composition needs `Q(x) ≠ 0` on
the tail where it differentiates, because that is what brick three requires. `pev_ne_zero_on_tail`
says a coefficient list that is not eventually zero is eventually nonzero. The gap between the two is exactly
`pev_dichotomy`, and this is the form the tail bookkeeping consumes.

Writing it first cost nothing and meant the link below assembled without a mismatch — the first
composition step in five commits that did not surface one.

### The first real link: the differentiated relation holds on a tail

`evRel_dcoeffs_ratFn` takes the relation holding eventually to the **cleared differentiated
relation** holding eventually. Every input was already in place: `hasDerivAt_ratFn` for `S'`,
`ratFn_deriv_cleared` for `S'·Q² = D`, `bipev_dcoeffs_eq_zero_on_tail` for the transfer, and the
nonvanishing above for the denominator. It built first try.

Stated for `S` *literally* `fun y => pev P y · (1/pev Q y)` — the function brick three
differentiates. A germ that merely *agrees* with it on a tail is handled by
`hasDerivAt_of_agrees_on_tail`, and is deliberately left a separate step: folding it in here would
have made one theorem carry two different tails and obscured which hypothesis governs which.

### Where the composition actually stands

Links built: relation ⟹ differentiated relation. Links remaining: differentiated relation ⟹
elimination ⟹ descent ⟹ coefficient identity ⟹ `cleared_relation_impossible`, all of whose pieces
and shape lemmas exist.

Gates: build 696 jobs, aggregator 693/999, consistency PASS, claims 333, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-23 (ay)

### `BipevDcoeffsShape` — the same two facts, for the other family

The elimination consumes `Ms` and `dcoeffs QQ D 0 Ms` **in lockstep**, so it needs them to have
equal length; and the drop needs both split at their last coefficient. Neither was stated when
`dcoeffs` was defined, because `BipevClearedDeriv` only ever *evaluated* it — nothing there asked
about its shape.

### The running index is the whole content

`dcoeffs` carries a running index, so splitting off the last coefficient must say which index it
lands at: for `dcoeffs QQ D j (Ls ++ [L])` the appended entry is at index `j + |Ls|`, not `j`. Getting that wrong would produce a coefficient with the wrong
multiple of `D`, which would then fail to match `coeff_identity` — whose entire point is that the
multiple is `m − j`. The error would have surfaced as a mismatched `pnsum` argument two steps later,
which is exactly the kind of thing that is cheap here and expensive if found during the final
assembly.

### A pattern, now on its third instance

`bipev`, `elimCoeffs`, `dcoeffs` — three recursive families in a row where the composition needed a
length lemma and a concat lemma that the defining module had no reason to prove. Stating it:
**a recursive family gets used in lockstep with another one before it gets used alone**, so
its shape lemmas are due at the first pairing, not at its definition.

Gates: build 695 jobs, aggregator 692/998, consistency PASS, claims 331, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-23 (ax)

### `BipevElimDrop` — the predicted argument-matching slip, and it was exactly that

`elimCoeffs` is pointwise, so `elimCoeffs top topD Ms Cs` has **the same length as `Ms`**. Its top
entry is killed — it evaluates to zero everywhere — but it is still *there*. So `Es.length < Ms.length` is false as
stated, and the descent does not apply to `Es` — it applies to `Es.dropLast`.

Two facts close it: `elimCoeffs_concat` (elimination commutes with splitting off the last
coefficient, so the truncation of the eliminated family *is* the eliminated family of the
truncations) and `elimCoeffs_top_eval`, already proved, which makes `evRel_dropLast` apply.

### The prediction was worth making

The previous commit said what remained was bookkeeping and that any surprise would be an
argument-matching slip. It was exactly that: no lemma was wrong, no mathematics
was missing, and the fix is two length facts. Naming the expected failure mode
in advance is what made it cheap to recognise rather than alarming to hit — the shape was known
before the error message was read.

### A junk hypothesis, caught by a warning

The first draft carried `hmin : ∀ Ns, ProperRel S Ns → Ms.length ≤ Ms.length → True` — a vestigial
argument that says nothing. It **compiled**, and only an unused-variable warning flagged it. Removed
rather than shipped: a theorem with a meaningless hypothesis is worse than one with none, because a
caller has to supply it and a reader has to work out that it means nothing. Worth noting that no gate
here would have caught it — the claim auditor checks hypothesis *counts*, not whether a hypothesis
carries content.

Gates: build 694 jobs, aggregator 691/997, consistency PASS, claims 329, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-23 (aw)

### `BipevCoeffIdentity` — step 3, the last step that is not instantiation

The eliminated coefficient at index `j`, with `v = pₘ` and `u = pⱼ`, is
`(Q²·v' + m·D·v)·u − v·(Q²·u' + j·D·u)`, and `cleared_relation_impossible` wants
`(u'v − uv')·Q² ≈ Nc·D·(u·v)` with `Nc = (m−j)·1`. Both sides split into the same four products, and the whole step is recognising that:

```
T₁ = (Q²·v')·u   T₂ = (m·D·v)·u   T₃ = v·(Q²·u')   T₄ = v·(j·D·u)
C ≈ 0  ⟺  T₁ + T₂ ≈ T₃ + T₄  ⟺  T₃ − T₁ ≈ T₂ − T₄
```

with `T₃ − T₁ ≈ Q²·(u'v − uv')` and `T₂ − T₄ ≈ (m−j)·D·u·v`. **No new mathematics** — every step is
`peq_pmul_comm`, `pmul_assoc_pnorm`, `pnsum_pmul` or `peq_pnsum_sub`, all already proved. The
identity itself built first try.

### Two pieces of subtraction algebra, finally named

`peq_of_psub_nil` and `peq_sub_swap`: "a difference vanishing means the
sides agree", and "`A + B ≈ C + D` gives `C − A ≈ B − D`". This arc has needed both repeatedly
without naming them, unfolding `psub` inline each time. Naming them is what makes the identity's
proof a chain of recognisable steps instead of a block of `pscale (0−1)` manipulation — and it is
the difference between a proof a future session can read and one it would rewrite.

### All four composition steps are now reduced

1. instantiate the chain — every link exists;
2. reach the `j`-th coefficient — `elim_coeff_evZero`;
3. rearrange into the count's identity — **this commit**;
4. apply `cleared_relation_impossible`.

Nothing left in the composition introduces mathematics or hypotheses. What remains is threading the
instantiation, which is bookkeeping over ~15 arguments.

Gates: build 693 jobs, aggregator 690/996, consistency PASS, claims 327, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-23 (av)

### `BipevElimMem` — step 2, three lines instead of an indexing theory

The descent concludes `∀ A ∈ Es, EvZeroF (pev A)` — a statement about **membership**, not indices.
So extracting "the coefficient at index `j`" does not need
an indexing theory at all: it needs only that the `j`-th combination *is a member* of
`elimCoeffs top topD Ls Cs`, which is one induction stepping `j` and the two lists together.

Worth recording because "extract the coefficient at index `j`" suggests `List.get`, lengths and
off-by-one bookkeeping, and none of that was needed. The descent's conclusion was already in the
weaker and more convenient form; matching the shape the *consumer produces* rather than the shape
the statement suggests made the step trivial.

That is the same lesson as `PolyDerivShort` two commits ago, now twice in three commits:
**size a step by what its consumer
actually delivers.**

### The composition's remaining work is now fully mapped

1. instantiate the chain — every link exists;
2. reach the `j`-th eliminated coefficient — **done here**;
3. rearrange `C_j ≈ 0` into `(u'v − uv')·Q² ≈ Nc·D·(u·v)` — the `pnsum` lemmas from (au);
4. apply `cleared_relation_impossible`.

Step 3 is the only one not reduced to existing lemmas, and it is `PEq` rearrangement over
`peq_pmul_comm`, `pmul_assoc_pnorm` and `peq_pnsum_sub` — no new mathematics, and no new
hypotheses, since (as) and (at) reduced both external inputs to nonvanishing facts about `ℝ`.

`AxiomLedger` invariant (7): **244 algebra-spine theorems, 0 leaking** (this module is analytic and
correctly outside).

Gates: build 692 jobs, aggregator 689/995, consistency PASS, claims 325, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (au)

### `PolyNsum` — the last algebraic gap before the coefficient identity

The eliminated coefficient is `Q²·(v'u − vu') + (m−j)·D·v·u`, and
`cleared_relation_impossible` consumes it as `(u'v − uv')·Q² ≈ Nc·D·(u·v)` with `Nc = (m−j)·1`.
Getting between the two needs three facts about `pnsum`:

* `pnsum n (A·B) = (pnsum n A)·B` — the multiple slides out of a product, by `pmul_padd_left`.
* `pnsum (a+b) X = pnsum a X + pnsum b X` — additivity of the multiple.
* `pnsum m X − pnsum j X ≈ pnsum (m−j) X` for `j ≤ m`. This is where the degree gap `m − j`
enters the coefficient identity.

The first two are **exact list identities**; only the third is a `PEq` statement, and only because
subtraction of coefficient lists is well behaved solely up to normalisation — the same reason every
subtraction in this arc has been.

### `rw` over-reaching, again, and the fix is the same

`rw [← he]` with `he : j + (m − j) = m` rewrites the `m` **inside** `m − j`. Rewrote the hypothesis
instead. Same shape as `PolyOrd`'s `l = j + (l − j)` and `PolyIrred`'s `q` inside `eea a.length q a`;
the general rule recorded at `PolyOrd` — `rw` acts on every occurrence, including ones inside the
terms you are reasoning about — has now cost a build round three times, and rewriting the hypothesis
has fixed it all three.

`AxiomLedger` invariant (7): **244 algebra-spine theorems, 0 leaking.**

Gates: build 691 jobs, aggregator 688/994, consistency PASS, claims 323, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 244 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (at)

### `PolyDerivShort` — `DerivCoprime` reduces to nonvanishing, without the leading coefficient

The remaining asymmetry from (as). Folding `DerivCoprime q r` looked like it needed the **leading
coefficient** of `pderiv` — index-tracking through the Horner recursion, the same shape that made
`bipev_cleared_deriv`'s correction term non-obvious.

It does not. The degree bound only needs that `pderiv` leaves a **trailing zero**:

```
pderiv (L₀ ++ [a])  =  … ++ [0]
```

one induction, no index arithmetic. `pnorm` strips it, so `pnorm (pderiv L)` is strictly shorter
than `L`, and `not_Pdvd_of_length_lt` finishes. **The leading coefficient is never computed.**

That is the second time in two commits that a step sized as "needs the leading coefficient" needed
only a length fact instead. Both times the cheaper route was found by asking what the *consumer*
needs — a degree bound — rather than what the natural statement about derivatives would be.

### The composition's two inputs now have the same shape

`DerivCoprime q r` reduces to `pnorm (pnsum r (pderiv q)) ≠ []`, and the constant input reduces to
`natCast n ≠ 0`. Both are now nonvanishing statements
about specific polynomials, both false over `𝔽₂`, and neither carries any divisibility content.

`pnsum` commutes with `pderiv` (because `pderiv` is additive), which is what lets the length bound
apply to `pnsum r (pderiv q)` without a second argument.

### `cases h : e` substitutes, for the fourth time

`rw [hp] at hlen ⊢` failed because `cases hp : e` had already rewritten the goal. Fourth occurrence
in this arc, and the fix is always the same: rewrite only the hypotheses that still mention the term.
Recorded again because it is now the single most repeated Lean-local cost here.

`AxiomLedger` invariant (7): **236 algebra-spine theorems, 0 leaking.**

Gates: build 690 jobs, aggregator 687/993, consistency PASS, claims 321, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 236 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (as)

### `PolyConstDvd` — separating the second input's field content from its polynomial content

`cleared_relation_impossible` needs `q ∤ Nc` for the constant `Nc = n·1`. That *looks* like another
divisibility fact, and it is not: `Pdvd_length` already says a divisor is no longer than what it
divides, so an irreducible — degree `≥ 2` by definition — cannot divide anything
of degree `0`. The only way `q ∣ Nc` can hold is `Nc ≈ 0`.

So the input reduces to **`Nc ≉ 0`**, which is `natCast n ≠ 0` — a statement about `ℝ` with no
polynomial content at all.

Doing this **before** the composition rather than after is the point. The composition fixes what the
final theorem's hypotheses look like, and a hypothesis phrased as "`q` does not divide this
constant" would have hidden that its content is characteristic zero and nothing else — leaving the
end statement carrying two inputs that appear to be about different things when they are the same
fact about `ℝ` twice.

### One induction replaced by an existing lemma

`pnsum_one_length` first tried a nested induction with `cases h : e` inside it, which does not
compose — the outer hypothesis still mentions the term the inner `cases` substituted away. Replaced
by one application of `padd_length_ge`: `padd` against a length-one list never lengthens it. Third
time in this arc that reaching for an induction where a length lemma already existed cost a build
round.

`AxiomLedger` invariant (7) now covers **228 algebra-spine theorems, 0 leaking**.

Gates: build 689 jobs, aggregator 686/992, consistency PASS, claims 319, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 228 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ar)

### `BipevRatFn` — the last ingredient, and it adds no hypothesis

`hasDerivAt_ratFn` (brick three) gives `S' = P'·(1/Q) + P·(−Q'/(Q·Q))`. Everything downstream wants
`S'·Q² = D` with `D = P'Q − PQ'` — the hypothesis `bipev_dcoeffs_eq_zero_on_tail` takes and the
identity `cleared_relation_impossible` is stated against.

The conversion is one field computation, and the only thing it needs is `Q(x) ≠ 0` — which is
already carried, since brick three needs it to differentiate at all. **No new hypothesis enters**, which was worth checking rather than assuming:
a composition step that quietly added a side condition is exactly the thing that surfaces only at the
end, and the previous two commits both found mismatches of that kind by applying rather than
inspecting.

### Every piece of the differential route now exists

```
exists_minimal_rel  →  bipev_dcoeffs_eq_zero_on_tail  →  bipev_elim_eq_zero
                    →  all_coeffs_evZero_of_shorter'  →  pnorm_eq_nil_of_evZero
                    →  cleared_relation_impossible
```

with `ratFn_deriv_cleared` supplying the `S'·Q² = D` link. What is **not** done is the final
composition itself — instantiating that chain end to end.

### The one thing I know the composition still needs

`cleared_relation_impossible` wants `q ∤ Nc` for the constant `Nc = n·1`, `n = m − j`. Since `q` is
irreducible its degree is `≥ 2`, so `q ∣ c` for a constant `c` forces `c = 0` by degree — meaning
`q ∤ Nc` reduces to `n ≠ 0` **in `ℝ`**, a second characteristic-zero input alongside `DerivCoprime`.

Both are the same fact about `ℝ` and could be folded into a single named hypothesis, but deriving
`DerivCoprime` from it needs the leading coefficient of `pderiv`, which is not built. Recording this
now rather than discovering it mid-composition, since that is the pattern that has held for the last
three commits.

Gates: build 688 jobs, aggregator 685/991, consistency PASS, claims 317, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (aq)

### `BipevDescent` — the last structural piece

The gap named at the end of (ap). The eliminated relation has its top coefficient eventually zero,
so by `bipev_concat` it agrees with its own truncation. That truncation is a relation too, and it is
*shorter* — so minimality forbids it
from being proper, forcing **its** top coefficient to be eventually zero as well, and the argument
repeats. Every coefficient of the eliminated relation vanishes
eventually, which is the single-coefficient identity `cleared_relation_impossible` consumes.

### The one induction in the arc that runs from the right

Every other list induction here runs from the head, because `pev`, `pnorm`, `pmul` and `bipev` all
recurse there. This one cannot: "top coefficient" is the *last* entry, and the descent
is precisely peeling it. So the list is decomposed as `Es₀ ++ [A]` and
the recursion is on a length budget rather than on the constructor — the same `Nat`-budget shape as
`exists_minimal_length`, for the same reason, and the fourth distinct place in this arc where a
budget replaced the structural recursion that looked natural.

### What it does not need

No minimality of the *eliminated* relation, no properness of it, and nothing about `q`. The inputs
are that the ambient minimal relation exists and that the shorter thing is a relation at all. Worth
noting because the natural first statement — phrased in terms of the eliminated relation's own degree
— would have needed the elimination's details, and this needs none of them. The elimination and the
descent are independent, which is why they could be built in either order.

Gates: build 687 jobs, aggregator 684/990, consistency PASS, claims 316, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ap)

### `BipevTail` — the assembly's first mismatch, found by applying

Brick four's `dbipevExp_eq_zero_of_relation_off_finite` transfers the derivative when the relation
holds **off a finite set** — the shape the `C₀` work needed, where exceptional sets are finite. The
differential route's relations hold **on a tail**, and the complement of a tail is not finite, so
that lemma does not apply.

For a tail the witness is explicit and better than the finite-set one: at any `x > X`, the radius
`x − X` works, because `|y − x| < x − X` forces `y > X`. No avoidance argument and no `Classical.em`.

Brick four is not wrong; it answers a neighbouring question, having been written before the route
was known and against the exceptional-set shape its surroundings used. This is the kind of gap that only appears when a piece is *applied*, which is why the assembly was worth
starting rather than deferring.

### An import that was heavier than the lemma

`abs_lt_split` lives in `RiemannIntegralFTCPart1`, and importing it pulled this module's build from
180 jobs to **337** — the Fundamental Theorem of Calculus, for one inequality. The footprint was
unaffected (per-theorem checking saw no integration axioms), so no gate would have objected; but the
dependency graph would have said this module needs the Riemann integral, and it does not.

Replaced with `neg_le_abs` from `FPModel`, which imports only `Basic`, `Lemmas`, `Forge`, `Ring`.
Back to **181 jobs**. Worth recording because the failure is invisible to every gate here: **a
footprint measures what a proof uses, not what a module claims to depend on.**

### The remaining gap, named rather than discovered later

The eliminated relation has its top coefficient eventually zero, so it agrees with its truncation;
minimality then forces the truncation's top coefficient to be eventually zero too, and so on down.
That descent — which turns "the eliminated relation is not proper" into the single coefficient
identity `cleared_relation_impossible` consumes — is **not built**. It is an induction on the list
from the right.

Gates: build 686 jobs, aggregator 683/989, consistency PASS, claims 314, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ao)

### `BipevMinimal` — step 1, and the well-founded recursion was not needed

`BipevExpDeriv`'s docstring calls for "a well-founded induction on the degree, on relations rather
than on lists", and entry (an) flagged this as the only step in the arc needing genuine well-founded
recursion rather than a fuel budget.

**That was wrong.** "Minimal degree" is the least element of a nonempty
set of naturals, and the well-ordering of `ℕ` *is* a budget: strong induction on a degree bound
gives it directly. No custom well-founded relation, no termination measure on
relations, nothing the other twenty-two modules had not already done.

The argument in one line: given a relation of length `≤ n+1`, either some relation has length `≤ n`
— recurse — or none does, in which case the one in hand is already minimal. `Classical.em` decides
which, **on a statement about naturals rather than about relations**, which is why nothing about
relations is needed.

### Genericity as a cost measurement

`exists_minimal_length` is stated for an arbitrary predicate on lists over an arbitrary type. It
mentions neither `bipev` nor `exp` nor `Real`, and its footprint is `propext`, `Classical.choice`,
`Quot.sound` — **Lean core alone, zero `MachLib.Real` axioms.**

That is not tidiness. A minimal-degree lemma phrased in terms of relations would have *looked* like
it needed something about relations; stating it generically makes visible that it needs nothing at
all. The same move that made `ord_pmul_norm` delete hypotheses, applied to a whole statement.

### The specialization's footprint says something the generic lemma cannot

`exists_minimal_rel` carries `leR` and `exp` — the *symbols* its statement mentions — and **no order
reasoning axioms at all**: `lt_total`, `lt_trans_ax`, `le_iff_lt_or_eq`, `add_lt_add_left` are absent,
as is `HasDerivAt`. So the argument uses no order reasoning, only the order *vocabulary* `EvRel`
needs to say "on a tail". The registered claim forbids exactly those four, which makes the
distinction checkable. (It was first written forbidding `leR` itself, by copying the generic lemma's
list; the auditor rejected that, correctly — a tail is an order notion and `leR` is unavoidable in
the statement.)

### The predicate needs its second clause

`ProperRel` requires both that the relation holds and that its leading coefficient is not eventually
zero. Without the second clause "minimal degree" is vacuous — padding with zero
coefficients would make every degree achievable.

### All three steps are built

`BipevExpDeriv` listed minimal degree, elimination, and nontriviality. Nontriviality — which that
docstring called "where a transcendence input is genuinely required" — was the pole-order count and
needed no transcendence. Elimination became coefficient algebra once denominators were cleared.
Minimal degree needed a `Nat` budget. **None of the three needed what the docstring predicted.**

Gates: build 685 jobs, aggregator 682/988, consistency PASS, claims 312, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (an)

### `BipevElim` — elimination, and it is **coefficient algebra now**

Step 2 of the three `BipevExpDeriv` listed. With the previous module having made the differentiated
relation's coefficients polynomial, this step is algebra rather than analysis — which was the whole
purpose of clearing denominators there, and it paid immediately: the module built first try and
needs no `exp` reasoning anywhere in its proofs.

The combination `c_m·(relation) − p_m·(differentiated)` has coefficients

```
c_m·pⱼ − p_m·cⱼ  =  Q²·(p_m'·pⱼ − p_m·pⱼ') + (m−j)·D·p_m·pⱼ
```

— exactly `Q²` times the coefficient `CRUX.md` §1 derives, as it must be, since `cⱼ` already carries
one factor of `Q²`. At `j = m` it is `c_m·p_m − p_m·c_m`, which vanishes: **the top term is killed**,
and that is the whole content of the step.

### Stated as an identity, not an implication

`bipev_elim` is an identity, not an implication: it computes the combination's value as
`c_m·(relation) − p_m·(differentiated)` for *any* lists of matching length. The vanishing corollary is one line from it. That ordering matters: an
implication-shaped lemma would have been unusable for the degree-drop argument, which needs the
*value* of the top coefficient and not merely that it is zero when the relation holds.

`bipev_concat` then exhibits the drop — a relation whose final coefficient evaluates to zero
everywhere agrees with its own truncation — and `elimCoeffs_top_eval` supplies that the final entry
does evaluate to zero.

**Two of the three steps are now built.** Minimal degree remains, and it is the only one needing
genuine well-founded recursion rather than a fuel budget — every other induction in this arc,
across twenty-two modules, ran on a list length or a `Nat` budget.

Gates: build 684 jobs, aggregator 681/987, consistency PASS, claims 310, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (am)

### `BipevClearedDeriv` — the differentiated relation, with **polynomial** coefficients

`BipevExpDeriv` differentiates the relation and warns, correctly, that the result is *not the same
shape*: the coefficients contain `S'`, which is rational. That is why `dbipevExp` is an explicit
recursion rather than a coefficient family. Multiplying through by `Q²` turns the
coefficients polynomial:

```
Q²·(pⱼ' + j·S'·pⱼ)  =  Q²·pⱼ' + j·D·pⱼ        D = P'Q − PQ',  S' = D/Q²
```

so the differentiated relation becomes an ordinary `bipev` over polynomial lists — the shape the
elimination needs and the shape `cleared_relation_impossible` ultimately consumes. The distinction
brick four kept visible is now *removed* rather than hidden, which is the right time to do it: it
was worth seeing while the route was uncertain and is worth eliminating now that it is not.

### The induction carries a correction term, and the naive form is false

The obvious claim — `Q²·dbipevExp Ls = bipev (dcoeffs …) ` — is **false**, and instructively so. `dbipevExp` nests its `S'` contributions, so peeling one coefficient
shifts every remaining index by one — the `j·` in `j·D·pⱼ` is exactly a count of how many peels a
coefficient has survived. The statement that inducts is

```
Q²·dbipevExp Ls x + j·D·(bipev Ls x y)  =  bipev (dcoeffs Q² D j Ls) x y
```

with `j = 0` the instance a caller wants. Both are stated, not just the corollary, because the naive
form is the natural first attempt and fails in a way that is easy to misdiagnose as a broken
rewrite.

### Outside the guard, by construction

This module mentions `exp` and inherits `HasDerivAt` through brick four, so it is not registered in
`algebraSpineModules` — **222 algebra-spine theorems, 0 leaking, unchanged.** It is the second module
deliberately outside, after `PolyEvZero`, and together they are the analytic half the boundary in
`PolyEvZero` was drawn to admit.

Gates: build 683 jobs, aggregator 680/986, consistency PASS, claims 308, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (al)

### `PolyEvZero` — the bridge, and the **first module deliberately outside the allow-list**

`pnorm_eq_nil_of_evZero`: a coefficient list whose polynomial vanishes on a tail is the zero
polynomial. This is the step the differential route needs to turn "the eliminated coefficient
vanishes eventually" into the `PEq` hypothesis `cleared_relation_impossible` consumes.

Everything from `PolyCanonical` through `cleared_relation_impossible` — nineteen modules, 222
theorems — stays inside `algebraFootprint`. **This one does not, by design.** It is not registered in
`algebraSpineModules`, so invariant (7) still reports 0 leaking; the exclusion is the statement, not
a loophole.

### Why it must leave, measured

The conclusion is false over a finite field: over `𝔽₂` the
list `[0, 1, 1]` is `X² + X`, which vanishes at every point and is not the zero polynomial. Measured footprint of
`pnorm_eq_nil_of_evZero`: `ltR`, `leR`, `lt_total`, `lt_trans_ax`, `lt_irrefl_ax`,
`add_lt_add_left`, `le_iff_lt_or_eq` — the ordered base and nothing more. No `HasDerivAt`, no
`sorryAx`. The order is spent on exactly one thing, `exists_ge_notMem`: **beyond any bound there is a
point outside any finite list**, which is "`ℝ` is infinite".

That is the third and last face of the obstruction this arc kept meeting — extensionality
(`PolyMulDegree`), characteristic zero (`PolyDeriv`), infinitude (here). All three are the same
fact: `algebraFootprint` is the theory of fields, and fields can be finite.

### A grep that could not fire, for the third time

The footprint check for this module first reported *no* order axioms — because the aggregator had
not been rebuilt and the constant did not exist, so `#print axioms` errored and the grep matched
nothing. Caught by printing the raw output instead of trusting the count. That is the third vacuous
check in this arc (the others were a wrong name prefix and a parser bug), all with the same
signature: **an empty result from a check that never ran looks identical to a clean pass.**

Gates: build 682 jobs, aggregator 679/985, consistency PASS, claims 306, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked (this module
excluded), sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-22 (ak)

### `cleared_relation_impossible` — the count in caller-facing form

Needs only that `q` is an irreducible factor of `Q` that
does not divide `P` — no explicit `q`-adic factorisation. `exists_ord_factor` closes the gap, and the exponent's
positivity comes free: were it `0` then `Q ≈ Q̃` and `q` would not divide `Q` after all.

The characteristic-zero input is quantified over `r` rather than fixed, because the exponent is
produced by the proof and not known to the caller. Slightly uglier as a hypothesis, and honest: for
irreducible `q` in characteristic zero it holds for every `r`.

### Where the algebraic layer stops, stated deliberately

This is the last theorem in the arc that stays inside `algebraFootprint`, and the boundary is worth
drawing rather than discovering. What a caller from the differential route must still supply is the
**cleared identity** as a `PEq` — i.e. as a statement about *coefficients*. Getting there from the
analytic relation requires "vanishes on a tail ⟹ is the zero polynomial", which is
`pev_zero_or_finite_roots` (field-only) **plus** `finite_list_avoidable` (`ℝ` is infinite, and
carries the whole ordered base).

So the next step leaves invariant (7) necessarily, for the third distinct reason in this arc — after
extensionality (`PolyMulDegree`) and characteristic zero (`PolyDeriv`), now the infinitude of `ℝ`.
All three are the same finite-model obstruction wearing different clothes: **`algebraFootprint` is
the theory of fields, and every one of these facts is false in a finite field.** That is not a
limitation to route around; it is the correct place for the algebra to end and the analysis to begin.

`AxiomLedger` invariant (7): **222 algebra-spine theorems, 0 leaking.**

Gates: build 681 jobs, aggregator 678/984, consistency PASS, claims 305, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 222 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (aj)

### The count now holds for **arbitrary** `k` and `l` — the previous version was over-restricted

Entry (ai) stated `ord_cross_lower` and `pole_order_contradiction` with the orders of `u` and `v`
written as `k+1` and `l+1`. That was done to dodge `Nat` truncated subtraction, and it is **a real
restriction, not a cosmetic one**: in the relation the count is aimed at,
`u` and `v` are coefficient polynomials with no reason to be divisible by `q` at all. Requiring `q ∣ u` and `q ∣ v` would have
made the count inapplicable to the very identity it was built for.

Generalised: the left side carries `q^(k+l−1+2(m+1))` and the right side has **exact** order
`m + k + l`, so equating them forces `m + 1 ≤ 0` — false for every `k` and `l`,
truncated subtraction included.

The generalisation cost three small lemmas — `Pdvd_one` (everything is divisible by `q⁰`),
`Pdvd_ppow_mono` (divisibility weakens to smaller powers), and `ord_deriv_drop'` (the order-`0` case
of the derivative bound, vacuous). None of them is deep; the point is that the restricted form would
have looked finished and been useless.

**Entry (ai)'s exponent `q^(k+l+1+2(m+1))` is therefore stale prose**, left in place as the record of
what was true then. The registered claim has been repointed at this entry, so the gate pins live
prose rather than history — a claim that keeps passing against a superseded sentence is exactly the
drift the auditor exists to prevent.

`AxiomLedger` invariant (7): **221 algebra-spine theorems, 0 leaking.**

Gates: build 681 jobs, aggregator 678/984, consistency PASS, claims 304, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 221 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted. (Written first as 219 — an estimate, not a reading. The gate said 221.)

## [Unreleased] — 2026-08-22 (ai)

### `PolyPoleCount` — **`CRUX.md` §3 is formalised**, at arbitrary irreducible `q`

`pole_order_contradiction`: the left side of the identity carries `q^(k+l+1+2(m+1))`; the right
side has **exact** order `m + (k+1) + (l+1)`. Equating them forces
`k+l+2m+3 ≤ k+l+m+2`, i.e. `m+1 ≤ 0`, which is false.

**No real-pole hypothesis. No FTA. Arbitrary irreducible `q`.** The only input beyond the field
axioms is `DerivCoprime`. This supersedes *both* restrictions the frozen specimen `e767940c`
carries — its §3 was proved only for `S` with a genuine real pole, and its §4 costed the general
case at real FTA plus a quadratic division routine.

### The companion bound cost almost nothing

`ord_q(X) ≥ k+1 ⟹ ord_q(X') ≥ k`, and it is a **one-liner** from `peq_pderiv_ppow_mul`: that lemma already exhibits `X'` as `qᵏ·(…)`, so the divisibility is read
straight off the factorisation rather than re-derived. The companion `ord_q(u'v − uv') ≥ k+l−1` then
needs no derivative reasoning at all — `q^(k−1) ∣ u'` with `qˡ ∣ v`, and symmetrically for `uv'`,
closed under subtraction. It had looked like separate work when the count was planned; it was three
lines.

Note the asymmetry: this direction needs **no coprimality**, because it is a bound. `ord_deriv_cross`
is an *identity* and therefore does. That is the whole reason the exactness of `qᵐ` had to be proved
separately — a bound on both sides would have made the count vacuous.

### Canonicity chained without carrying hypotheses

`ord_pmul` needs its first cofactor canonical, for `euclid_lemma`. Chaining it three times would drag
a `PNormal` along for every intermediate product. `ord_pmul_norm` normalises the cofactor at each
step instead — legitimate because `Pdvd` depends only on `pnorm`, so normalising changes neither the
divisibility nor the factorisation. Same move as `pnorm_pmul_right` made available in
`PolyDvdAlgebra`, reused a second time to delete hypotheses rather than proof steps.

`AxiomLedger` invariant (7) covers seventeen modules: **216 algebra-spine theorems, 0 leaking**.
`pole_order_contradiction` itself carries no `ltR`, no `leR`, no `HasDerivAt`, no `natCast`, no
`sorryAx`.

Gates: build 681 jobs, aggregator 678/984, consistency PASS, claims 303, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 216 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ah)

### `PolyPoleOrder` — **the pole-order count**

`ord_deriv_cross`: for `Q ≈ qʳ·Q̃` with `q ∤ P` and `q ∤ Q̃`, the cross term `P'Q − PQ'` factors as
`q^(r−1)·E` with `q ∤ E`. This is the step `CRUX.md` §3 runs on, and the reason the Euclid spine
exists.

With `r = m+1`, the power rule gives `Q' ≈ qᵐ·(T·Q̃ + q·Q̃')` where `T = r·q'`, and
`P'Q ≈ qᵐ·(P'·(q·Q̃))`, so `D ≈ qᵐ·E` with `E = P'·(q·Q̃) − P·(T·Q̃ + q·Q̃')`. Then
`q ∤ E` because modulo `q` it is `−P·T·Q̃`, whose three factors `q` all fails to
divide — `q ∤ P` by hypothesis, `q ∤ T` by `DerivCoprime`, `q ∤ Q̃` by hypothesis — so
Euclid's lemma applied twice finishes.

**The `qᵐ` is exact, not a bound.** That is what makes the count a strict inequality rather than a tautology:
`ord_q(D)` is `r−1` and not merely `≥ r−1`, so equating it against the other side of
`(u'v − uv')·Q² = n·(P'Q − PQ')·u·v` forces `r ≤ 0`.

### Cost, finally settled

**One named hypothesis** beyond the field axioms — `DerivCoprime q r`. The footprint of
`ord_deriv_cross` is field axioms plus Lean core: no `ltR`, no `leR`, no `HasDerivAt`, no `natCast`,
no `sorryAx`. **204 algebra-spine theorems, 0 leaking.**

Three sizings of this step, for the record: two commits ago *free*, one commit ago *two inputs*,
actually *one*. Both wrong estimates came from reasoning about the machinery instead of working the
algebra; only the paper derivation got it right.

### Two `psub` identities that had to be built

`X − (X − Y) ≈ Y` and `(X + Y) − Y ≈ X`. Both were assumed present when the proof was drafted and
neither was — the spine had `(U + R) − U ≈ R` only. Cheap to add, but worth noting as the last
instance of a pattern that ran through this whole arc: **the lemma you reach for mid-proof is more
often absent than the one you plan for.**

Gates: build 680 jobs, aggregator 677/983, consistency PASS, claims 301, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 204 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ag)

### `PolyPowDeriv` — the power rule, and the characteristic-zero input named exactly once

**`(q^(k+1))' ≈ q^k · (k+1)·q'`**, with the multiple as an iterated sum so the
coefficient never leaves the field axioms.

### Why the multiple is `pnsum` and not `natCast`

Writing the `k` as `natCast k` would pull `MachLib.Real.natCast` and its arithmetic into the layer
and — worse — would invite a reader to *discharge* `natCast k ≠ 0`, which is precisely the step this
layer cannot take (last commit's `𝔽₂` correction). As an iterated sum `Z + Z + … + Z` the
coefficient stays inside the field axioms and the characteristic-zero question is pushed to exactly
one place.

### Both characteristic-zero needs turned out to be one

Last commit predicted the count would need *two* named inputs: `q ∤ q'` for the nonvanishing of the
derivative, and `natCast r ≠ 0` for the power-rule coefficient. Working the algebra shows they
collapse: the `qʳ` term contributes `r·q'`, and the requirement is `q ∤ r·q'`. That single condition
covers both, because `q ∣ 0` holds trivially, so `q ∤ k·q'` already implies `k·q' ≠ 0`, hence both.

So `DerivCoprime q r` is the whole extra-field-axiom cost of the pole-order count — one named
hypothesis, false over `𝔽₂` with `q = X²+1, r = 2`, true for irreducible `q` over `MachLib.Real`,
and dischargeable only by leaving the allow-list. `pnsum_deriv_ne_zero` records that it already
implies nonvanishing, so nothing else needs stating.

`AxiomLedger` invariant (7) covers fifteen modules: **192 algebra-spine theorems, 0 leaking**.

Gates: build 679 jobs, aggregator 676/982, consistency PASS, claims 299, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 192 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (af)

### Correcting the previous commit: the pole-order count does **not** fit inside `algebraFootprint`

`PolyOrd` measured `pev_pderiv_cons` as field-only — nine `MachLib.Real` axioms, no `ltR`, no
`HasDerivAt` — and concluded that the pole-order count "can be stated and proved inside
`algebraFootprint`, and invariant (7) will hold across it". **That conclusion was wrong**, and wrong
in a way the measurement could not have caught: it is true of the derivative *operation* and false of
the *count*, which needs `q ∤ q'`, hence `q' ≠ 0`, hence **characteristic zero**.

Characteristic zero is not available here, and not by omission. `algebraFootprint` is the theory of
fields and `𝔽₂` is a model of it; over `𝔽₂`, `q = X² + 1 = (X+1)²` is a square with `q' = 2X = 0`, so `q ∣ q'`;
so `q ∤ q'` is **false in a model of the allowed axioms**, hence unprovable from them.

Measured confirmation of where the missing strength lives: `MachLib.Real.natCast_ne_zero` carries
`ltR`, `leR`, `lt_irrefl_ax`, `lt_trans_ax`, `add_lt_add_left`, `le_iff_lt_or_eq` and
`zero_lt_one_ax`. **In this corpus characteristic zero comes from the order axioms.**

This is the second time the finite-model observation has decided a design question — the first was
extensionality in `PolyMulDegree` — and the first time it has overturned something already written
down. It does not damage the spine: the count will carry `q ∤ q'` as a **named hypothesis**,
everything algebraic stays inside invariant (7), and discharging that hypothesis for `MachLib.Real`
is a separate step that leaves the allow-list *visibly* rather than silently.

### `PolyDeriv` — the derivative laws, all field-axiom-only

`pderiv_padd` and `pderiv_pscale` are **exact** list identities. **`(A·B)' ≈ A'·B + A·B'`**, up to `pnorm` because `pmul (0 :: W) B` sheds a trailing zero.

`pderiv_length` shows the derivative never changes a list's length, which is the degree half of
`deg q' < deg q` and costs nothing. Only the **nonvanishing** half needs characteristic zero — a
clean split worth recording, since it says exactly how much of `q ∤ q'` is free.

Note the module imports `MachLib.PevDeriv`, which transitively carries the analytic axioms. **189
algebra-spine theorems, 0 leaking** — bringing axioms into *scope* does not put them in a footprint,
which is what per-theorem checking is for.

Gates: build 678 jobs, aggregator 675/981, consistency PASS, claims 297, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 189 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ae)

### `PolyOrd` — cancellation, and the `q`-adic exponent is unique

`PolyFactor` proved additivity of a *given* factorisation and said explicitly that uniqueness was
not supplied. This supplies it, so `ord_q` is well defined and exponents can be **compared across an
equation** — which is what a pole-order count actually does.

### Cancellation is degree additivity used a second time

`c·X ≈ c·Y → X ≈ Y` reduces to `c·Z ≈ 0 → Z ≈ 0`, and that is `pmul_normal` plus
`pmul_length`: for canonical nonempty `c` and `Z` the product is canonical of length
`|c| + |Z| − 1 ≥ 1`, hence not the zero polynomial. No integral-domain axiom is invoked: the absence of zero divisors was
already spent once inside `pmul_normal`, and this is that same fact reused rather than a new
assumption.

### Uniqueness

If `A ≈ qʲ·M ≈ qˡ·N` with `q` dividing neither cofactor and `j ≤ l`, cancelling `qʲ` gives `M ≈ q^(l−j)·N`. Were `l > j` that exhibits `q ∣ M`,
contradicting the hypothesis. So
`j = l`, and `Nat.le_total` removes the ordering assumption.

### Sizing answered: the pole-order count can stay algebraic

I flagged last commit that `ord_q(D) = r − 1` for `D = P'Q − PQ'` would be the first place this
spine touches derivatives, and that whether it stays field-axiom-only was not answerable by
inspection. Measured: `pev_pderiv_cons` carries **only** `propext`, `Quot.sound` and nine
`MachLib.Real` field axioms — no `ltR`, no `leR`, no `HasDerivAt`. `pderiv` is a pure coefficient
operation; only the *analytic bridge* `hasDerivAt_pev` is analytic, and the pole-order count does not
need it. **So the count can be stated and proved inside `algebraFootprint`**, and invariant (7) will
hold across it.

### A repeated `rw` failure, now with a rule

Two more instances this module: `rw [show l = j + (l − j) …]` also rewrote the `l` *inside* `l − j`,
and `cases h : e` already substitutes `e` in the goal so a following `rw [h]` has nothing to match.
Both are the shape recorded last commit — **`rw` acts on every occurrence, including ones inside the
terms you are reasoning about.** The fixes are the same each time: rewrite the *hypothesis* rather
than the goal, or compose at term level.

`AxiomLedger` invariant (7) covers thirteen modules: **184 algebra-spine theorems, 0 leaking**.

Gates: build 677 jobs, aggregator 674/980, consistency PASS, claims 295, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 184 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ad)

### `PolyFactor` — an irreducible factor exists, and `ord_q` is additive

The two remaining pieces of the Euclid spine.

### No FTA, and `CRUX.md` §4's cost estimate was wrong

"Every nonconstant polynomial has an irreducible factor" is often reached via factorisation into
linear and quadratic pieces — which over `ℝ` is the fundamental theorem of algebra. It is neither
available here nor needed: induct on a degree budget; either the
polynomial is irreducible and divides itself, or it factors into two nonconstants, the left of which
is strictly shorter and has an irreducible factor by induction.

**The degree of the factor is never inspected.** So `CRUX.md` §4 — frozen in `e767940c`, which costed
this step as needing real FTA *and* a division routine for quadratics — overstated it on both counts.
The correction was predicted in `NEXT.md` on the same day; this is the machine-checked confirmation.

### Where Euclid's lemma is spent

`ord_pmul` is the whole reason `PolyIrred` exists. Given `A ≈ qʲ·M` and `B ≈ qˡ·N` with `q` dividing
neither cofactor, the product is `q^(j+l)·(M·N)`, and the *only* difficulty is showing `q`
still fails to divide `M·N`. That is exactly Euclid's lemma, applied once. The exponent arithmetic
is `peq_ppow_add` and three associativity rewrites.

### What is deliberately not proved

That the exponent is **unique**. `ord_pmul` is additivity of a *given* factorisation, which is what
a pole-order count over an equation between two products needs on each side. Making `ord_q` a
function requires cancellation (`q·X ≈ q·Y → X ≈ Y`, which follows from degree additivity — nothing
new), and that is a separate step. Nothing here should be read as supplying it.

`AxiomLedger` invariant (7) covers twelve modules: **172 algebra-spine theorems, 0 leaking**.

Gates: build 676 jobs, aggregator 673/979, consistency PASS, claims 293, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 172 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ac)

### `PolyIrred` — irreducibility, and **Euclid's lemma**

`q` irreducible, `q ∤ a` and `q ∣ ab` gives `q ∣ b`, and every step is a `PEq` rewrite
over lemmas already proved — nothing new is needed about polynomials.

### Irreducibility stated as non-factorisation, not as a divisor condition

`PIrred q` says `q` is canonical, nonconstant, and admits no factorisation into two nonconstant
polynomials. The alternative — "every divisor is a unit or an associate" — would have to be
*assumed*; the factorisation form **derives** it from `pmul_length`: degree is additive, so a
divisor of a degree-`n` polynomial is either constant or has a constant cofactor. `Pdvd_irred_dichotomy` is that derivation.

### Units need no side condition

A unit is a canonical list of **length one**. Canonicity does the work: a length-one canonical list
is `[u]` with `u ≠ 0`, which is exactly a nonzero constant, so no nonvanishing hypothesis travels
anywhere. "Associate of `q`" is likewise just "same length as `q`". This is the representation
decision from `PolyCanonical` paying off a fifth time.

### A rewrite that reached too far

`rw [← pnorm_eq_self q hqn]` inside `euclid_lemma` rewrote **every** `q`, including the one inside
`eea a.length q a`, producing a goal about `eea a.length (pmul g M) a`. The fix is to compose at
term level — `Eq.trans (Eq.trans (pnorm_eq_self q hqn).symm hM) hcanon` — and take lengths with
`congrArg`. Worth recording as a shape: **when a variable appears inside an index of the term being
rewritten, `rw` is the wrong tool** and term-level composition is the right one.

`AxiomLedger` invariant (7) covers eleven modules: **160 algebra-spine theorems, 0 leaking**.
`euclid_lemma` itself is field-axiom-only.

Gates: build 675 jobs, aggregator 672/978, consistency PASS, claims 291, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 160 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (ab)

### `PolyGcd` — `pmul` commutes, and extended Euclid returns a common divisor

`eea_bezout` proves the identity `g ≈ s·A + t·B`. That is only half of what a gcd is, and
Euclid's lemma needs the other half: `g` divides both inputs. With both halves in hand
the gcd is complete.

### A definition was deliberately *not* changed to dodge a missing lemma

The divisor half turns on `q ∣ B → q ∣ Q·B`. With `B ≈ q·M` that is `Q·B ≈ Q·(q·M) ≈ (Q·q)·M`, and
getting `q` back to the front needs `pmul` to **commute** — the one ring law this spine had not
needed until now.

There was a cheaper route: flip `Pdvd` to `∃ M, A ≈ M·q`, after which the divisor half needs only
associativity and left-distributivity, both already proved and both the cheap direction. That is the
smaller change today and it was rejected: commutativity is a fact the ring should have on record, `ord_q` will want it,
and a definition chosen to dodge a missing lemma tends to be paid for twice.

### Why `pmul` commuting is not a one-liner here

`pmul` recurses on its **first** argument, so `pmul Y (x :: xs)` does not unfold and the naive
induction stalls immediately. The fix is to prove the recursion from the right first —
`pmul X (y :: ys) ≈ pscale y X + x·(pmul X ys)` — which is exact *except* for trailing zeros
(`ys = []` makes the two sides differ by a single `[0]`), so it is a `PEq` statement rather than a
list identity. With it, commutativity is one induction and `padd_left_comm`.

`AxiomLedger` invariant (7) covers ten modules: **151 algebra-spine theorems, 0 leaking**.

Gates: build 674 jobs, aggregator 671/977, consistency PASS, claims 289, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 151 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (aa)

### `PolyPEq` + `PolyBezout` — extended Euclid, and `g ≈ s·A + t·B`

Every statement in this spine since `PolyCanonical` has had the form `pnorm X = pnorm Y`, threaded
by hand through `pnorm_padd_congr`, `pnorm_pmul_left` and `pnorm_pmul_right`. The Euclid step is
where that stops scaling — its invariant is a chain of substitutions into a Bézout identity — so
`PEq X Y := pnorm X = pnorm Y` is named, shown to be an equivalence, and shown to be a **congruence
for every operation**. It is `@[reducible]`, not a quotient: nothing is abstracted and any `PEq`
unfolds back to the list equation. A readability decision, not a foundational one.

### The step turned out to be mostly exact identities

Worth recording because it is the opposite of what the `PEq` machinery suggests. Of the four
substitutions the Euclid step performs, **three are exact list identities** — `pmul` distributing
over `psub` on each side, and `X + (Y − Z) = Y + (X − Z)` — because `psub` is just `padd` composed
with `pscale (0−1)`, so each inherits an exact form already proved. `pdivmod_identity` supplies `A ≈ Q·B + R`, `peq_remainder_of_identity` turns that
round into `R ≈ A − Q·B`, and only associativity enters as a `PEq` step, since `pmul`
genuinely does not associate on the nose. `PEq` is
doing bookkeeping here, not carrying weight, and the module is short because of it.

### A naming hazard, self-inflicted

The congruences are `peq_padd`, `peq_pmul`, … and **not** `PEq.padd`, `PEq.pmul`. A theorem named
`PEq.pscale` shadows `pscale` inside the `PEq` namespace, so the *statement* of the congruence stops
elaborating — `pscale c Y` resolves to the theorem being declared. Same class as `open Real`
shadowing `max`, but caused by my own naming rather than inherited. Only `refl`/`symm`/`trans` stay
in the namespace.

`AxiomLedger` invariant (7) covers nine modules: **144 algebra-spine theorems, 0 leaking** — the
whole spine, canonical form through Bézout, is field-axiom-only.

Gates: build 673 jobs, aggregator 670/976, consistency PASS, claims 287, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 144 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (z)

### `PolyDvdAlgebra` — associativity up to `pnorm`, and divisibility's closure

`Pdvd` is transitive and closed under sums, but neither is available until `pmul` associates — and
it does not associate on the nose (`PolyDvd`: the bracketings differ by trailing zeros). So what is
proved is `pmul_assoc_pnorm`, and that is **not** a weakening: `Pdvd` is itself a statement up to
`pnorm`, so this is exactly the strength its closure properties consume.

### Why the second-argument congruence had to come first

`PolyDvd` needed only `pnorm_pmul_left`. Transitivity needs the other side, and the reason is worth
recording because it removed work rather than adding it. The witness `Pdvd r A` wants is `pmul N M`,
which has no reason to be canonical, and `Pdvd` requires canonical witnesses. Taking
`pnorm (pmul N M)` instead is legitimate only if `pmul` cannot tell the difference — which is
`pnorm_pmul_right`. With it, **every witness normalises on the way out**, and the `N = []` /
`M = []` edge cases disappear entirely instead of each needing a branch.

Both congruences reduce to the same two facts as every previous one (`pnorm_padd_congr` and
`pnorm_decomp`), and the `padd`-left form is one `padd_comm` from the `padd`-right form already
proved. That is now the **third** time a lemma in this spine landed cheaply because an earlier
module took the harder general form.

### One lemma cost more than its mirror image, and it is the expected one

`pmul_padd_left` was one induction because `pmul` recurses on its first argument. `pmul_padd_right`
needs `pscale_padd` first and then the same four-term rearrangement — the extra cost is exactly the
asymmetry the earlier "keep the quotient on the left" decision was avoiding. Paid here, once,
because divisibility's closure under sums genuinely needs the right-hand form.

`AxiomLedger` invariant (7) covers seven modules: **116 algebra-spine theorems, 0 leaking**.

Gates: build 671 jobs, aggregator 668/974, consistency PASS, claims 285, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 116 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (y)

### `PolyDvd` — divisibility, with two choices that are not decoration

`Pdvd q A` says some `M` makes `q·M` share a normal form with `A`. On coefficients, because the
transport back from `pev` is refutable over `𝔽₂` and there is no functional definition available to
this layer.

**The witness is required canonical.** `Pdvd` carries `PNormal M`, not merely `∃ M`. That is exactly
what makes the degree bound free: with `q` and `M` both canonical and nonempty, `pmul_normal` says
`pmul q M` is *already* canonical, so `pnorm` does nothing and `pmul_length` reads the degree off
directly. Without it every degree argument would first have to normalise the witness.

**`pmul` is not associative on the nose**, and it is worth knowing why before anyone tries to prove
it. `pmul (pmul [x] Y) Z` and `pmul [x] (pmul Y Z)` differ by trailing zeros — concretely
`padd (pscale 0 Z) [0]` versus `[0]`, equal only when `Z` has length one. So associativity, and with
it transitivity of divisibility, is a statement **up to `pnorm`**, which is what forces the
congruence below rather than any deficiency in how it was stated.

### The `pmul` congruence was cheap because the `padd` one was paid for

`pnorm (pmul L M) = pnorm (pmul (pnorm L) M)` looks like it should cost what its `padd` counterpart
cost in `PolyDivIdentity`. It did not. `pmul` recurses on its first argument's head *into a `padd`*,
so stripping a trailing zero from the left argument is one application of `pnorm_padd_congr` plus
the induction hypothesis. The awkward work — separating "shortening changes the length" from
"boundary entries differ syntactically but not propositionally" — was done once and is reused.

That is the second time in this spine that a lemma landed cheaply because an earlier module chose
the harder general form: `padd_concat` for the division descent, and now `pnorm_padd_congr` here.

`AxiomLedger` invariant (7) covers six modules: **103 algebra-spine theorems, 0 leaking**.

Gates: build 670 jobs, aggregator 667/973, consistency PASS, claims 283, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 103 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-22 (x)

### `PolyRingLaws` + `PolyDivIdentity` — the division identity, in coefficients

`pdivmod_spec` states `A = B·Q + R` through `pev`. Divisibility, gcd, Bézout and `ord_q` all need it
as a **coefficient** identity instead, and the transport back from `pev` is refutable in a model of
the allowed axioms (the `𝔽₂` argument recorded last commit). So the transport was done the only way
left: syntactically. `pdivmod_identity` is
`pnorm A = pnorm (padd (pmul Q B) R)`.

**Why the laws are cheap and where they are not.** Two coefficient lists of the same length with
propositionally equal entries *are* equal, so most laws are one induction plus one `mach_ring` per
coefficient. The exceptions are where lengths differ: `padd` pads to the longer argument, and
`pmul [c] M` leaves a trailing `[0]`. Those are exactly the places a `pnorm` or an `M ≠ []`
hypothesis appears, and nowhere else. The quotient is kept on the **left** of `pmul` throughout,
because `pmul` recurses on its first argument and left-distributivity is therefore the cheap
direction — `pmul_padd_left` is one induction, the right-hand version would need commutativity.

**The one genuinely nontrivial ingredient** is that `pnorm` is insensitive to what a summand looks
like below its normal form:

```
pnorm (padd M Y) = pnorm (padd M (pnorm Y))
```

That is *not* free. Shortening `Y` can shorten the sum, and at the boundary the entries differ
syntactically (`m + 0` versus `m`) while being propositionally equal — so the two effects have to be
separated. They are, by stripping one trailing zero at a time (`pnorm_padd_concat_zero`) and by
`pnorm_decomp`: **every list is its normal form followed by zeros**. With that, `pnorm_padd_congr`
follows and the recursion assembles, `pmul_pshift_singleton` supplying the fact that the quotient's
monomial contribution is literally the list the step subtracted.

`AxiomLedger` invariant (7) now covers five modules: **92 algebra-spine theorems, 0 leaking** — the
whole spine from canonical form through the division identity is field-axiom-only.

Gates: build 669 jobs, aggregator 666/972, consistency PASS, claims 281, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 92 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-21 (w)

### Polynomial extensionality is **unprovable** in the algebra spine — a model argument, not a gap

Before building gcd it was worth asking how divisibility should be defined. The functional form
`∃ M, ∀ x, pev A x = pev q x · pev M x` is the tempting one, and it is **closed off**, for a reason
with teeth rather than a missing lemma.

`algebraFootprint` is exactly the theory of fields, and **fields have finite models**. Over `𝔽₂` the
polynomial `X² + X` vanishes at every point and is not the zero polynomial. So
`(∀ x, pev L x = 0) → pnorm L = []` is *false in a model of the allowed axioms*, hence unprovable
from them. There is no clever proof to look for.

Measured, this is exactly where the missing strength sits: `pev_zero_or_finite_roots` is **field-only**
(it is synthetic division), while `finite_list_avoidable` — "there is a point outside a finite list",
i.e. `ℝ` is infinite — carries `ltR`, `leR`, `lt_total`, `lt_trans_ax`, `add_lt_add_left`,
`le_iff_lt_or_eq`, `mul_pos`, `zero_lt_one_ax`.

**Consequence.** Divisibility, gcd and multiplicity must be coefficient-level. A functional
divisibility would force a degree comparison, a degree comparison would force extensionality, and
extensionality would drag the ordered-real base into the layer whose whole point is being algebraic.
Invariant (7) would catch it; the model argument says it could never have been fixed. The canonical
representation chosen in `PolyCanonical` was not merely tidier — it was the only available option.

### `PolyMulDegree` — the product of canonical polynomials is canonical

`ord_q(ab) = ord_q(a) + ord_q(b)` runs on this: multiplying two canonical nonzero polynomials
**cannot** produce a trailing zero, so nothing renormalises and the lengths add.

`pmul` recurses on its first argument's *head* while canonicity is about the *last* entry, so the
product is put in concat form — `pmul_concat_left` writes `pmul (A₀ ++ [α]) M` as
`padd (pmul A₀ M) (pshift |A₀| (pscale α M))`, whose second summand is at least as long and carries
the leading term. `pmul_concat_normal` then reads off a literal `α·μ` at the end, and
`pmul_normal` concludes. **`mul_ne_zero` is the only place the field's absence of zero divisors is
used, and it is precisely what makes degree additive.**

No `Nat.max` appears: `omega` treats it as an opaque atom here, so `padd_length_le` / `padd_length_ge`
are the two one-sided forms the induction actually needs. No `getLast?` reasoning either — the same
concat shape that carried the division descent carries this.

`AxiomLedger` invariant (7) now covers three modules: **74 algebra-spine theorems, 0 leaking**.

Gates: build 667 jobs, aggregator 664/970, consistency PASS, claims 279, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 74 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-21 (v)

### `PolyDivision` — `A = B·Q + R`, the theorem the PRS never supplied

`MultiVarPRS.prsLoop` is already the Euclidean loop in shape, but `reduceOnce` carries only
`reduceOnce_vanish`: *common zeros are preserved*. That is enough for a resultant and **not** enough
for gcd, Bézout or Euclid's lemma, every one of which consumes the identity. `pdivmod_spec` supplies
it for an arbitrary nonzero divisor.

### Where the canonical invariant turns out to be load-bearing

The step subtracts `c·xᵏ·B` with `c = α/β`, `α` and `β` the leading coefficients. If `β` were
allowed to be `0` — which an unnormalised list permits, `[1, 0]` having a trailing zero — then under
this corpus's **totalised** division `c = α/0 = 0`, the step would silently fail to cancel, the
recursion would not descend, and the fuel would run out returning a wrong quotient. `PNormal B` is
precisely what forbids that. Module 1's invariant is not bookkeeping here; it is what makes the
algorithm correct.

### The cancellation is syntactic, not evaluative

Little-endian lists put the leading coefficient last, so cancelling the top term would normally need
`getLast?` reasoning about the difference. Written in concat form it needs none. With `A = A₀ ++ [α]`
and `B = B₀ ++ [β]`:

```
c·xᵏ·B = P ++ [c·β]        A − c·xᵏ·B = padd A₀ (−P) ++ [α − c·β] = D ++ [0]
```

because `c·β = (α/β)·β = α`. **The zero is in the list, not merely a value the last coefficient
evaluates to**, so `pnorm_concat_zero` applies and the length drops — that is the entire descent.
`padd_concat` / `pscale_concat` / `pshift_concat` exist to keep it that way.

### What canonicity buys in the statement

The remainder condition is usually `R = 0 ∨ deg R < deg B`. Canonically it is just
`r.length < B.length`: the zero polynomial is `[]`, of length `0`, and `B ≠ []`, so the disjunction
collapses. One fewer case to carry through gcd and `ord_q`.

### What is claimed, and what is not

The **remainder** is canonical and length-bounded. The **quotient** is `padd (pdivMono …) …` and is
correct only up to `pev` — `padd` can leave a trailing zero, and no claim is made that it does not.
`PolyNF.divMod` normalises both and `pev_pnorm` carries the identity across; that pair
(`divMod` / `divMod_spec`) is the intended public contract, not the list lemmas underneath it.

### The specimen computes rather than instantiates

The first draft of the specimen instantiated `pdivmod_spec` at concrete lists. That proves nothing
the spec does not already prove — it cannot fail unless the spec fails, so it convicts nothing, and
it was replaced. `pdivStep_specimen` and `pdivmod_specimen_remainder_is_zero` **compute**: `x²`
divided by `x` is carried through the step and the whole recursion, and the remainder is shown to be
`[]` — exactly the zero polynomial, not merely something short — with the quotient's value shown to
be `x`. It breaks on an off-by-one in the shift exponent, on a leading term that fails to cancel, or
on a recursion that stops a step early.

`AxiomLedger` invariant (7) now covers `PolyDivision` too: **60 algebra-spine theorems,
0 leaking**. Division uses `div_def` and `mul_inv`, both field axioms; `div_mul_cancel` was proved
locally rather than imported from `DivisionError`, which carries the ordered-real base this layer is
gated against.

Gates: build 666 jobs, aggregator 663/969, consistency PASS, claims 277, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 60 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-21 (u)

### `PolyCanonical` — the representation decision, made once and gated

The Euclid spine needs degree, divisibility, gcd, irreducibility and multiplicity, and every one of
those is a **coefficient-level** statement. `List Real` does not identify polynomials — `[1]` and
`[1, 0]` are the same function and different lists — so that noncanonicity is deleted here rather
than routed around at every use.

**Chosen: normalise once, carry the invariant at type level.** `pnorm` strips trailing (high-power)
zeros; `PolyNF` bundles a list with its normality proof, so canonical polynomials are equal exactly
when their coefficient lists are. Two alternatives were rejected with reasons:

* **`pev` as the equality relation.** Defining `P ≡ Q` as `∀ x, pev P x = pev Q x` is lighter until
  Euclid runs it backwards and needs `(∀ x, pev P x = 0) → P` is the zero polynomial. That buys
  polynomial extensionality and root machinery merely to *identify zero* — the wrong dependency
  direction for a layer meant to sit underneath all of it. **`pev` is the interpretation theorem,
  not the algebra's equality.**
* **A quotient by trailing-zero equivalence.** Clean, mechanically unnecessary, and it makes
  division opaque. One source of noncanonicity: delete it, do not quotient by it.

### The order axioms stay out, and a gate now enforces it

The tempting way to get a degree is `pev_leading_form`, which already extracts an exponent for any
nonzero list. Measured, it carries `ltR`, `leR`, `lt_total`, `lt_trans_ax`, `lt_irrefl_ax`,
`add_lt_add_left`, `le_iff_lt_or_eq` — the entire ordered-real base. Importing that into a purely
algebraic layer would be a regression the ledger would show. So the coefficient zero-test is
**classical equality**, never `instDecLT`/`instDecLE`, and for a canonical nonzero polynomial the
degree is just `length − 1` — which is what lets division terminate on a list length with no
analysis anywhere.

`AxiomLedger` gains **invariant (7)**: every theorem in `algebraSpineModules` must stay inside
`algebraFootprint` — Lean core, the `Real` carrier, and the *field* axioms. It is deliberately an
**allow-list**, because this repo's own gate post-mortem found deny-list shape in three of five
defective gates, and because whole-module coverage means a future declaration is checked without
anyone registering a claim for it. 28 algebra-spine theorems, 0 leaking.

### Cancellation lives inside normalisation

Raw list addition does not preserve the invariant — `[1,1] + [-1,-1]` cancels its leading term — so
the canonical operations are *defined* as `pnorm (raw …)`. Every cancellation is normalisation
rather than a side condition. Same move that made the rational-germ work go through: choose the
representation in which cancellation is canonical computation.

`pnorm` is also split into a one-step `pconsN` and a fold. Written as a single `match` on
`pnorm cs`, every unfolding needs the equation compiler's match shape spelled out at each use and
two proofs died on exactly that; factored, `pnorm (c :: cs) = pconsN c (pnorm cs)` is `rfl`.

### Specimens, and one that convicts

`pnorm` is the representation decision, so it is specimened before anything is built on it: a wrong
normaliser would make every downstream theorem *vacuously* fine, not false. The invariant lemmas are
no substitute either — `pnorm_normal` is satisfied by `fun _ => []`.

The discriminating one is **`pnorm_specimen_interior_zero_survives`**: `[0,1]` is `x`, and a
normaliser stripping zero coefficients rather than *trailing* zero coefficients returns `[1]`, the
constant. This was validated by construction, not by assertion: a deliberately wrong `pnormBad` was
written and machine-checked to **pass** the other four specimens and to be convicted only by this
one (`pnormBad [0,1] = [1] ≠ [0,1] = pnorm [0,1]`).

### Two broken checkers before one worked

Worth recording because the failure mode is the one this project keeps naming. The first footprint
check grepped for `MachLib.Real.ltR` against output produced under `open MachLib`, which prints
`Real.ltR` — it could not have matched anything and reported a clean pass. The second had a parser
bug that split each `#print axioms` block at its closing quote and silently audited nothing, again
reporting no violations. **Both failed open.** The third is validated by a positive control
(`pev_leading_form`, which must trip and does) and the ledger invariant by a canary theorem inserted
into the spine, confirmed to fail the gate with exit 1 naming `MachLib.Real.ltR`, then removed.

Gates: build 665 jobs, aggregator 662/968, consistency PASS, claims 274, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)** + 28 algebra-spine field-axiom-checked, sorry-audit 1
allowlisted.

## [Unreleased] — 2026-08-21 (t)

### The crux of the differential route was mis-typed — it is not a transcendence input

Brick four (`1f8fa3a3`, earlier today) closed with: *"the eliminated relation is trivial exactly when
`(pⱼ/pₘ)' = (j−m)·S'·(pⱼ/pₘ)` … ruling that out is where a transcendence input is genuinely
required."* `docs/what_is_proven.md` §7 (`cc301dae`) repeated it. **Both were wrong about the type of
the step, and the first was also wrong about the sign.** Neither was load-bearing — nothing is
proved from either sentence — but the first is the specification a future session would formalise
from, and the second is the authoritative claim inventory, rewritten this afternoon precisely so it
would stop drifting.

**The sign is `(m−j)`, not `(j−m)`.** The smallest genuine relation settles it by eye:
`p₀ + p₁·exp(S) = 0` gives `p₀/p₁ = −exp(S)`, a constant multiple of `exp(+1·S)` with `m−j = 1` —
the reciprocal of what was written. Confirmed independently by symbolic elimination over abstract
coefficients at `m = 3`, which also reproduces the `yᵐ` coefficient cancelling identically.

**The type is algebra, not transcendence.** Put `W = pⱼ/pₘ`. The trivialising condition is
`W' = n·S'·W` with `n = m−j ≥ 1` — an identity between **rational functions**, the `exp` having
divided out. Cleared of denominators with `S = P/Q` and `W = u/v` it is the polynomial identity
`(u'v − uv')·Q² = n·(P'Q − PQ')·u·v`, and **what refutes it is an order-of-vanishing count**. At a
real `a` with `Q(a) = 0` and `P(a) ≠ 0`, writing `r = ord_a Q ≥ 1`, `k = ord_a u`, `l = ord_a v`:
`ord_a(P'Q − PQ')` is exactly `r−1` (this is where `P(a) ≠ 0` and characteristic zero are spent),
while `ord_a(u'v − uv') ≥ k+l−1`; equating the two sides forces `k+l−1+2r ≤ r−1+k+l`, i.e. `r ≤ 0`.

So the bounded branch closes **on paper** for every `S` with a genuine real pole. Note *which*
germs that is: the route runs on the branch where `F(S) = exp(S)`, which by `Fbasis_of_nonpos`
needs `S ≤ 0` on the tail — so the canonical covered germ is **`−1/x`** (`P = [−1]`, `Q = [0,1]`,
pole at `a = 0`), not `1/x`, which is positive on a tail and therefore sits in the `S > 0` branch
this route does not touch at all. The residual within the covered branch is `S` bounded and
nonconstant with **no** real pole (canonically `−1/(x²+1)`), where the identical count runs at an
irreducible quadratic factor but needs division by a quadratic and real FTA. That is a bounded build, and notably it is
**not** the "genuinely new theory" the 2026-08-20 SPEC costed: the reusable algebraic-over-a-field
predicate that SPEC priced is not on this route at all.

Derivation, and the sympy scripts that checked every step rather than asserting it:
`monogate-research/exploration/bounded_germ_crux_retyped_2026_08_21/`.

### `PevOrder` — `deflate` iterated to full multiplicity

`pev_ord_factor` is the first brick of that count: **a coefficient list is identically zero, or it
factors at a real point as `(x − a)ᵏ · M(x)` with `M(a) ≠ 0`.** `PevRoots` divides out *one* root;
this divides out *all* of them at one point, by the same length-budget induction asking a different
question at each step — where `pev_zero_or_root_list` asks "is there a root **anywhere**?", this asks
"is `a` **still** a root?", so `Classical.em` enters on a quantifier-free question instead of an
existential one.

The exponent is produced **with its witness** (`pev M a ≠ 0`) rather than as a numeric `ord`
function. That is deliberate: the non-vanishing *is* the content, and an `ord` that computed without
carrying `M` would have to re-derive it at every use site.

Footprint, read off `#print axioms` and not from a name-grep: **field axioms only** — 16
`MachLib.Real` arithmetic axioms plus `propext`, `Classical.choice`, `Quot.sound`. No order axiom,
no `HasDerivAt`, no `rolle`, no `sorryAx`. The ledger does not move, and would not have: the
factorisation is synthetic division and nothing else.

**What this is not.** One lemma of the count, not the count. `ord_a` of a product, the two displayed
order facts, and the minimal-degree induction over relations are all unbuilt. The real-pole theorem
is a paper result and should be read as one.

Gates: build 664 jobs, aggregator 661/967, consistency PASS, claims 271, obligations 18 rows,
AxiomLedger **242 pinned (unchanged)**, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (s)

### The authoritative inventory was ten days stale — twenty-one results missing

`docs/what_is_proven.md` is what `CLAUDE.md` calls *"the authoritative claim inventory"* and what its
own header calls *"a reader's front door"*. It was last written **2026-08-11**. None of today's
results appeared in it, and **nothing gates it** — the claim auditor pins CHANGELOG prose, not this
file.

That is the same defect class this session spent the day fixing elsewhere: the tower registry
publishing one relation's answer under another's name, the obligations count reading "four" over
sixteen rows, published pages naming Bessel a Pfaffian tower. **An artifact described as
authoritative that quietly stopped being written.** Flagged three times today and deferred three
times in favour of more theorems, which is precisely how the others got that way.

### The `L_F` lane, added to §7

Written as a lane with its asterisks named, matching the section's existing convention:

* `C₀` characterised **globally** — `zero_query_iff_ratGerm` plus
  `zero_query_finite_exception_normal_form`, with a note on *why* the finite-exception form matters
  (the eventual form is blind to bounded regions, which is where `floor`/`mod` misbehave);
* the two exclusions and the two **different** instruments behind them — substitution into the
  algebraic frame for `log`, level sets for `sign`, the latter being the first lower bound here whose
  obstruction is branching rather than growth;
* `1 ≤ q_F(sign) ≤ 12`, and the finding it carries: **the zero-query barrier is a basis boundary,
  not an expressibility barrier**;
* the level-0 asymptotic toolkit, with the fact that none of it touches a derivative, continuity,
  Rolle or IVT axiom;
* **what is open and precisely where** — including that `q_F(sign) ≥ 2` reduces to `OneQueryLevelSet`
  and *not* to `OneQueryDichotomy`, the distinction this session got wrong once and corrected.

### Checked rather than written

Every theorem name the new lane cites was `#check`ed against the built library (15 names, 0 errors),
and the reproduction command the lane *prints for readers* was run: `#print axioms
ratGermSignedTrichotomy_holds` really does show no `HasDerivAt`, no `rolle`, no `sorryAx`, at 34
axioms. A front-door document that tells a reader to run a command owes them a command that works.

Gates: build 663 jobs, aggregator 660/966, claims 269, obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (r)

### Brick four, mechanical half: the relation differentiates

`BipevExpDeriv`. The earlier bricks differentiate the *pieces*; this differentiates the **relation**
— `t ↦ bipev Ls t (exp (S t))`, the left side of `Σⱼ pⱼ(x)·exp(S x)ʲ = 0`. Each Horner step is a
product `y · (rest)`, so it is one product rule per coefficient, and `y' = S'·y` is what keeps the
result expressed in the **same** `y`. No new transcendental appears, which is the entire reason this
route exists.

`dbipevExp_eq_zero_of_relation_off_finite` then does what the argument actually needs: a relation
vanishing off a finite set has a **vanishing derivative** there — `HasDerivAt_congr` against the
constant `0`, with the neighbourhood supplied by `finite_list_avoidable` from brick three, and
`HasDerivAt_unique` to identify the two derivatives.

### One thing the textbooks write that is false here

Classically the differentiated relation is `Σⱼ (pⱼ' + j·S'·pⱼ)·yʲ = 0`, described as "the same
shape". **It is not the same shape**: those coefficients contain `S'`, which is *rational*, not
polynomial. Recovering a genuinely polynomial relation needs the denominators cleared first.

`dbipevExp` is therefore an explicit recursion rather than a `List (List Real)` coefficient family —
writing it as a family would have hidden exactly that, and the corpus has spent the day learning
that the wrong normal form is how cancellation problems become hard.

### Everything mechanical is now built. What remains is mathematics

1. **Minimal degree** — a well-founded induction on the degree of the relation, not on lists.
2. **Elimination** — combine original and differentiated relation to kill the top term.
3. **Nontriviality of the result**, and this is the crux rather than bookkeeping: the eliminated
   relation is trivial exactly when `(pⱼ/p_m)' = (j−m)·S'·(pⱼ/p_m)` for every `j`, i.e. when each
   ratio is a constant multiple of `exp((j−m)·S)`. **Ruling that out is a transcendence input**; it
   does not follow from any of the mechanics above.

Step 3 is the honest reason this entry claims a half. And the caveat that has not moved all day:
**the positive branch is not this argument** — `F(S) = exp(S) + log(S)` is not `exp` of anything, so
`y' = S'·y` does not hold there at all.

`sorryAx` absent from both new theorems. `HasDerivAt_unique` appears in the second's footprint and
not the first's, which is the expected split: differentiating needs no uniqueness, identifying two
derivatives does.

Gates: build 663 jobs, aggregator 660/966, claims 269, obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (q)

### Brick three: the germ has a derivative, and it is the germ's — not a stand-in's

`RatGermDeriv`. The previous entry named this gap instead of stepping over it: `RatGerm` gives
`f = pev P / pev Q` **off a finite exceptional set**, `HasDerivAt` is pointwise, and
`HasDerivAt_congr` transfers a derivative only across a **neighbourhood**. Getting from *"agrees off
a finite set"* to *"agrees near `x`"* was the missing step.

It is exactly as small as predicted. **A finite list of reals does not cover a neighbourhood of a
point outside it** — the same shape as `list_two_sided_bound`, and the same construction principle:
each `e ∈ E` sits a positive distance from `x`, `two_bound_witness'` shrinks two positive distances
to one beating both, and the induction does the rest. `finite_list_avoidable`.

With it, `hasDerivAt_zero_query`: **a zero-query function is differentiable off a finite set**, with
its derivative given by `pderiv` on the normal form's numerator and denominator. And
`hasDerivAt_exp_zero_query` composes that with `y' = S'·y`, so the identity the argument turns on now
applies to a **genuine zero-query argument** rather than an explicit stand-in.

The exceptional set needed no extending: `zero_query_finite_exception_normal_form` already
guarantees the denominator is nonzero there, which is precisely the quotient rule's hypothesis. Two
theorems built a month apart fitting without adjustment is usually a sign the earlier statement was
the right one.

### The route, restated

* brick 1 — `pderiv`, polynomial differentiation in Horner form ✔
* brick 2 — `y = exp(S) ⟹ y' = S'·y` ✔
* brick 3 — the germ inherits its representative's derivative ✔
* brick 4 — **differentiate the relation** and drop its degree against minimality — *not built*
* and the caveat that has not moved: **the positive branch is not this argument**, since
  `F(S) = exp(S) + log(S)` there is not `exp` of anything

`sorryAx` absent from all five new theorems. `HasDerivAt_congr` appears in the footprint of the two
transfer theorems and not in `finite_list_avoidable`, which is the expected split — the avoidance
lemma is pure list arithmetic and the analytic axiom enters only at the transfer.

**The claim auditor rejected this entry's first registration**, and correctly: it credited
`hasDerivAt_zero_query` with invoking `HasDerivAt_congr`, which the proof does *not* do — the
congruence is invoked one level down, inside `hasDerivAt_of_agrees_off_finite`. The axiom footprint
is where that dependency legitimately shows up; `proof_uses` is about the composition the proof
performs. Fixed to credit the wrapper. Third time today the gate fired on the author.

Gates: build 662 jobs, aggregator 659/965, claims 268, obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (p)

### Brick two: `y = exp(S)` satisfies `y' = S'·y`

`ExpCompDeriv`. This is the identity the differential argument turns on — a polynomial relation in
`y = exp(S(x))` differentiates back into a polynomial relation **in the same `y`**, no new
transcendental appearing, which is what makes a degree drop against minimality possible.

It costs two lines given the chain rule, and that is the point: the expensive part of this route is
not the step everyone names, it is the bookkeeping around it. `hasDerivAt_exp_ratFn` assembles the
composite — `exp` of a rational function with its derivative through `pderiv` — as a single term.

**The chain rule was already in the corpus.** `hasDerivAt_exp_comp` has been in
`EMLTChartKhovanskii` since the Khovanskii work; the build caught the duplicate on the first
compile. Second time today that grepping before writing would have been cheaper — the first cost a
published claim, this one cost a rebuild. What is added here is only the factor order that makes
`y' = S'·y` readable, plus the composite.

### The gap that is named rather than papered over

`RatGerm` says `f = pev P / pev Q` **off a finite exceptional set**, and `HasDerivAt` is pointwise —
`HasDerivAt_congr` transfers it only across a **neighbourhood**. Getting from "agrees off a finite
set" to "agrees near `x`" needs a finite-set-avoidance step this corpus does not have.

So every statement here is about an **explicit function**, not a germ, and the quotient rule is
stated for `pev P · (1 / pev Q)` — the function literally differentiated — rather than for
`pev P / pev Q`. The two agree wherever the denominator is nonzero. The difference is only about
which function the theorem is *about*, and conflating them is exactly the quiet step this file
declines to take. `PevRoots` makes the exceptional set finite, so the transfer is available in
principle and is simply **not built**.

That is now the next brick, and it is a smaller one than it looks: a finite list of reals does not
cover a neighbourhood of a point outside it, which is the same "no finite list exhausts an interval"
shape as `list_two_sided_bound`.

Gates: build 661 jobs, aggregator 658/964, claims 267, obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (o)

### Into the differential route: differentiating a coefficient list

`pderiv` / `hasDerivAt_pev` (`PevDeriv`). **One brick, and only one** — named as such because the
temptation here is to describe an ingredient as a route.

Today's two envelope theorems proved that no growth argument can reach the bounded branch:
`F ∘ S` is polynomially enveloped there, so every instrument in this corpus has a **false**
hypothesis. `BoundedGermTranscendence`'s own docstring anticipated exactly this — *"a bounded `F ∘ S`
is indistinguishable from an algebraic function by any envelope, which is why the route through
differentiation is the one on offer"* — and that prose is now backed rather than asserted. So:
differentiation.

### The Horner-native derivative

The obvious definition scales each coefficient by its index, which needs an index-carrying recursion
and a lemma relating it back to Horner form. The Horner-native one needs neither:

```
pderiv []        = []
pderiv (_ :: cs) = padd cs (0 :: pderiv cs)
```

because `pev (padd cs (0 :: pderiv cs)) x = pev cs x + x·pev (pderiv cs) x` **is** the product rule
applied to `c + x·P(x)` — and it follows from `pev_padd` alone. The dropped head is differentiation
killing a constant; the `0 ::` is the shift multiplication by `x` induces.

Checked against a concrete instance, not just proved in general: `pderiv [c, a₁, a₂]` evaluates to
`a₁ + 2a₂·x`.

### On the trust surface, precisely

This is the first result in the arc whose **footprint** contains analytic axioms — `HasDerivAt`,
`_add`, `_const`, `_id`, `_mul`. The **ledger is still 242**, and the distinction matters: those
axioms already existed in the corpus and are used elsewhere, so the *corpus's* trust surface did not
grow. What grew is *this arc's*. Fifteen results held the arc analytic-free and declined the analytic
route three times where it was available; spending it here is deliberate, because the bounded branch
was **proved** unreachable without it.

### What is not claimed, and the plan that is

`hasDerivAt_pev` does not prove `BoundedGermTranscendence` and is not progress on it beyond supplying
an ingredient. The remaining bricks are named in the module so the next session starts from a plan:
the quotient rule for a rational germ, the chain rule giving `y' = S'·y` for `y = exp(S)` (**the step
the whole argument turns on**), differentiating the relation to drop its degree against minimality —
and then the honest one:

**the positive branch is not this argument.** On `S > 0`, `F(S) = exp(S) + log(S)`, which is not
`exp` of anything, so the `y' = S'·y` step does not apply as stated. That branch needs its own
treatment and must not be assumed to follow by symmetry — the two sides have now diverged twice in
one day.

Gates: build 660 jobs, aggregator 657/963, claims 266, obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (n)

### The bounded branch does not evaporate — and now there is a theorem saying why

`Fbasis_bounded_of_floor` / `polyEnvelope_of_Fbasis_floor` (`BoundedGermEnvelope`). `NEXT.md` said:
classify, feed the cases into `F`, and hope most of the bounded branch evaporates the way the last
several hard residues did. **It does not**, and the obstruction is structural rather than a failed
attempt.

On the **nonzero-floor** branch, `ratGerm_eventual_sign` makes `S` one-signed and the floor keeps it
away from `0`, so eventually `S` lives in a compact annulus `c ≤ |S| ≤ K` on one side of zero:

* **negative side** — totalisation deletes the logarithm outright, `F(S) = exp(S)`, and `S < 0`
  gives `exp(S) < 1`;
* **positive side** — `F(S) = exp(S) + log(S)`, with `exp(S) ≤ exp K` and `log c ≤ log S ≤ log K`.

Either way **`F ∘ S` is bounded** — and therefore has a polynomial envelope, a constant one.

### Why that settles the method though it settles no theorem

Every exclusion instrument in this corpus works by **escaping a polynomial envelope**:
`not_polyEnvelope_of_ge_exp`, `..._scaled`, and through them `FS_not_algebraic_of_ge_linear`,
`_of_le_linear`, `Fbasis_not_algebraic`. Each needs the generator to outgrow every polynomial.

`polyEnvelope_of_Fbasis_floor` says their hypothesis is **false** here — not narrowly missed, false.
So the silence of every existing instrument on this branch is now a theorem rather than an
observation, and a future session cannot lose a day rediscovering it.

**The suspicion in `NEXT.md` is confirmed and sharpened.** The nonzero-finite-limit case is the
survivor, and it survives *for a reason that is now proved*. Anything that closes
`BoundedGermTranscendence` there must come from somewhere other than growth — differential algebra,
or transcendence of `exp` on a compact set. That is precisely the specimen `NEXT.md` said would earn
bringing such machinery in, and it has now earned it.

### The decaying branch, closed in the same session

`polyEnvelope_of_Fbasis_decay`. The paragraph above originally left this open and said the symmetry
was likely but unproved. It holds, and the positive side is the only one needing an argument: there
`log S → −∞`, so `F ∘ S` is genuinely **unbounded** — but only *logarithmically*, and that is still
inside a polynomial envelope.

The bound comes from the decay having a **floor of its own**: a rational germ cannot decay faster
than some `c·x^{−m}`, so `log S ≥ log c − log(x^m)`, and `log(x^m) ≤ x^m − 1` converts the logarithm
into a polynomial **without ever computing `log(x^m) = m·log x`** — which would have cost an
induction and a `natMul` bound for nothing.

**So every bounded rational argument gives `F ∘ S` a polynomial envelope.** The structural
obstruction covers the whole bounded region, not half of it.

**34 axioms, `sorryAx` absent** across all three theorems here, ledger still 242.

Gates: build 659 jobs, aggregator 656/962, claims 265 (verdict tree-bound), obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (m)

### The bounded classification, limit-free — decay or a nonzero floor

`ratGerm_shape` / `boundedRatGerm_shape` (`RatGermShape`). The first move `NEXT.md` prescribes, and
deliberately **not** a transcendence theorem.

A bounded rational germ classically has a finite limit `a`, with `S − a ∼ c·x^{−m}`, and the split
that matters for `F ∘ S` is `a = 0` versus `a ≠ 0` because totalisation treats them differently.
**This corpus has no limits and does not need them** — the same split is visible in the degrees, and
`pev_leading_form` already exposes those:

| degrees | classically | stated here |
| --- | --- | --- |
| `d_P < d_Q` | `S → 0` | `x·|S x| ≤ K` — decays at least like `1/x` |
| `d_P = d_Q` | `S → a ≠ 0` | `c ≤ |S x|` — a **nonzero floor** |
| `d_P > d_Q` | unbounded | already handled — `c·x ≤ |S x|` |

Saying "`S → 0`" as "`x·|S x|` is bounded" is not a workaround. It is the same content in the idiom
the corpus can state, and it is **stronger** than convergence — it names the rate.

### What the split buys, concretely

With `ratGerm_eventual_sign`, a bounded germ with a **nonzero floor** is eventually of one sign *and*
bounded away from `0`. So `F(S)` has **no branch ambiguity**: `exp(S)` when that sign is negative,
`exp(S) + log(S)` when it is positive. In the **decaying** branch the sign still decides, and
`log S` now carries an explicit logarithmic scale — `S ∼ c·x^{−m}` forces `log S` to grow like
`−m·log x`, which is a scale the corpus can see rather than a bounded quantity it cannot.

That is the whole point of classifying before proving: the bounded region has stopped being one
opaque case and is now three concrete ones, each with a known shape for `F(S)`.

**34 axioms, no derivative, continuity, Rolle or IVT axiom, `sorryAx` absent.** The thirteenth result
today and the ledger still reads 242.

### Explicitly not claimed

No progress on `BoundedGermTranscendence` itself. Nothing here says any of the three branches is
algebraically impossible — only that they are *distinguishable*, and by what. Whether one survives
(the nonzero-floor case is the suspect) is the next question, and it is untouched.

Gates: build 658 jobs, aggregator 655/961, claims 263 (verdict tree-bound), obligations 18 rows, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (l)

### The claim audit now names the tree it certified

`tools/claim_audit/claim_audit.py` fingerprints the worktree (`HEAD` plus a hash of
`git status --porcelain`) **before and after** the run. If it moved, the verdict does not bind and
the gate exits **2** — UNAVAILABLE, never a pass — printing both fingerprints. An unreadable
fingerprint is also exit 2: *a gate that cannot tell you what it certified has not certified
anything.*

**Earned, not speculative.** The audit takes ~12 minutes, and twice today it was launched in the
background before an edit and read afterwards as though it had covered the edit. The second time it
reported **261 claims for a tree that had 262** — green, and about a tree that no longer existed.
Nothing was wrong with the gate; the mistake was attaching its verdict to work done after it started.

> **A gate certifies a repository state, not a work session.**

Validated deterministically rather than by a timed race: two consecutive fingerprints are equal
(control, silent), touching one file makes them differ (specimen, fires), removing it restores
equality. The passing path now prints
`[tree-binding] verdict bound to 1067cc1c… (worktree unchanged during the run)`.

### Level 0 is finished as infrastructure

With today's twelve results the zero-query layer has the full complement one wants *before* attacking
the next one:

```
normal form · finite roots · level sets · leading order · magnitude · eventual sign
```

**All of it algebraic.** `AnalyticFiniteZeros`, Rolle and the IVT were available throughout and used
**zero** times; the axiom ledger reads 242 at the start of the day and 242 at the end. That is not a
coincidence of easy problems — three separate results had an obvious analytic route that was
available and declined.

The next session's plan is written and committed
(`monogate-research/exploration/level1_hostile_spec_2026_08_21/NEXT.md`): **classify bounded rational
germs by finite limit and leading inverse-power term** — not a transcendence theorem. The signed
trichotomy removed the entire unbounded regime, so the hard core, if there is one, is now cornered
rather than merely named.

Gates: build 657 jobs, aggregator 654/960, claims 262 (**verdict tree-bound**), obligations 18 rows,
AxiomLedger 242 pinned, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (k)

### The trichotomy now emits what the instruments take

`ratGermSignedTrichotomy_holds` (`PevSignGerm`). The lemma the previous entry said was missing, and
said would be needed before any of this was usable:

```
RatGermSignedTrichotomy :  bounded  ∨  eventually c·x ≤ f x  ∨  eventually f x ≤ −(c·x)
```

Those two branches are exactly `FS_not_algebraic_of_ge_linear`'s and `FS_not_algebraic_of_le_linear`'s
hypotheses. **The `F ∘ S` dispatch is now performable for every unbounded rational argument.**

### Where the sign comes from

Not from `f`. Nothing is known about `f` beyond the germ identity `f = P/Q`. It comes from `P` and
`Q` **separately** — each decided by `pev_eventual_sign` — and is then combined through the quotient.
The denominator cannot die (the germ hypothesis makes it eventually nonvanishing), so exactly four
cases arise, and each fixes the sign of `f`.

Three of the four are immediate. `p < 0, q < 0` is not: it goes through `p/q = (−p)/(−q)` by cross
multiplication (`div_eq_div_of_cross`, since `p·(−q) = (−p)·q`), after which both arguments are
positive.

`ratGerm_eventual_sign` is the reusable half — **a rational germ eventually has a constant sign** —
and it is worth having on its own, independent of the trichotomy.

**34 axioms, no derivative, continuity, Rolle or IVT axiom, `sorryAx` absent.** The entire level-0
asymptotic classification — magnitude, degree comparison, and now sign — is algebraic end to end.

### What this does and does not change

Does: `Q3`'s step 3 can be dispatched. An unbounded rational `S` now lands on a *proved* instrument
instead of on an absolute value that fits neither.

Does not: **`Q3`'s cost is still two open rows.** `BoundedGermTranscendence` still owns the bounded
branch, and `OneQueryDichotomy` still owns the `N/D` collapse at step 1. Nothing about
`q_F(sign) ≥ 2` has moved. What moved is that the *third* obstruction, added and then removed today,
is genuinely gone rather than replaced by its own missing lemma.

Gates: build 657 jobs, aggregator 654/960, claims 262, obligations 18 rows, AxiomLedger 242 pinned —
unchanged across all twelve of today's results — sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (j)

### The trichotomy was not yet usable, and saying so is the point of this entry

`RatGermTrichotomy` gives `c·x ≤ |f x|`. The instruments it was built to dispatch onto are
**one-sided**:

```
FS_not_algebraic_of_ge_linear    needs   c·x ≤ S x
FS_not_algebraic_of_le_linear    needs   S x ≤ −(c·x)
```

An absolute-value bound feeds **neither**. Discharging the row did not make the dispatch possible,
and noticing that an hour later is better than discovering it inside a proof that was supposed to
consume it.

### The missing ingredient, proved without the IVT

`pev_eventual_sign`: **eventually a coefficient list has a constant sign**, with a dominating bound
on that side — three-way where `pev_dichotomy` is two-way.

The tempting proof is analytic: `|pev L x| ≥ c·x^d > 0` on a tail, so `pev L` does not vanish there,
and a nonvanishing continuous function has constant sign. That is the intermediate value theorem, and
it would put an analytic axiom into the footprint of **every** consumer of the trichotomy — after a
level-0 development that has stayed clear of one throughout.

The algebraic proof is one induction, and it is `pev_dichotomy`'s absorption **with the absolute value
simply not taken**: at `a :: as`, once `x` is past `2|a|/c₀`, the tail term `x·pev as x` exceeds `|a|`
in magnitude and therefore **decides the sign** of `a + x·pev as x`. Sign propagates outward from the
top coefficient — which is what "eventually the leading term wins" has always meant, and the absolute
value in `pev_dichotomy` was hiding it rather than needing it.

**34 axioms, no derivative, continuity, Rolle or IVT axiom, `sorryAx` absent.** Third theorem today
whose obvious analytic route was available and not taken.

### What is NOT claimed

**The germ-level signed trichotomy is not built.** `pev_eventual_sign` is the polynomial-level fact;
assembling it into *"a rational germ is eventually bounded, or eventually `≥ c·x`, or eventually
`≤ −c·x`"* needs the four-way sign combination for `P/Q`, which is easy and is **not done**. Until it
is, the dispatch still cannot be performed, and `Q3`'s cost is unchanged at two open rows.

Stated because "the trichotomy is now usable" is the sentence that wants writing here, and it would
be false by one lemma.

Gates: build 656 jobs, aggregator 653/959, claims 261, obligations 18 rows, AxiomLedger 242 pinned — unchanged
across all eleven of today's results — sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (i)

### `RatGermTrichotomy` discharged — the residue that blocked three arcs was one induction away

`ratGermTrichotomy_holds` (`PevLeading`). Ledgered **open** an hour ago on its third sighting;
**discharged** now. A rational germ is eventually bounded, or eventually grows at least linearly.

**The fix was not a new idea. It was proving two old ones together.**

`pev_dichotomy` gives *some* `k` with `c·xᵏ ≤ |P|`. `pev_envelope` gives *some* `N` with
`|P| ≤ C·xᴺ`. Neither is the degree, and `k ≤ N` in general — so the quotient `|P|/|Q|` sits between
`x^{k_P − N_Q}` and `x^{N_P − k_Q}`, and when those straddle zero the germ is shown neither bounded
nor linear. That looseness is precisely what three separate arcs each routed around.

`pev_leading_form` runs **one** induction and emits **one** exponent with both bounds:

```
pev L eventually zero,  or  ∃ c C d,  c·x^d ≤ |pev L x| ≤ C·x^d   eventually
```

The lower half is `pev_dichotomy`'s absorption argument unchanged. The upper half is *free on the
same induction* — `|a + x·P| ≤ |a| + C·x^{d+1} ≤ (|a| + C)·x^{d+1}` for `x ≥ 1`. **The two halves were
always provable together; they had simply been proved apart**, in two theorems written months apart
for two different consumers, and nobody had needed them to share an exponent until now.

No degree is ever defined. `d` is produced by the induction — incremented at each `cons` whose tail
dominates, `0` where the tail dies and the head does not — which *is* the degree, with no
`List.length` detour and no trailing-zero bookkeeping.

### And then the trichotomy is a `Nat` comparison

With one exponent on each of `P` and `Q`, `Nat.lt_or_ge dP (dQ + 1)` splits it:

* `dP ≤ dQ` — `x^{dP} ≤ x^{dQ}` for `x ≥ 1`, quotient at most `C_P/c_Q`, **bounded**;
* `dQ + 1 ≤ dP` — `x·x^{dQ} ≤ x^{dP}`, quotient at least `(c_P/C_Q)·x`, **at least linear**.

No subtraction of exponents anywhere, which is what keeps it out of `Nat`-subtraction trouble.

**34 axioms, no analytic content** — no derivative, continuity, Rolle or IVT axiom. `sorryAx` absent
from both new theorems, each checked individually. The corpus keeps confirming that this flavour of
polynomial algebra goes through without touching analysis.

### What it unblocks

The three arcs that named it:

1. **`EMLLogNotRational`'s "inverting through `exp`" route** — its docstring calls this *"exactly the
   missing fact"*. That route is now unblocked (the arc itself was already closed by the `x = exp t`
   substitution, so this is an alternative proof, not a new result).
2. **The first `LogQueryLowerBound` attempt**, which wanted the asymptotic form of a germ rather than
   the envelope.
3. **Q3 / `q_F(sign) ≥ 2`** — the dispatch onto the four `F ∘ S` instruments can now be performed.
   **Q3's cost drops from three open rows to two**: `OneQueryDichotomy` and
   `BoundedGermTranscendence`.

Gates: build 655 jobs, aggregator 652/958, claims 260, obligations 18 rows (`RatGermTrichotomy`
open → **discharged**), AxiomLedger 242 pinned, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (h)

### Q3 traced to the end: `q_F(sign) ≥ 2` costs three open rows, and one of them is new

Not a theorem — a **trace**. The rule the spec set was *trace the proof, do not guess the
obligation*, and following `q_F(sign) ≥ 2` to the end of the argument found three stopping points
where the prediction had one.

`T` one-query and equal to `sign`; the global normal form gives `T(x) = C(x, F(S(x)))` off a finite
set. If `T = 1` on the positive ray then `Σⱼ pⱼ(x)·F(S(x))ʲ = 0` there; kill the relation, descend to
every `pⱼ ≡ 0`, conclude `T = 1` off a finite set, contradict at `x = −1`. **Step 4 is only available
because the normal form went global this evening** — the eventual version cannot take it.

**Where it stops:**

* **`OneQueryDichotomy`, at step 1.** Writing `C` as `N/D` is exactly the collapse the corpus refuses
  to assume — denominators are functions of `x` *and* `F(S(x))`. **This refines yesterday's
  correction rather than reversing it**: the dichotomy does not *give* the bound (`sign` is eventually
  constant, so it excludes nothing on its own), but it is an **ingredient**. Neither "the missing
  theorem" nor "irrelevant" was right.
* **`RatGermTrichotomy`, at step 3 — new, and the reason for this entry.** The `F ∘ S` instruments
  come in four cases (grows, decays, bounded, constant), and dispatching an arbitrary rational `S`
  onto them requires knowing *which case it is in*.
* **`BoundedGermTranscendence`**, behind that dispatch — the one the prediction called.

### `RatGermTrichotomy` — a residue on its third sighting

> A rational germ is eventually bounded, or eventually grows at least linearly. Nothing between.

Ledgered **open** (17 rows → 18). Named because it has been the missing ingredient **three separate
times in three unrelated arcs**: the first `LogQueryLowerBound` attempt, the "inverting through `exp`"
route in `EMLLogNotRational` (where it is *"exactly the missing fact"*), and now Q3. A residue that
recurs across arcs is one that should have a name, and this corpus's own convention says so.

Why it is not free: `pev_dichotomy` gives *some* `k` with `c·xᵏ ≤ |P|`, `pev_envelope` *some* `N` with
`|P| ≤ C·xᴺ`, and `k ≤ N` with neither being the degree. Bounded-versus-linear needs actual leading
behaviour — a degree/leading-coefficient development the corpus does not have. Three arcs each routed
around it, which is the signature of a real gap rather than an oversight.

### The prediction, scored honestly

The spec predicted Q3 would run into `BoundedGermTranscendence` *"rather than needing something new"*.
**Half right, and the wrong half is the informative one.** That row does appear — but *behind* a
dispatch that cannot be performed, and the dispatcher is a fourth thing rather than a corollary of
the three. `OneQueryDichotomy` also re-entered, having been written off.

### The recommendation this produces

**Do not attack Q3.** Three stacked open obligations is not a target, it is a reason to pick another.

`RatGermTrichotomy` is the entry worth building: it is elementary, it lives at **level 0** where the
machinery is strong, and it blocks three arcs at once. Sharpening `pev_dichotomy` from *"some `k`"* to
*"the top nonzero coefficient"* would likely discharge it — ordinary polynomial algebra of exactly
the kind `PevRoots` turned out to be, and that took one session with no analysis.

Gates: build 654 jobs, aggregator 651/957, claims 259, obligations **18 rows**, AxiomLedger 242
pinned, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (g)

### Level 1 goes global, and the threshold comes off for free

`one_query_finite_exception_normal_form` (`EMLOneQueryGlobal`):

```
fOcc T = 1  ⟹  ∃ finite E, C, P, Q,  ∀ x ∉ E,  pev Q x ≠ 0
                ∧ T(x) = C(x, F(pev P x / pev Q x))
```

The eventual version (`one_query_normal_form`, `CtxAppliesEv … X`) is what made the whole level-1
layer blind to the bounded region, and therefore useless to both query-cost sandwiches. Removing the
threshold cost **five lines**, because both ingredients were already in place: `one_query_decompose`
is *global* (`CtxApplies`, every real point, no asymptotics), and this morning's
`zero_query_finite_exception_normal_form` handles the inner argument off a finite set. Compose.

The context `C` is still **not** collapsed to a quotient — that needs `OneQueryDichotomy`, and this
theorem does not assume it. What changed is only *where* the statement holds, which was the whole
blocker.

### The reduction, typed — and it is a different obligation than advertised

Having the normal form does not give `q_F(sign) ≥ 2`. What does is the **level-1 analogue of
`zero_query_level_set`**, now stated as its own named obligation:

```
OneQueryLevelSet :  every level set of a one-query function is finite,
                    or is everything off a finite exceptional set
```

and `sign_not_one_query_of_levelSet : OneQueryLevelSet → ¬ ∃ T, fOcc T = 1 ∧ T = sign`, proved.

**`OneQueryLevelSet` is not `OneQueryDichotomy`.** The dichotomy row asks whether a one-query
*context* is eventually zero or eventually nonzero; `sign` is eventually constant, so it is
compatible with the dichotomy and excluded by it never. Yesterday's narrative conflated the two —
they now have separate names, separate ledger rows, and a reduction recorded as an **implication**,
which cannot be mistaken for a discharge.

Ledger: **16 rows → 17**. The section's own prose count moved with it — that sentence has been wrong
before, and it is the kind of number this project has learned to update in the same commit that
invalidates it.

### What this does and does not unlock

Does: the level-1 layer is now stated where the open questions actually live. `q_F^global(exp)`'s
gap is the negative ray; `q_F(sign)`'s is a single bounded point. Neither is visible to an eventual
statement, and both are visible to this one.

Does not: any bound moves yet. Both sandwiches stay exactly where they were —
`1 ≤ q_F(sign) ≤ 12`, `q_F^global(exp) ∈ {1,2}` — because the normal form is a *statement about
shape*, not an obstruction. The obstruction is `OneQueryLevelSet`, and it is open.

Gates: build 654 jobs, aggregator 651/957, claims 259, obligations **17 rows**, AxiomLedger 242
pinned, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (f)

### `q_F(sign) ≤ 12` — the self-division was paying twice for a value it already knew

`sign_query_cost_bounds_tight`. Same sandwich, upper bound halved, and by a better construction
rather than a new theorem.

`posIndicator x = logGap x / logGap x` buys nonvanishing at the price of evaluating `logGap` twice —
`fOcc` counts tree occurrences, and the subterm sits in both numerator and denominator. But on the
positive ray `logGap` is not merely nonzero, **it is the constant `log 2`**. Divide by that constant
instead and one copy suffices:

```
sign x = (logGap x − logGap (0 − x)) / log 2          fOcc = 12, by rfl
```

The self-division trick was solving a problem the construction did not have. That is worth naming as
a pattern: `A/A` is the reflex for "indicator of `A ≠ 0`", and whenever `A`'s nonzero value is a
*known constant*, `A/c` is the same indicator at half the tree.

### What the remaining gap is made of

`1 ≤ q_F(sign) ≤ 12`, and the two ends are not the same kind of uncertainty. The upper bound is a
construction and might still come down. The lower bound needs level-1 machinery.

**[CORRECTED, same day.] This paragraph originally named `OneQueryDichotomy` as the missing theorem
for both this lower bound and `q_F^global(exp) ∈ {1,2}`, and called it "one obstruction under two
sandwiches". That is wrong, and wrong in the exact way this morning's rung-1 plan was wrong.**

`OneQueryDichotomy` asks whether a one-query context is **eventually** zero or **eventually**
nonzero, and `one_query_normal_form` is itself eventual (`CtxAppliesEv … X`). `sign` is eventually
*constant* on the positive ray — an eventual dichotomy is perfectly compatible with it and excludes
nothing. Nor does it serve `exp`: `q_F^eventual(exp) = 1` is already settled by `EFone`, and what
remains open is the *negative* ray, which an eventual statement cannot see either.

So **the eventual level-1 obligation serves neither sandwich.** What both need is the **global**
level-1 normal form — the analogue of `zero_query_finite_exception_normal_form` one level up, with a
finite exceptional set rather than a threshold. That is a different theorem from the ledger row, and
attaching an implied consumer to a row whose statement does not support it is how a residue quietly
acquires jobs it cannot do.

Second time today the same error: a global conclusion drawn from an eventual theorem, at level 0 this
morning and at level 1 this evening. The rung-1 build is the template for the fix, not just a
neighbour of it.

Gates: build 653 jobs, aggregator 650/956, claims 257, AxiomLedger 242 pinned — unchanged across all
six results today — obligations 16, sorry-audit 1 allowlisted. Figures read off the run.

## [Unreleased] — 2026-08-21 (e)

### `1 ≤ q_F(sign) ≤ 24` — a branching operation gets both bounds

`sign_query_cost_bounds` (`EMLSignQueryCost`).

**This corrects entry (d), written an hour earlier.** That entry showed `EF`/`LF` fail off the
positive ray — which is true, and is a theorem — and I read it as closing the corridor. It does not.
**`FTerm.LFneg` is a global logarithm decoder and was already in the corpus**: `LFneg u = F u −
EFneg u`, with `EFneg` reaching `exp` through `F` at the always-negative arguments `−(u²+1)` and
`−(u+u²+1)`, so the totalised log never contributes. `LFneg_eval` carries **no side condition** at
all, and costs three queries where `LF` costs four and only works on the positives.

I looked at `LF`, found the positivity hypothesis, and stopped. The right move was to grep for every
decoder before concluding none of them reaches. Fourth instance of that pattern in this corpus, and
the first where it cost a *published claim* rather than a rebuilt proof.

### The bound

`log` is an `FTerm` everywhere via `LFneg`, `sign` is a finite expression in `log`
(`sign_eq_posIndicator`), so:

```
signT = posIndT var − posIndT (0 − var)        fOcc = 24, by rfl
```

Lower bound `1`: `sign_not_zero_query`, the level-set argument — no growth, no continuity.
Upper bound `24`: an explicit term, evaluated by Lean rather than counted by hand.

**The 24 is deliberately unoptimised.** `fOcc` counts *tree* occurrences and the indicator uses its
`logGap` subterm twice on each side, so a DAG measure sees 12. The gap between 1 and 24 is honest:
the construction was written to be correct, not small. Tightening it is a separate question from
establishing that a sandwich exists at all.

### Why it matters that it is a *branching* operation

Alongside `q_F^eventual(exp) = 1`, this is the second function in the corpus with both bounds
recorded — and the first whose **lower bound comes from a branching obstruction rather than a growth
one**. Every previous lower bound here (`exp`, `F`, `log`) ran through envelopes or the algebraic
frame. This one runs through level sets: the branch is not free and not impossible, it has a price,
and pricing it is what the query hierarchy is for.

Gates: build 653 jobs, aggregator 650/956, claims 256, AxiomLedger **242 pinned — unchanged across
all five results today**, obligations 16, sorry-audit 1 allowlisted.

(Those two figures were first written as 654 and 651/957 — predicted from the previous entry rather
than read off the run, and wrong by one each. Caught before commit. The rule this corpus keeps
relearning: a number in a claim is *computed*, never continued from a pattern.)

## [Unreleased] — 2026-08-21 (d)

### The open step is closed, with a "no": the decoders break at the boundary point

`EF_ne_exp_at_zero` (`EMLDecoderOffPositives`): **the exponential decoder is wrong at `x = 0`.**

The previous entry left one question and named it as the tempting next claim — does
`sign_eq_posIndicator` upgrade to a `q_F(sign)` bound? It needs `log` as an `FTerm`, hence the
decoders `EF`/`LF` off the positive ray. **They do not go there**, and the cheapest possible witness
proves it: not a point far out on the negative ray, but `0` itself.

`Fbasis 0 = exp 0 + log₀ 0 = 1 + 0 = 1` — totalisation deletes the log term, and that is the whole
mechanism. Both `Fbasis` differences in the decoder collapse to `1 − 1`, leaving

```
eval (EF var) 0  =  (0 − log 3) / (0 − log 2) − 1  =  log 3 / log 2 − 1
```

which equals `exp 0 = 1` only if `log 3 = 2·log 2 = log 4`, i.e. only if **`3 = 4`**.

No numerics — no bounds on `exp(−1)`, no interval arithmetic. The refutation is exact, algebraic,
and lands on the boundary rather than deep in the negatives.

### What it settles

* **No `q_F(sign)` sandwich from these decoders.** `sign_eq_posIndicator` stands as a semantic
  representation over `{field operations, totalised log}`.
  **[CORRECTED, same day — see entry (e).]** The sentence that followed here said it "does not
  become a query-complexity bound". That was an overclaim: it does not become one *through these
  decoders*, but `FTerm.LFneg` is a **global** log decoder already in the corpus, and through it the
  sandwich `1 ≤ q_F(sign) ≤ 24` follows immediately. The scoped claim was right; the general one was
  a failure to grep.
* **`EF_eval`/`LF_eval`'s `0 < eval u x` is necessary, not incidental** — worth knowing for every
  future caller, since a hypothesis that is merely convenient invites being routed around.
* **Half of the problem is free after all.** `Fbasis_eq_exp_of_nonpos`: for `x ≤ 0`, `Fbasis x =
  exp x`, because totalisation removes the log term. `exp` needs **no decoder** on the nonpositive
  ray — it is `F` itself. And on the positive ray `exp x = 1 / Fbasis (0 − x)`.

So `exp` is expressible on each ray separately, by two *different* finite expressions, and what is
missing is a single one covering both. That is the same branch the construction was trying to build,
which is a clean statement of where the difficulty actually sits — and a much better place to be
stuck than "the decoders might extend".

Gates: build 652 jobs, aggregator 649/955, claims 254, AxiomLedger **242 pinned — unchanged across
all four results today**, obligations 16, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (c)

### The zero-query barrier is a **basis** boundary, not an expressibility barrier

Both halves now exist, in the same file, and they are not in tension:

```
sign_not_zero_query      no F-free term equals sign, at any size
sign_eq_posIndicator     sign x = H x − H (0 − x),  H built from field ops and TWO LOGS
```

`sign` cannot be arithmetised, and `sign` *is* a finite expression once one totalised transcendental
is in the basis. What separates the two is not "arithmetic versus comparison" — it is **how much
branch information is latent in the chosen basis.** In a totalised one, the answer is: enough.

### The construction, and a simplification worth keeping

```
logGap x = log (2x) − log x
```

* `x > 0` — `log_mul` splits it, `log x` cancels, and what is left is the **nonzero constant** `log 2`;
* `x ≤ 0` — then `2x ≤ 0` too, both logs are `0` by `log_nonpos`, and the gap is `0`.

Divide it by itself: `div_zero` sends the second case to `0`, `self_div` the first to `1`. A
positivity indicator with **no comparison in it**, and `sign x = H x − H (0 − x)`.

The natural form of this construction squares two logs — `log x ² + log (2x) ²` — to dodge
`log 1 = 0`. **The difference needs no squares:** `log (2x) − log x` is *constantly* `log 2` on the
positive ray, so it cannot vanish there, and it vanishes identically off it. One subtraction replaces
a sum of squares and the whole positivity argument that came with it.

### Why the two theorems do not collide

Because `log ∉ C₀` — `logQueryLowerBound_holds`, proved this morning. The indicator is built from the
one function already known not to be zero-query, so no contradiction is available. The three results
of today lock together: `log ∉ C₀`, `sign ∉ C₀`, and `sign` expressible *from* `log`.

### What is NOT claimed

**No `q_F(sign)` bound.** Turning this into an `L_F` *term* needs `log` as an `FTerm`, and the
decoder `LF u = F u − EF u` is documented correct only "wherever `u` is positive" — precisely the
domain this construction leaves. What `EF`/`LF` compute at nonpositive arguments is open, and until
it is settled there is no query-complexity sandwich, only a semantic representation over
`{field operations, totalised log}`. Stated because the sandwich is the tempting claim here.

### And the floor/mod boundary moves

If finite branching is expressible, then `floor`/`mod` cannot be excluded for being "discrete" or for
the language "having no comparison" — that intuition is now refuted by a theorem, not merely
suspected. `H(x − c)` is a threshold, `H(x − a)·H(b − x)` an interval, and any finite piecewise
selector follows. The dividing line has to be **finitely many branch boundaries versus infinitely
many**, which is a zero-counting question and the right shape for the machinery here.

Gates: build 651 jobs, aggregator 648/954, claims 254, AxiomLedger **242 pinned — still unchanged,
no axiom added today**, obligations 16, sorry-audit 1 allowlisted.

## [Unreleased] — 2026-08-21 (b)

### The first exclusion at query level zero, and it is not `floor`

`sign_not_zero_query` (`EMLSignNotZeroQuery`): **no `F`-free term of the language equals `Real.sign`,
at any size.**

The exclusion machinery landed this morning aimed at `floor`/`mod` and could not be *instantiated*
there — this corpus axiomatises `floor` by bracketing only, so it cannot be shown to have even one
infinite level set. Rather than add a `floor` axiom to make the target fit, the target was changed to
one the corpus already pins completely.

`Real.sign` is a **definition**, not an axiom:

```
sign x = if 0 < x then 1 else if x < 0 then −1 else 0
```

so its level sets are fixed by construction — `1` on the whole positive ray, `−1` on the whole
negative ray. Two distinct levels, neither exhausted by any finite list, which is precisely what
`not_zero_query_of_two_infinite_levels` consumes. **No new axiom**, and `#print axioms` confirms the
result touches none of the `floor` axioms.

The supporting lemma is the one that makes "infinitely many" usable in a corpus whose finiteness
witness is a `List`: `list_two_sided_bound` — every finite list of reals has a bound it does not
reach, on both sides.

### What it says about the compiler

`sign` is a Forge-emit primitive (the Perlin-noise gradient builtin), and `Forge.lean` records that
it is "genuinely derived, not an opaque primitive" — a case split over a `Decidable` instance, adding
no axiom. Both are true, and this theorem says what the case split costs:

**`sign` cannot be compiled away into field operations.** Not with more nodes, not with a cleverer
rational form. A backend targeting an `F`-free datapath must implement the comparison; it cannot
arithmetise it. That is a statement about the emitted hardware, not only about the proof language.

### No continuity anywhere

The argument never mentions continuity, and could not: `L_F` is totalised, so its primitives are
already discontinuous (`x/x` is a finite term equal to `1` off zero and `0` at zero). What does the
work is that **a level set of a zero-query function is finite, or is everything off the exceptional
set** — and a ray is neither.

Gates: build 651 jobs, aggregator 648/954, claims 253, obligations 16, AxiomLedger 242 pinned,
sorry-audit 1 allowlisted. `sorryAx` absent from all four new theorems.

## [Unreleased] — 2026-08-21 (a)

### `C₀` is globally rational outside a finite set — and it cost no analysis

`zero_query_finite_exception_normal_form` (`EMLZeroQueryNormalForm`):

```
fOcc T = 0  ⟹  ∃ finite E, ∃ P Q,  ∀ x ∉ E,  pev Q x ≠ 0  ∧  T(x) = pev P x / pev Q x
```

**Correcting yesterday's plan, which was wrong.** It said a `C₀` function is an eventual rational
germ *and therefore* has finitely many discontinuities. That is a **global conclusion from an
eventual theorem**: `RatGerm` controls a tail `x ≥ X` and says nothing below it, while `floor` and
`mod` misbehave everywhere. `ratGerm_of_zero_query` cannot see the bounded part of the line, so it
could never have supported the exclusion it was being recruited for.

The threshold is gone. Totalisation's zeros do not have to be pushed past `X` — they have to be
**named**, and there are only finitely many.

### The missing ingredient was a finite-roots theorem, and the corpus had none

`PevRoots`: **a coefficient list vanishes identically or its roots fit in an explicit finite list.**
The global counterpart of `pev_dichotomy`, which is one-sided (`EvDom` bounds `|P|` only for
`x ≥ X`).

Proved by **synthetic division and nothing else** — `deflate r L`, Horner from the head, with

```
pev L x = (x − r) · pev (deflate r L) x + pev L r        for EVERY r, root or not
```

Stating the division algorithm without the root hypothesis is what keeps it a ring identity instead
of a case analysis; `pev L r = 0` is used only at the call site. The head of `L` never enters the
quotient, so the list gets exactly one shorter and the induction terminates on a length budget.

**No analysis anywhere.** `AnalyticFiniteZeros` was available and was not used: measured footprints
are 21 axioms for `pev_zero_or_finite_roots` and 28 for the normal form, with **no** derivative,
continuity, Rolle or IVT axiom in either. `Classical.em` asks whether a root exists — genuinely
undecidable — and adds nothing, since `Classical.choice` is already in every footprint here.

### The exclusion, and why it is about level sets rather than continuity

`zero_query_level_set`: **every level set of a zero-query function is finite, or is everything off
the exceptional set.** `T(x) = c` off `E` says the polynomial `P − c·Q` vanishes; the dichotomy does
the rest. No continuity is imported, and none is needed.

`not_zero_query_of_two_infinite_levels` turns that into the countertarget shape: a function with two
distinct levels, neither exhausted by any finite list, is not zero-query. `floor` is exactly that —
`0` on `[0,1)`, `1` on `[1,2)`.

Also: **"finite jump set" was the wrong invariant.** Under totalised division `1/x` is discontinuous
at `0` with no finite one-sided limits, so it is not a jump. The right property is *continuous
except at finitely many points*, and the level-set form is stronger and cheaper than either.

### What this does NOT yet close, stated plainly

**The corpus's `floor` is too weak to be the countertarget.** `Forge.lean` axiomatises it by
bracketing only — `floor_le`, `lt_floor_add_one`, `floor_zero` — which does not pin `floor` to be
constant on `[0,1)`; the axiom block's own docstring says the integer-valued facts are not derivable.
So `floor` cannot presently be shown to have even one infinite level set. **The exclusion is ready
and the countertarget is under-specified** — the remaining work is an axiom question about `floor`,
not a theorem about `C₀`.

This is the honest replacement for the atlas's *"modulo is outside because it is discrete; continuous
primitives compose to continuous functions"*. That argument was never available here: `L_F` is
totalised, and `x/x` is a finite term equal to `1` off zero and `0` at zero.

Gates: build 650 jobs (was 648), aggregator 647/953, model, AxiomLedger 242 pinned, obligations 16,
sorry-audit 1 allowlisted. `sorryAx` absent from all six new theorems, each `#print axioms`-checked.

## [Unreleased] — 2026-08-20 (ab)

### `log ∉ C₀` — the obligation is discharged, and the instrument was already there

`LogQueryLowerBound` flips **open → discharged** (`logQueryLowerBound_holds`, `EMLLogNotRational`).
Computing `log` costs at least one `F`-query, with no restriction on the term — the `log` companion
to `fQueryLowerBound_holds`, reached by a different instrument.

**The whole content is a substitution.** The envelope argument that settled `exp` is structurally
blind to `log`: it works because `exp` escapes every polynomial envelope, and `log x ≤ x` sits inside
one. Substituting `x = exp t` — legitimate because `log (exp t) = t` *unconditionally*, no positivity
side condition — turns `log x = P(x)/Q(x)` into

```
Σⱼ (aⱼ − t·bⱼ) · (exp t)ʲ = 0        for all large t
```

a polynomial in `exp t` with coefficients polynomial in `t`, which `exp_not_algebraic` forbids. No
new analysis: **the growth question became an algebraic one, and the algebraic one was already a
theorem.**

The mathematical statement under the query bound is `log_not_ratGerm`: `log` agrees with no quotient
of polynomials on any tail. Since `C₀` *is* the eventual rational germs (`zero_query_iff_ratGerm`,
both inclusions), that is `log ∉ C₀` — and it is the stronger of the two, since it rules out
agreement on a tail, not merely everywhere.

### The nontriviality argument is where the denominator is spent

`exp_not_algebraic` needs the relation to be nonzero, and the corpus hands you a germ, not a
coefficient. The argument that closes the gap costs two lines and no coefficient inspection: the
coefficients are **linear in `t`**, so the `t`-difference of the relation at fixed `y` is exactly
`−Q(y)`. Evaluate a hypothetically-vanishing family at `t = Z` and `t = Z + 1` and subtract, and `Q`
is identically zero — which the germ's nonvanishing denominator forbids. `logRel_not_all_evZero`.

Worth naming because it is easy to miss: **the nonvanishing denominator is spent twice.** Once to
clear the fraction, which is the obvious use, and once here. Nontriviality is not a property of the
shape `logRel` produces — `logRel_zero_all_evZero` exhibits `P = Q = [0]`, whose one coefficient
dies — so without `hQ` the hypothesis of `exp_not_algebraic_of_not_all_evZero` is unavailable and
the argument does not start.

### The refactor was done as an addition, not a restatement

Yesterday's note said the clean version *restates* `exp_not_algebraic` to take "not every coefficient
list is eventually zero", and flagged that as a refactor to start a session with because it changes a
theorem other results depend on. Eight declarations in `EMLFTranscendence` state or consume the
leading form. **Adding `exp_not_algebraic_of_not_all_evZero` beside the original disturbs none of
them and pays the extraction in exactly the same place** — once, inside a theorem, rather than at
each call site. The risk that motivated deferring the work was a cost of the *in-place* restatement,
not of the generalisation, and separating those two made the fiddly part safe to do.

The extraction itself (`bipev_trim`, `EMLBipevTrim`) is constructive: `pev_dichotomy` decides each
coefficient, so a list induction finds the top nonvanishing index with no appeal to `not_forall`.

### Measured, not asserted

- `logQueryLowerBound_holds` and `fQueryLowerBound_holds` have **identical** axiom footprints — 42
  axioms each, set-equal under `#print axioms`. Two different instruments, one trust base.
- `exp_not_algebraic_of_not_all_evZero` carries **41** axioms against `exp_not_algebraic`'s **39**;
  the two added are `Real.div_zero` and `Real.one_div_nonneg_of_pos`, both inherited from
  `pev_dichotomy`'s `c₀/2`, both already ledgered.
- `sorryAx` absent from all eight new theorems (`#print axioms` on each, not a build-green
  inference — `mach_ring` is an all-`try` tactic and a swallowed goal compiles fine).

### The ledger row existed for a proposition that did not

`LogQueryLowerBound` has been a row in the obligations table since yesterday, and there was no
`def LogQueryLowerBound` anywhere in the corpus. `check_obligations.sh` passed the whole time and was
right to: it checks whether a theorem concludes the proposition, and nothing can conclude a
proposition that does not exist. **A row naming a nonexistent proposition is invisible to the gate
that reads the row** — the same blind spot `CLAUDE.md` already records for claims with no registered
theorem. Stating the obligation (in `EMLRationalGerm`, where the row says it lives) is what made the
row checkable; discharging it came after.

Also corrected in that section: it opened *"Four propositions in this corpus have been introduced as
named obligations"* over a table of **sixteen** rows. Prose that counts rows and is not the thing the
gate reads.

## [Unreleased] — 2026-08-20 (aa)

### The route to `log ∉ C₀` needs no new instrument — it needs a substitution

Specced in `monogate-research/exploration/log_query_lower_bound_2026_08_20/SPEC.md`.

Two routes fail. **Direct germ comparison** needs `log x / x → 0`, absent. **Inverting through `exp`**
needs "unbounded rational germ ⟹ at least linear", which is exactly the missing fact — circular.

The route that works substitutes `x = exp t`. Since `log (exp t) = t` unconditionally,
`log x = P(x)/Q(x)` becomes

```
Σⱼ (t·bⱼ − aⱼ) · (exp t)ʲ = 0        for all large t
```

a polynomial in `exp t` with coefficients polynomial in `t` — **precisely the shape
`exp_not_algebraic` forbids**. The growth question becomes an algebraic one, and the algebraic one is
already a theorem.

**That is the finding: `exp_not_algebraic` is a more general instrument than it looked.** Proved for a
transcendence question about `F`, it also settles a *growth* question about `log` once a substitution
moves that question into the algebraic frame. The next move for the lower-bound programme is probably
not another envelope but asking, of each open growth question, whether a substitution puts it in
reach of the algebraic theorem.

### Proved here: the degree-zero case

`log_not_evConst` — an eventually-**constant** germ cannot be `log`. That case needs none of the
plumbing and is now closed.

**And the full build caught a duplicate the per-module build did not.** I wrote a
`log_unbounded_above`; one already existed in `EMLSmoothness`, and stronger (a whole ray, not one
witness). `lake build MachLib.EMLRationalGerm` accepted it; `lake build` rejected it —
*"environment already contains `MachLib.log_unbounded_above`"*. Reused rather than redefined. Fourth
instance today of the same failure mode: **a check narrower than the claim it is asked to support.**

### Not built, and why

The remaining piece is coefficient-list bookkeeping: pad `P` and `Q`, extract the top index with
`(aⱼ, bⱼ) ≠ (0,0)`, transport the tail through `x = exp t`. The clean version restates
`exp_not_algebraic` to take "not every coefficient list is eventually zero" — matching what
`pev_dichotomy` produces — paying the extraction once inside the theorem instead of at every call
site.

**That restatement changes a theorem four other results depend on**, and it is fiddly rather than
deep. Today has already produced three defects of exactly that shape caught late — a `sorry` left in
a working tree, a `assert` that silently did not fire, and a footprint check that failed open. That
is the evidence for beginning this refactor at the start of a session rather than at the end of one.

## [Unreleased] — 2026-08-20 (z)

### ⚠ `fDepth` is **not** a reparametrisation of exponential number — corrected within the hour

The second literature pass reported `fDepth` as "very likely a reparametrisation" of the
log-exp-analytic *exponential number*. That was read off matching **shapes** and does not survive
checking the **base classes**.

Exponential number's base case is **log-analytic**, which already contains `log`. Ours is **rational
germs**, which does not.

| | exponential number | `fDepth` |
| --- | --- | --- |
| `x` | 0 | 0 |
| `log x` | **0** | **1** |
| `exp x` | 1 | 1 |
| `exp(exp x)` | 2 | 2 |
| `exp(log x · log x)` | **1** | **2** |

They agree on the pure exponential tower and diverge wherever a logarithm appears. **Exponential
number counts nesting of `exp` with logarithms free; `fDepth` counts nesting of a generator
containing both.** A different measure, not a rescaling.

So all three of our measures remain unmatched by anything found. That is *weak* evidence of novelty
and is recorded as such: two shallow passes finding no match is not a match not existing.

### The correction exposed a gap in our own results

That comparison table asserts `fDepth(log) = 1` — **`log` costs at least one query**. It is *not
proved*, and the instrument that settled `exp` **cannot** prove it:

> `FQueryLowerBound` works because `exp` escapes every polynomial envelope. `log x ≤ x` sits
> comfortably *inside* one. The envelope argument is blind to `log`.

Ruling `log` out of `C₀` needs the **asymptotic** form of a rational germ (`~ a·xᵏ`, integer `k`)
rather than the envelope: a rational germ is bounded or grows at least linearly, and `log` is
unbounded and sublinear, so it is neither. The ingredients (`log` unbounded; `log x / x → 0`, e.g.
via `log x ≤ 2√x`) are elementary but absent.

`LogQueryLowerBound` ledgered **open** (15 rows → **16**). It is the natural next lower-bound target
precisely because it needs a different instrument — and the corpus currently has exactly one.

## [Unreleased] — 2026-08-20 (y)

### Hostile audit of the `L_F` arc — two attacks land, four fail

Run against the brief "assume this is notation wrapped around elementary identities; try to collapse
it."

**FAILS — the lower bounds are semantic, not construction-specific.** `fQueryLowerBound_holds`,
`fQueryLowerBound_eventual` and `zero_query_lt_one_query_full` all quantify `∀ T : FTerm` over every
term computing the target. They are statements about the function, not about a representation I
happened to pick.

**FAILS — the generator family does not trivialise `F`.** `Fmix` is an affine mixture of the *same
two primitives*, not an arbitrary function. `F` is shown non-canonical, not arbitrary.

**FAILS — the eventual/global distinction is stated, not hidden.** It is exactly what separates
`q_F^eventual(exp) = 1` from `q_F^global(exp) ∈ {1,2}`, and `EFone_fails_globally` is the witness.

**FAILS — `sorryAx` and axiom-witness status hold**, checked in (x).

**LANDS — `C₀` = eventual rational germs was an overclaim.** Only `ratGerm_of_zero_query` (⊆) existed;
the converse was never proved. Repaired: `pevTerm` realises a coefficient list as an `F`-free term
(Horner *is* field operations on constants and the variable), giving `zero_query_of_ratGerm` and the
biconditional `zero_query_iff_ratGerm`. The `=` is now earned.

**LANDS — `C_k` is measure-dependent from `k = 1`, not from some large `k`.** `F(x)·F(x)` needs two
`F` nodes in a tree — `FTerm` has no sharing — and one oracle query in a DAG. So tree-`C₁` and
DAG-`C₁` are **different function classes**, and every `C_k` statement must name its measure.

Everything here uses `fOcc`, the tree measure. Where the measures agree the results transfer:
`fOcc T = 0 ↔ fArgs T = []`, so `C₀` is the same class in both, and the witnesses for
`q_F(exp) = 1` and `C₀ ⊊ C₁` have one `F` node each. The general hierarchy does **not** transfer, and
`fOcc_EFall` versus `FQueriesLe_toFTermFast` already puts the gap at exponential in depth.

### `C₁ ⊊ C₂` — the proposed witness is gone

Both muses suggested proving `exp ∉ C₁` globally and `exp ∈ C₂` by the decoder. **`exp ∈ C₁`
eventually** kills that: `1/F(−x)` is a one-query term. What survives is the *global* question, where
`EFone` genuinely fails and `EFneg` genuinely works — but a global separation needs a global lower
bound, and every lower bound here is eventual. **No candidate witness for `C₁ ⊊ C₂` currently
exists**, in either measure. Recorded rather than left as an assumed next step.

### Hold on Paper I

No `L_F` claim is cited in the finite-depth manuscript, and none should be for a week — the arc is
two days old with 77 commits and no cold review. The pairing the muses describe (Paper I: complexity
in the EML basis; Paper II: what survives a change of basis) is the right shape, and Paper I needs at
most one sentence pointing at it.

## [Unreleased] — 2026-08-20 (x)

### Literature placement, first pass — and the nearest prior art is ours

`monogate-research/exploration/lf_literature_2026_08_20/NOTE.md`.

**`arXiv:2603.21852` — *All elementary functions from a single operator* — is this project's own EML
paper.** It proposes `eml(x,y) = exp(x) − ln(y)` with the constant `1`: a **binary** operator with
**no field operations**. `F(x) = exp x + log₀ x` is a **unary** function **with** them. Neither
subsumes the other, and it proves no lower bounds — so `FQueryLowerBound`, `q_F(exp) = 1` and the
`C_k` hierarchy are new relative to it.

### ⚠ The conventions diverge, and every cheap global decoder rides on ours

The arXiv paper works over **ℂ with the principal branch**, extended by `ln(0) = −∞`. MachLib
totalises differently: `log₀(y) = 0` for **every** `y ≤ 0`. Consequences:

| result | convention |
| --- | --- |
| `exp u = F(−q)/F(−p)` (2 queries, global) | **totalised only** |
| `exp x = 1/F(−x)` (1 query, `x > 0`) | **totalised only** |
| `log₀ u = F(u) − exp u` (unconditional) | **totalised only** |
| `Δₙ F(x) = exp(nx) − exp x` → `unary_decoder` on `(0,∞)` | **convention-free** |

The dilation decoder never evaluates `log` off the positives, so it is the exportable result. The
generator claim needs three qualifiers, all load-bearing: **unary, over the field operations, of the
totalised class.**

**Gate limitation, stated rather than papered over.** `log_nonpos` is a *theorem*, not an axiom, so
the totalisation convention is **invisible to axiom footprints** — "convention-free" cannot be
machine-checked the way `sorryAx`-freedom can. What is checkable is structural: the dilation decoder
carries `0 < x` as a hypothesis, and the cheap decoders' proofs invoke `Fbasis_of_nonpos`. Both are
now pinned that way, which is weaker than a footprint check and is the best available.

### Two more literatures, both live

**Pfaffian chain order** (Khovanskii): the chain length `s` is precisely "how many nested
transcendentals", and `F` is Pfaffian of order 2. Not obviously the same as `q_F` — `s` counts a
differential chain, `q_F` counts occurrences of one generator under field operations — but it must be
ruled out before `q_F` is called new.

**Hardy fields**, and this one reframes a result. Germs at `+∞` of unary definable functions form a
Hardy field iff the structure is o-minimal (van den Dries–Miller), and a Hardy field is an *ordered
field of germs* — so eventual sign-definiteness holds **by construction**. So `zero_query_evSignDef`
is "rational germs form a Hardy field" (textbook), `SignHardCase` is "EML germs form a Hardy field",
and since `EMLClass ↔ LFClass` is proved those are one statement. Rosenlicht's rank (1983) and
Marker–Miller's level (1997) are the second candidate reparametrisation of `q_F`.

### The axiom-witness question, answered

The 50-axiom footprint of `Fbasis_root` was reported without saying whether those axioms are
discharged. They are. `AxiomLedger` records **2 unwitnessed axioms out of 220** (`erf`, absent from
Mathlib; `eml_tree_analytic_on_pos`, pending a side-condition), and **neither appears** in
`Fbasis_root` (50), `FS_evSignDef` (52) or `exp_query_cost_eventual` (42) — checked, not assumed.
The count alone was the wrong thing to quote.

## [Unreleased] — 2026-08-20 (w)

### `q_F(exp) = 1` — the two-query decoder was not optimal, and a search found the one-query one

```
exp x = 1 / F(−x)        for every x > 0
```

`−x < 0` puts `F` on the branch where the totalised logarithm vanishes, so `F(−x) = exp(−x)` and one
reciprocal finishes it. `exp_query_cost_eventual` gives both bounds and they meet:
**`q_F^eventual(exp) = 1`.**

`EFneg`'s two queries bought *globality*, not tail correctness — `EFone_fails_globally` shows
`1/F(−x)` is genuinely wrong at `x = −e`, where `−x > 0` and the logarithm returns. So

```
q_F^eventual(exp) = 1        q_F^global(exp) ∈ {1, 2}
```

and the whole remaining gap is the totalisation branch.

### Searching before proving impossibility is what produced it — and the first two searches failed open

A validated numeric search flagged `S = −x`, `S = −x−1`, `S = −x/2` at out-of-sample relative error
`1e-52`, `1e-52`, `1e-47`, against `1e-3`–`1` for every other candidate.

**Two broken versions came first.** Version 1 reported all fifteen candidates as hits: monomial bases
on a short interval are so ill-conditioned that `σ_min/σ_max` is tiny regardless of the target.
Version 2 added controls, but the *negative* control was degenerate by construction — `y = x`
duplicates columns, so the matrix is exactly rank-deficient for reasons having nothing to do with
`exp`. The working version fits on one interval and **validates out of sample** on another, with a
genuine rational target as positive control (`3e-55`) and `sin` as negative control (`1.14`).

Same failure shape as the footprint checker earlier the same day, caught the same way: a test that
cannot be seen rejecting something is not evidence.

### Two corrections to earlier entries, marked in place

**`C₀ ⊊ C₁` was oversold as "the first strict separation".** Rational germs are algebraic and `F` is
not, so it is essentially free — a check that `q_F` is not vacuous. `C₁ ⊊ C₂` is the one with content.

**The `C₀`-sign-definiteness contrast was read too strongly.** `C₀` is the rational germs — the base
case, not a competing representation — and since `EMLClass ↔ LFClass` is proved, `SignHardCase` *is*
eventual sign-definiteness for all `C_k`. The right claim is that `L_F` supplies an induction handle
the EML presentation did not.

## [Unreleased] — 2026-08-20 (v)

### The base transcendence theorem, named — and it was already free

`exp_not_algebraic`: `exp` satisfies no polynomial relation with polynomial coefficients. One line
from `not_algebraic_of_dominates_exp`.

That matters for what it says about the *reduction*, not for its own sake. The bounded case runs
`F` algebraic ⟹ `F′` algebraic ⟹ `exp = F′ − 1/u` algebraic — and its base case turns out to be a
theorem already. **The missing step is differentiation-preserves-algebraicity, and nothing about
`exp` or about `exp + log`.**

### `BoundedGermTranscendence`, typed

The ledger row now points at a Lean `def`, not prose. Boundedness stands in for "has a finite limit"
— this corpus has no limits, and for a rational germ the two coincide. Nonconstancy is "not
eventually equal to any constant", which `constant_germ_is_algebraic` shows cannot be dropped.

### Specification instead of a sketch

`monogate-research/exploration/bounded_germ_transcendence_2026_08_20/SPEC.md` costs the build:
bivariate polynomial derivatives, the chain rule against `HasDerivAt`, **algebraic-over-a-field as a
predicate with closure under the field operations**, and transitivity across `ℝ(S(x)) ⊆ ℝ(x)`. The
third is the real cost and is reusable for every future transcendence question here.

It also records why this residue is unlike the previous four. Each of those evaporated within an hour
once the right invariant was chosen. This one cannot: every argument in the arc is an envelope
argument, and **a bounded `F ∘ S` is indistinguishable from an algebraic function by any envelope** —
the engine is absent, not weak. The note says so explicitly, so the next session does not spend its
first hour hunting a fifth trick.

## [Unreleased] — 2026-08-20 (u)

### ⚠ Correction: `x ≤ S x` is a sufficient condition, not "the unbounded regime"

Entry (t) said "both unbounded regimes of a substituted germ, closed". **That was an overclaim.**
`S(x) = x/2` tends to `+∞` and satisfies neither `x ≤ S x` nor `S x ≤ −x`. What a rational germ
tending to `±∞` actually satisfies is `c·x ≤ S x` for some `c > 0` — strictly weaker whenever
`c < 1`.

Closed at any positive rate: `not_polyEnvelope_of_ge_exp_scaled` shows `exp(r·x)` outgrows every
polynomial for **any** `r > 0`, by substituting `x = t/r` to turn a polynomial envelope for it into
one for `exp` itself (`powNat_mul` supplies `(t/r)ᴺ = tᴺ·(1/r)ᴺ`). `FS_not_algebraic_of_ge_linear`
and `FS_not_algebraic_of_le_linear` are the widened statements; the `x ≤ S x` versions survive as
the `c = 1` instances, so the registered claims on them are untouched.

Both engines were generalised in place — `not_algebraic_of_dominates_exp` and
`not_algebraic_of_dominated_by_exp` now carry a rate `r > 0` — rather than duplicated. A first
attempt did duplicate the proof body inline and left a `sorry` in the working tree; reverted before
building. **Widen the engine, never copy it.**

### The constant exception is real, not defensive

`constant_germ_is_algebraic`: for constant `S` the transcendence statement is **false**, and one line
exhibits it — `F(0) = 1`, so `Y − 1` vanishes on it with leading coefficient `1`. A constant germ
collapses the one-query expression back into `C₀`, where a polynomial relation is exactly what one
should expect. The nonconstancy hypothesis is load-bearing.

### `BoundedGermTranscendence`, ledgered open

Ledger 14 rows → **15**. Nonconstant rational germ with a finite limit ⟹ `F ∘ S` not algebraic.
Everything else is now a theorem: constant `S` is a counterexample, and both unbounded rates are
closed at 39 axioms with nothing analytic. The residue is a single sharply-typed case, and it is the
one where growth arguments have no purchase at all — `F(S)` bounded is indistinguishable from
algebraic by any envelope.

## [Unreleased] — 2026-08-20 (t)

### Both unbounded regimes of a substituted germ, closed — same instrument, two orientations

| regime | mechanism | theorem |
| --- | --- | --- |
| `S(x) ≥ x` | `F(S) ≥ exp S ≥ exp x` — split off the **leading** coefficient | `FS_not_algebraic_of_ge_id` |
| `S(x) ≤ −x` | `F(S) = exp S`, super-polynomially small — split off the **constant** coefficient | `FS_not_algebraic_of_le_negId` |

The second is not a separate idea. It is the first argument read from the other end of the
polynomial: where a large generator forces the leading coefficient to dominate, a tiny one forces the
constant coefficient to vanish. `bipev_bounded_envelope` (degree stops mattering once `|y| ≤ 1`) is
the dual of `bipev_degree_drop`.

Both cost **39 axioms and nothing analytic**, same as the `S = x` case.

### The generalisation was a removal, not an addition

`Fbasis_not_algebraic` is now a corollary of `not_algebraic_of_dominates_exp`, which asks only that
`g` eventually dominate `exp`. The original proof never used anything else about `F` — dropping the
hypothesis to what the argument actually consumes is what made both substitution regimes fall out
without new machinery.

### What is left is exactly the bounded case

If `S` converges to a finite limit then `F(S)` is bounded, and **growth cannot distinguish a bounded
function from an algebraic one** — the engine driving both theorems above is gone, not merely weaker.
That is the first place in this arc where function-field or differential-algebra infrastructure is
the honest reading rather than an over-answer.

One reduction recorded before anyone builds it. On the positive branch `F(u) = exp u + log u`, so
`F′(u) = exp u + 1/u`. Algebraic functions stay algebraic under differentiation in characteristic
zero, so `F` algebraic would give `F′` algebraic, hence `exp u = F′(u) − 1/u` algebraic. The whole
route therefore needs **one** base transcendence theorem — `exp` transcendental over `ℝ(u)` — and no
special theory for `exp + log`. Recorded as a reduction, **not proved**: it needs the
differentiation-preserves-algebraicity step, which this corpus does not have.

## [Unreleased] — 2026-08-20 (s)

### `F` is not algebraic over the polynomial coefficients — and it costs **no new axioms**

`Fbasis_not_algebraic`: no nonzero polynomial in `F(x)` with polynomial coefficients vanishes on a
tail. If `aₘ(x)·F(x)ᵐ = −Σ_{i<m} aᵢ(x)·F(x)ⁱ`, the right side has degree `< m` in `F`, so dividing
bounds `F(x)` by a ratio of polynomials — hence by a polynomial. But `F(x) ≥ exp x` for `x ≥ 1`, and
`not_polyEnvelope_Fbasis` forbids that.

**The `C₀` lower-bound instrument pays for `C₁` directly.** Footprint: 39 axioms, and *no analytic
ones* — no `HasDerivAt`, no `hasDerivAt_continuousAt`. Contrast `FS_evSignDef` at 52 with the whole
derivative layer. A functional-transcendence statement turned out cheaper than the sign theorem that
preceded it.

`bipev_degree_drop` carries the degree drop as `y·|P(x,y)| ≤ B(x)·y^(deg+1)`, multiplied through by
`y` so no `Nat` subtraction appears and the induction is one line per constructor.

### A specimen that is not a linear relation

`Fbasis_nasty_relation_impossible`: `(x² + 1)·F³ + (7 − x⁵)·F² + x·F − 3 ≠ 0` on any tail. Degree 3
in `F`, coefficients of degree 0, 1 and 5 in `x`, one with a negative leading term.

Its coefficients are spelled `1 + 1 + 1` rather than `3` because `MachLib.Real` carries `OfNat`
instances for `0` and `1` only — the numeral discipline refusing a decimal literal into a statement,
which is what it is for.

### What this is, and three things it is not

It is **functional** transcendence in the elementary sense — no polynomial relation with polynomial
coefficients — not a number-theoretic statement about values.

It is the `S = x` case. Transport along a nonconstant rational substitution is **not** assumed. The
abstract reason to expect it (`ℝ(S(x)) ⊆ ℝ(x)` algebraic for nonconstant rational `S`) is a statement
about function fields, and these objects are eventual real functions, not yet elements of one. Of the
three regimes, `S → ±∞` look reachable with present machinery — one by the same envelope
contradiction, one by its lowest-power dual — while `S → c` finite makes `F(S)` **bounded**, where
growth cannot distinguish it from an algebraic function. That is the branch that would actually need
function-field or differential-algebra infrastructure.

And even the full composed statement would give the **normal form** for `C₁` — cancellation is
algebraically forced — *not* the lower bound `exp ∉ C₁`. That asks about an algebraic relation over
`ℝ(x, exp x)`, whose coefficient field already contains `exp`: a strictly stronger question. The two
are kept apart deliberately, because conflating them would turn a normal-form theorem into a
lower-bound claim it does not support.

## [Unreleased] — 2026-08-20 (r)

### The window evaporates: `F ∘ S` is eventually sign-definite for **every** rational germ

`FS_evSignDef`. No exception, no trapped case.

`F` is a sum of two strictly increasing functions on `(0, ∞)`, so it is **strictly increasing**
there (`Fbasis_strictMono`) — no derivatives, just `exp_lt` and `log_lt_log`. It is negative at
`e^(−e)`, positive at `1`, and its derivative `exp y + 1/y` is positive throughout, so it has exactly
one root `r ∈ (e^(−e), 1)` (`Fbasis_root`, via `exists_unique_root_of_deriv_pos`).

Then the whole question collapses: `S − r` is a rational germ like any other, the trichotomy decides
it, and monotonicity turns that into the sign of `F(S)`. The window's endpoints were simply the wrong
constant to compare against.

**So the generator is no longer the difficulty at level 1.** What is left of `OneQueryDichotomy` is
the *context* — whether `C(x, F(S(x)))` can cancel — between two functions whose individual behaviour
is now fully classified.

### Disclosure: this is the first result in the arc that costs analytic axioms

`Fbasis_strictMono` has a 16-axiom footprint and touches nothing analytic. `Fbasis_root` and
`FS_evSignDef` have **50 and 52**, pulling in the derivative layer and the IVT bridge —
`HasDerivAt_exp`, `HasDerivAt_log_pos`, `HasDerivAt_unique`, `HasDerivAt_add`, and
`hasDerivAt_continuousAt`.

That is the price of *existence* of the root; monotonicity alone is free. The window theorem is kept
rather than deleted precisely because it gives usable bounds at no analytic cost, and a reader who
wants the cheap version can still have it.

### Four for four

Four times in this arc a residue has evaporated once the right invariant was chosen rather than the
first one that fit: `SignHardCase` for `C₀`, the division case of `FQueryLowerBound`, the `(0,1)`
branch, and now the window. Recorded because the pattern is by now more reliable than any individual
guess about which residues are real.

## [Unreleased] — 2026-08-20 (q)

### `C₀` is eventually sign-definite — **unconditionally**

`zero_query_evSignDef`: every zero-query `L_F` term is eventually strictly positive, eventually
strictly negative, or eventually zero. No hypothesis, no ray supplied from outside.

**`SignHardCase` is this exact statement for EML, and it is open.**

> **⚠ The contrast below was read too strongly — see 2026-08-20 (w).** `C₀` is the rational germs,
> which are eventually sign-definite for elementary reasons: it is the *base case*, not a competing
> representation. And since `EMLClass ↔ LFClass` is proved, `SignHardCase` **is** eventual
> sign-definiteness for all `C_k`. The honest framing is that `L_F` supplies an *induction handle* on
> a conjecture the EML depth presentation gave none for — more accurate, and a much larger claim if
> the induction ever closes.

The contrast is the content: sign
definiteness is not hard *in general* — it is hard when the representation offers no normal form to
read it from. `C₀` has one, so the sign of a quotient comes off the signs of a numerator and a
denominator, each settled by `pev_signed_dichotomy` (the leading-term induction, refined to track
sign rather than magnitude).

`pev_dichotomy` is now derived from the signed version rather than proved separately, and the
threshold construction both share is factored out as `big_threshold`.

### What the trichotomy buys at level 1 — three of four regimes collapse

A rational germ `S` feeding the single `F` of a one-query term:

| regime | `F(S)` | status |
| --- | --- | --- |
| `S < 0` | `= exp S`, and `0 < F(S) < 1` | logarithm **gone**, generator **bounded** |
| `S = 0` | `= 1` | **constant** |
| `S ≥ 1` | `≥ exp S > 0` | exponential dominates |
| `0 < S < 1` | sign depends on scale | **the open branch** |

`Fbasis_of_neg`, `Fbasis_zero`, `Fbasis_ge_exp_of_one_le` are the first three.

### And the fourth branch is a bounded WINDOW, not an interval

> **⚠ SUPERSEDED within the same day by `FS_evSignDef` (below).** The window was the right *step* and
> the wrong *endpoint* — what decides the sign is which side of `F`'s **root** the germ lies on, not
> which side of an interval. Kept because the endpoints are still the cheapest bounds available and
> they cost no analytic axioms, where the root does.


`FS_evSignDef_or_window` — **`F ∘ S` is eventually sign-definite for every rational germ `S`, unless
`S` is eventually trapped in `(e^(−e), e⁻¹]`.**

The contest on `0 < S < 1` is between `exp S ∈ (1, e)` and `log S < 0`, and it is decided everywhere
outside that window:

* `S > e⁻¹` gives `log S > −1` while `exp S > 1`, so `F(S) > 0` — and this needs **no upper bound on
  `S` at all** (`Fbasis_pos_of_gt_expNegOne`);
* `0 < S ≤ e^(−e)` gives `log S ≤ −e` while `exp S < e`, so `F(S) < 0` (`Fbasis_neg_of_le_tiny`).

**Neither endpoint is numeric.** Both are comparisons against `exp` of something, so no decimal
enters and the numeral discipline is untouched — `sqrt` is absent from the footprints.

`ratGerm_sub_const` (germs are closed under subtracting a constant) is what lets the trichotomy be
applied to `S − e⁻¹` and `S − e^(−e)`, turning two comparisons into two sign questions already
answered.

`Fbasis_sign_changes` records the source of the difficulty explicitly rather than leaving it implied:
`F(e^(−e)) < 0` and `F(1) = exp 1 > 0`.

### What this says about the level-1 problem

The residue shrank from an interval to a bounded window, and a rational germ trapped in a bounded
window is a strong constraint — it converges, and its limit lies there. `F` has exactly one zero in
the window, so the delicate case is a germ approaching *that* zero.

More usefully, it says what the problem is **not**. On every regime outside a bounded window the sign
is settled by comparisons against `exp` of a constant. Transcendence of `F` is not what is at stake,
and a transcendence theorem would be answering a strictly harder question.

**This says something about how *not* to attack `OneQueryDichotomy`.** On three of the four regimes
the level-1 question never arises — the generator is bounded, constant, or dominated by its
exponential part. The difficulty is not that `F` is transcendental. Reaching for a transcendence
theorem would be answering a strictly harder question than the one that is open: what happens on
`0 < S < 1`, where `log S < 0` outweighs `exp S ∈ (1, e)`.

## [Unreleased] — 2026-08-20 (p)

### The one-query normal form, in two layers

**Layer 1 is exact and syntactic.** `one_query_decompose` — a term with exactly one `F` node is an
`F`-free one-hole field context applied to `F` of an `F`-free argument:

```
T(x) = C(x, F(A(x)))      at EVERY real point
```

No asymptotics, no rational normalisation, no denominator condition. `FCtx` has **no `F`
constructor**, so "the context is `F`-free" is a fact about the type rather than a predicate to carry
around, and `holes C = 1` is proved rather than assumed.

The relation is named (`CtxApplies`, `CtxAppliesEv`) rather than written inline: Lean prints
`C.eval x y` in dot notation, so an inline conclusion leaves no token a claim can bind to. The claim
auditor rejected the first attempt for exactly that — the same repair `FRepresentable` needed.

**Layer 2 is eventual.** `one_query_normal_form` feeds `ratGerm_of_zero_query` into the argument:
`T(x) = C(x, F(P(x)/Q(x)))` from some point on.

### The outer context is deliberately *not* collapsed to a quotient

At level 0 a denominator is a polynomial in `x` and `pev_dichotomy` decides it. At level 1 the
denominators look like `Q(x, F(S(x)))`, and `pev_dichotomy` says nothing about those. Writing `C` as
a single `P/Q` "eventually" would silently assume the very dichotomy that is the *next* theorem — so
the context stays a context.

`OneQueryDichotomy` is registered as **open** (ledger 13 rows → **14**): is a one-query context
eventually zero, or eventually nonzero? Expanding `Σⱼ qⱼ(x)·F(S)ʲ` asks whether the surviving
component dominates or whether exact cancellation persists — the same question `C₀` faced, one level
up. Normal forms and lower bounds at query level `k` look to be governed by one cancellation theorem
at level `k`.

### Canary 13: the footprint matcher must fail *closed*

The `sorryAx` canary has always tested **detection** — a `by sorry` theorem must be caught. It never
tested **non-detection**, which is the direction that fails silently.

Canary 13 tests both: `MachLib.Real.div_zero` must be **present** in `fQueryLowerBound_holds`'s
footprint (the totalised-division branch) and **absent** from `fDepth_toFTermFast`'s (purely
combinatorial). Both convicted, on a copy of the gate:

| perturbation | control that fired |
| --- | --- |
| needle `MachLib.RealX.div_zero` (wrong namespace — the historic bug's shape) | **positive** |
| needle `propext` (matches everything) | **negative** |

Added after a hand-rolled check reported `div_zero=False` for four theorems that all rest on it — it
compared list *elements* against a suffix. A checker that can only fail open reads clean when broken,
and the same bug in `sorryAx` detection would certify the whole corpus.

*Process note: the first convict run mutated the checked-in gate and was killed mid-run, leaving
`needle = "propext"` in the working tree. Convict on a **copy**; never on the live gate.*

## [Unreleased] — 2026-08-20 (o)

### `FQueryLowerBound` — **discharged**. No division-free hypothesis, no restriction at all.

```
fOcc T = 0  ⟹  T is an eventual rational germ  ⟹  polynomially bounded  ⟹  T ≠ exp
```

`fQueryLowerBound_holds`. Ledger row **open → discharged**, and `zero_query_lt_one_query_full`
upgrades the strict separation `C₀ ⊊ C₁` to the whole language.

### `C₀` = eventual rational germs

> **⚠ Only the ⊆ direction was proved when this was written — repaired 2026-08-20 (y).**
> `zero_query_of_ratGerm` and `zero_query_iff_ratGerm` now supply the converse, so the `=` is earned.

`ratGerm_of_zero_query` — every `F`-free term, **division included**, agrees from some point on with
`P(x)/Q(x)` for coefficient lists `P`, `Q` with `Q` nonvanishing there.

The `÷` case is where `pev_dichotomy` earns its keep. Applied to the divisor's *numerator* it splits
cleanly: eventually zero makes the whole quotient eventually `0` by `div_zero`; eventually nonzero
puts ordinary fraction algebra back in force. And cancellation under `+` is no longer *predicted*
from leading-order data — it simply happens inside `padd`/`pmul`, which is the entire reason for
abandoning envelopes and passing to an exact representation.

The germ is stated **eventually** and deliberately not globally: with totalised division a global
`T = P/Q` identity is false at the denominator's zeros, and at `+∞` those are all behind us.

### The missing infrastructure, built

Named last commit as the blocker; now present. `abs_one_div`, `abs_div_eq`,
`one_div_le_one_div_of_le`, `div_one_eq`, `zero_div_eq`, `div_add_div_eq`, `div_sub_div_eq`,
`div_mul_div_eq`, `div_div_div_eq`, `div_eq_div_of_cross`, `eq_of_mul_eq_mul_right'` — all derived
from `div_def`, `mul_inv` and `div_zero`, nothing new assumed. Plus `padd`/`pscale`/`pmul`/`psub` on
coefficient lists with their `pev` homomorphisms.

### `div_zero` is load-bearing, and the footprint proves it

`MachLib.Real.div_zero` appears in the axiom footprint of `ratGerm_of_zero_query`,
`polyEnvelope_of_ratGerm`, `fQueryLowerBound_holds` and `zero_query_lt_one_query_full` — checked, not
asserted. Without it, `x ↦ a x / 0` is unconstrained, a model can set `divR y 0 = exp y`, and
`div var (sub var var)` becomes a **zero-query term computing `exp`**: the statement would be
*independent*, not merely unproved.

*(A first pass at that check reported `div_zero=False` — the test used list membership against
`'Real.div_zero'` where the entries read `MachLib.Real.div_zero`. The bug was in the check, not the
theorem. A verification that can fail closed is worth more than one that reads clean.)*

### Discrimination

`divTower = (x / (x − x)) / (x·x + 1)` — nested division, and the inner denominator vanishes
*identically*, so the totalised branch is genuinely exercised. Still a rational germ
(`divTower_ratGerm`), still not `exp` (`divTower_ne_exp`). The previous commit's theorem could not
state this term, let alone decide it.

## [Unreleased] — 2026-08-20 (n)

### The keystone: a polynomial is eventually zero, or eventually dominates `c·xᵏ`

`pev_dichotomy`. Not a root-counting theorem — leading-term domination, by induction on the
coefficient list: a nonzero constant term dominates when the tail dies, and otherwise
`|c + x·P(x)| ≥ c₀xᵏ⁺¹ − |c| ≥ (c₀/2)xᵏ⁺¹` once `x ≥ 2|c|/c₀`.

This is the one genuinely new supporting result the rational-germ programme needs. Envelopes break on
cancellation; the escape is an **exact** representation `P/Q` where cancellation happens in the
polynomial arithmetic and needs no asymptotic prediction. `pev_envelope` is the easy other half.

### The first strict query separation: `C₀ ⊊ C₁`

> **⚠ OVERSTATED as "the first strict separation" — see 2026-08-20 (w).** Rational germs are
> algebraic and `F` is not, so this separation is essentially free. It shows `q_F` is not vacuous; it
> is not a result. The separation that would carry content is `C₁ ⊊ C₂`.

`zero_query_lt_one_query`, on the division-free fragment. The witness is **`F` itself**, not `exp`:
`F` costs exactly one query *by definition*, whereas `exp` currently costs two, so the upper bound is
free. And since `log x ≥ 0` for `x ≥ 1`,

```
F(x) = exp x + log x ≥ exp x        (x ≥ 1)
```

so `not_polyEnvelope_Fbasis` — `F` outgrows every polynomial envelope and cannot be zero-query.

`not_polyEnvelope_of_ge_exp` generalises `polyEnvelope_ne_exp`: *anything* eventually dominating
`exp` is excluded, not just `exp` itself. The instrument now has two customers.

### Division is totalised, and `FQueryLowerBound` depends on that

Checked before building on it: `div_zero : a / 0 = 0` is an **axiom** of `MachLib.Real`
(`Basic.lean:149`, matching the Lean/Mathlib convention). This matters more than a convenience.

Without it, `x ↦ a x / 0` would be an unconstrained function, and a model could set
`divR y 0 = exp y` — making `div var (sub var var)` a **zero-query term computing `exp`**.
`FQueryLowerBound` would then not merely be unproved, it would be *independent*. The axiom is what
makes the statement true, and the `÷` case of the germ compilation is exactly where it gets used.

### What remains, precisely

`pev_dichotomy` is banked; the germ compilation is not built. The concrete inventory:

* coefficient-list `padd`/`pmul` with `pev` homomorphism lemmas — the corpus has `listAddR` /
  `listMulR` and `polyCoeffs_eval`, in another namespace and phrased for the `Poly` expression tree;
* the fraction identities, valid where denominators are nonzero — which `pev_dichotomy` now supplies
  eventually;
* the division envelope `|P/Q| ≤ (C/c)·x^N`, needing `abs_div` and a reciprocal monotonicity lemma.
  **Neither exists in the corpus.** That is the missing infrastructure, named rather than assumed.

## [Unreleased] — 2026-08-20 (m)

### The Apollonius degree-drop locus is where a circle becomes a **line**

`oii_lead_zero_iff_tangent_line` — for the `(o,i,i)` class,

```
QMlead d ρ classOII = 0   ↔   the class admits a common tangent LINE
```

The `8 → 7 → 8` anomaly across `d² = 8ρ²` was never a collision of two finite circles. Homogenising
the radius as `r = R/S`, the class quadratic `A R² + B R S + C S² = 0` at `A = 0` becomes
`S·(B R + C S) = 0`: two projective roots still, the finite one and `S = 0`, a solution of infinite
radius. **A circle of infinite radius is a line**, and here it is a concrete one — for `ρ = 1` and
`d² = 8`, the line `x + y = √2`, at distance exactly `1` from all three centres.

In the compactified count the anomaly is `8 → 8 → 8` throughout.

### Why the proof needs no division in the direction that matters

An oriented line `{p : n·p = c}` with `|n| = 1` is tangent with signs `sᵢ` iff `n·cᵢ − c = sᵢρ`. The
`(o,i,i)` signs and centres `(0,0)`, `(d,0)`, `(0,d)` give `c = −ρ` and `n_x d = n_y d = −2ρ`.
Multiplying `|n|² = 1` through by `d²` turns the unit condition into

```
(n_x d)² + (n_y d)² = d²    ⟹    4ρ² + 4ρ² = d²
```

so the forward direction is division-free; only the *construction* of the line needs `d ≠ 0`.
`sqrt` is absent from both footprints — the sqrt firewall holds.

### Discrimination: the locus is class-specific, and the arithmetic says why

`oio_tangent_line_iff` — flip one companion sign and the tangent line exists at `d² = **4**ρ²`
instead. That is exactly what `[(s₁−s₀)² + (s₂−s₀)²] ρ² = d²` predicts: the bracket is `0`, `4` or
`8`, and only `(o,i,i)` — *both* companions opposite to the first — gives `8`.

Without that specimen the theorem could have been about lines in general rather than about this
class, and a reader would have no way to tell.

### Method note

This is the first result in the corpus that argues *projectively*, and it arrived by asking where a
vanishing quantity **went** rather than treating it as a degeneracy to be assumed away. The leading
coefficient vanishing is not the phenomenon; it is the shadow of one.

## [Unreleased] — 2026-08-20 (l)

### The zero-query barrier: the first lower-bound instrument on the `L_F` side

```
fOcc T = 0  ⟹  T is eventually polynomially bounded  ⟹  T ≠ exp
```

`polyEnvelope_of_zero_query` is the reusable half, and it is deliberately *not* called
`exp_not_rational`: any target with proved super-polynomial growth now costs at least one `F`-query,
and `exp` is only the first customer.

`exp_beats_powNat` — the one analytic input — was already in the corpus. Nothing new was needed
there.

### Scope: this closes the division-free case, and the reason is precise

`divFree T` is a hypothesis and it is load-bearing. The envelope induction closes for constants, the
variable, `+`, `−` and `×`. It does **not** close for `÷`, because bounding `a / b` needs `|b|`
bounded *below*, so the invariant must be two-sided — upper envelope plus "eventually zero, or
eventually `≥ c/xᴹ`".

That strengthened invariant is closed under `×` and `÷` and **not under `+`**: two terms can cancel
to strictly smaller order (`x` and `−x + 1/x` sum to `1/x`), and the leading-order data of the
summands does not determine the order of the sum. Recovering it needs the full rational germ at
`+∞` — a Laurent normal form with descent through cancelling leading terms.

**So the obstruction is cancellation under addition** — the same shape that gates `SignHardCase` and
the EML depth program. That is worth more than the theorem: it says the `L_F` lower-bound problem is
not a new kind of difficulty, it is the corpus's existing one wearing different clothes.

I did *not* attempt a global fraction normal form. With totalised division, combining fractions by
multiplying denominators can disagree with the original function exactly at the denominators' zeros,
so `T = P/Q` everywhere is not a safe promise. The eventual germ is the right object and it is not
built here.

### The obligation gate caught a real overclaim

I first marked `FQueryLowerBound` as **reduced**, citing `fOcc_pos_of_eq_exp` as the discharger. The
gate refused: *"marked reduced; cited [`fOcc_pos_of_eq_exp`], actual dischargers (none)"* — because
that theorem carries an extra hypothesis and does not conclude the unrestricted statement.

Correct fix: **split the obligation.** `FQueryLowerBoundDivFree` is a separate row, **discharged** by
`fQueryLowerBoundDivFree_holds`; `FQueryLowerBound` stays **open**. Ledger 12 rows → **13**.

A weaker theorem cited against a stronger row is exactly the drift the ledger exists to catch, and it
caught it on the first attempt.

### Specimen

`nastyTerm = ((x·x − x)·(x·x) + x) − 7` — nested products and differences, nothing polynomial-looking
about the *syntax* — falls under the envelope with no case analysis, hence `nastyTerm_ne_exp`. The
theorem is about the language, not about terms that happen to look like polynomials.

## [Unreleased] — 2026-08-20 (k)

### Simulation overhead, the other direction — and it is not symmetric

`toEML_depth_le` — **`EMLTree.depth (toEML T) ≤ 400 · fHeight T`.** A constant times the `L_F` term's
*syntactic height*, and it cannot be improved to a function of `fDepth` alone, because EML has no
primitive `+`, `−`, `×` or `÷`: every field operation is a gadget costing a fixed number of levels
(`EMLDepthCost.lean` already recorded the numbers at `var` — `subGen` 15, `addGen` 34, `mulGen` 54).

Side by side:

```
fDepth (toFTermFast t)   =  t.depth                 exact, no overhead, no constant
EMLTree.depth (toEML T)  ≤  400 · fHeight T         constant × HEIGHT, not × fDepth
```

The general per-gadget bounds (`subTree` 12, `addTree` 12, `mulPos` 40, `subGen` 24, `addGen` 56,
`mulL` 64, `mulGen` 112, `invPos` 28, `divGen` 384, `FTree` 64, each `+ max` of the children) are new;
the corpus had only the exact depths at `var`. **The constants are envelopes, not optima** — the first
attempt used `8` for `addTree` and `omega` rejected it, because `addTree` routes its right argument
through `negOffset`, which costs 2 that `max a b` does not see.

### The asymmetry is real, not an artefact of loose constants

`inv_x_basis_gap` — `1/x` has minimum EML depth **exactly 4** (`inv_x_min_depth`, certified via
`invX4_depth_optimal`) and in `L_F` is the term `1/x`: `F`-depth `0`, **zero** distinct `F`-queries.

`additive_slack_at_least_four` — therefore any inequality `d_EML(f) ≤ C·d_F(f) + D`, valid for all
`f` with `d_EML` the *minimum* over EML trees, forces **`4 ≤ D`**, whatever `C` is. Two specimens now
show the gap (`x + 1` and `1/x`); the second is the better one, because its EML minimality is
certified rather than assembled from an exclusion plus a witness.

### `FQueryLowerBound`: the obligation this arc did not discharge

Registered in the obligations ledger (11 rows → **12**), marked **open**:

```
FQueryLowerBound : ∀ T : FTerm, (∀ x, FTerm.eval T x = exp x) → 1 ≤ fOcc T
```

Computing `exp` requires at least one `F`. Equivalently — an `F`-free `L_F` term being a rational
function of `x` — **`exp` is not a rational function**. Certainly true; **this development does not
prove it**, which is the point of the row.

That matters more than one missing lemma, because it is the shape of the whole arc: every complexity
statement here is an upper bound or an exact count of a construction I wrote. `additive_slack_at_least_four`
is the single lower bound, and it is *imported from the EML side*, where the corpus's exclusion
machinery reaches. On the `L_F` side there is no lower-bound machinery at all — discharging
`FQueryLowerBound` would need either a growth comparison (`exp` outgrows every rational function) or a
rational normal form for `F`-free terms, and the corpus has neither.

So: "is `F` a minimal basis" cannot be attacked yet. Not because the question is hard, but because
there is no instrument that can answer *any* question of that shape here. That is the honest state.

## [Unreleased] — 2026-08-20 (j)

### `F` is not isolated: a two-parameter family of unary generators

`Fmix_unary_basis` — for **every** `a ≠ 0` and **every** `b ≠ 0`, the affine mixture

```
F_{a,b,c}(x) = a·exp x + b·log₀ x + c
```

is a unary generator for the whole EML class, with the same query counts: two per exponential, three
per logarithm, and `F`-depth equal to EML depth (`fDepth_toFTermMix`). `F = F_{1,1,0}`.

**The generalisation is free, and the reason is instructive.** A *dilation*-based decoder would have
needed three separate repairs — `c` removed by a difference, `b·log n` subtracted off, `a` cancelled
in a ratio, one per parameter. The **negative-argument** decoder needs none: where `y ≤ 0` the
totalised logarithm vanishes, so `F_{a,b,c}(y) = a·exp y + c`, and

```
exp u = (F_{a,b,c}(−q(u)) − c) / (F_{a,b,c}(−p(u)) − c)
```

cancels `a` and `c` *simultaneously*. `b` never appears — the exponential half of the basis does not
see the logarithmic coefficient at all. It enters only in `log₀ u = (F(u) − a·exp u − c)/b`.

The parameters were never obstacles to defeat one at a time. Which parameters a decoder must fight
is a property of **where it evaluates the generator**, not of the generator.

`Fmix_b_zero_is_affine_exp` records why `b ≠ 0` is asymmetric: at `b = 0` the generator is `exp` up
to an affine change and carries no information about `log₀` at all, while the exponential decoder
above still works verbatim.

### The family is uniform mathematically and *not* numerically

Measured, not asserted. With `c ≠ 0` the decoder recovers `a·exp(−q(u))` — of size `e^{−(u²+1)}` — by
subtracting `c` from `a·exp(−q) + c`. Catastrophic cancellation, losing about `0.434·(u² + 1)`
decimal digits, **quadratic in `u`**:

| precision | range | worst rel err (exp) |
| --- | --- | --- |
| 50 dps | `u ∈ [−8, 8]` | 2.9e-16 — about 34 digits lost |
| 200 dps | `u ∈ [−8, 8]` | 6.1e-166 |
| 600 dps | `u ∈ [−30, 30]` | 7.4e-194 |
| 50 dps, **`c = 0`** | `u ∈ [−30, 30]` | **3.3e-51** — nothing to cancel against |

So the parameter the *algebra* cancels for free is exactly the one that costs precision, and the
original `F` (`c = 0`) is distinguished after all — numerically, not algebraically. An earlier run at
50 dps raised `ZeroDivisionError`: the denominator underflowed to exactly `0`. That is the failure
mode, caught rather than reasoned about.

### `x + 1`: what a change of basis does to one function

`x_plus_one_basis_gap`, three facts in one statement:

* the EML witness has depth `4`, and its compiled image has `F`-depth `4` — the translation adds
  nothing;
* **no** EML tree of depth `≤ 3` computes `x + 1` on `(0, ∞)`;
* in `L_F` the function is the term `x + 1`: `F`-depth `0`, **zero** distinct `F`-queries, and on
  *all* of `Real` rather than merely `(0, ∞)`.

Basis change preserves *compiled* depth **exactly** and collapses *minimal* depth from 4 to 0. The
finite-depth paper's "exact depth is a property of the presentation" now has both presentations of
one function written side by side, with the minimum in each proved rather than estimated.

## [Unreleased] — 2026-08-20 (i)

### The measures, fixed first — and they diverge exponentially

"Three `F` evaluations" was never well defined. A syntax tree counts `F(u)` twice inside `EF u`; an
evaluator with common-subexpression sharing queries it once. Three measures are now defined:

* `fOcc T` — occurrences of `F` in the **syntax tree**;
* `fDepth T` — maximum **nesting** depth of `F`;
* `FQueriesLe T n` — the arguments at which `T` applies `F` are covered by a list of length `≤ n`,
  an upper bound on the **distinct** (evaluation-DAG) query count. Stated as a cover rather than
  `dedup.length` so that no decidable equality on `Real` is needed.

They are not interchangeable: `fOcc_EFall` gives `fOcc(EFall u) = 8 + 20·fOcc u`, so the tree count
**multiplies by 20 at every EML level** — exponential in depth — while `FQueriesLe_toFTermFast`
bounds the distinct count by `5` per `eml` node, linear in size.

### A two-query global exponential decoder

`EFall` needed six distinct queries because it routes through `EF`, which needs its argument
**positive** and spends three queries on the dilation identity. Wrong instrument again.

Query `F` at a **negative** argument and the totalised logarithm is `0`, so `F` reports the
exponential alone: `F(y) = exp y` for every `y ≤ 0`. Both `p(u) = u + u² + 1` and `q(u) = u² + 1` are
positive for every real `u`, so `−p` and `−q` are negative for every real `u`, and `p − q = u`:

```
exp u = F(−q(u)) / F(−p(u))
```

**Two queries. No dilation identity, no positivity hypothesis, no case split, and no scales at all.**
`log₀ u = F(u) − exp u` costs one more, so three for the logarithm.

The totalisation is not being worked around here — it is being *used*. `F` is a mixed signal, and
evaluating it where one component vanishes is a cheaper demixing than the dilation calculus, which
demixes by *transformation law* and needs two scales to do it.

### Simulation overhead: zero in depth, linear in count

`fDepth_toFTermFast` — **`fDepth (toFTermFast t) = t.depth`, exactly.** The decoders never nest `F`
inside `F`, so the change of basis is depth-preserving with no constant factor and no additive
slack. The entire cost of the translation lives in query *count*:

```
fDepth (compiled)      =  depth (source)          exactly, no overhead
FQueriesLe (compiled)  ≤  5 · (eml nodes)         linear
fOcc (compiled)           ×20 per level           exponential
```

Two presentations of one class, coarse complexity preserved in the two measures that respect
sharing, and destroyed in the one that does not.

### One query: open, and left open

The reason to look: the argument of `F` is free, any rational function of `u` may be used. The
reason to expect none: for `exp u` to be rational in `F(w)` and `u` the exponential parts must be
rationally related, which pushes `w` toward affine `a·u + b` — and no affine `w` is non-positive for
*every* `u`, so `F(w)` cannot report the exponential alone; where `w` is positive, `F(w)` carries
both components and separating them is what needed three queries.

**That is a reason to look, not a proof.** It assumes the decoder is rational in `F(w)` and `u`, and
assumes rational relatedness forces affinity. Neither is established. This arc produced three
impossibility guesses in one day and refuted all three, so "one query does not suffice" is recorded
as a conjecture with no supporting theorem.

### Verification

Independent Python at 60 dps: `EFneg` matches `exp` to 2.1e-61 worst relative error over
`u ∈ [−40, 40]` — a range four times wider than `EFall` could be tested on, because `EFall` overflows
double range at `|u| > 12` (it evaluates `exp(3(u²+1))`). The cheap decoder is not only shorter, it
is numerically far better conditioned; `EFneg` evaluates `F` only at *negative* arguments, where
`exp` is bounded by `1`.

## [Unreleased] — 2026-08-20 (h)

### Change of basis: `EML` and `L_F` generate the *same* function class

`eml_class_eq_lf_class` — **`EMLClass f ↔ LFClass f`.** The totalised exponential–logarithmic
function class admits a single unary transcendental generator over the field operations. Neither
direction assumes anything about signs, domains or rays.

`toEML_eval` is the reverse direction: every `L_F` term is computed by an EML tree at every point
where its divisions are defined, and the tree does not depend on the point.

`F_mem_EMLClass` keeps this internal: `F` is itself an EML function (`FTree`), so this is a second
presentation of one semantic class, not an extension of it by an outside oracle.

### Most of the reverse direction already existed, and I nearly rebuilt it

I started writing unconditional `+`, `−`, `×` for EML and hit *eleven* "already declared" errors.
`EMLRingClosure.lean` has had all of it since an earlier arc, via a **better** shift than the one I
was constructing: `domTree t = exp (1 − t)` is positive *and* dominates `−t`, so
`domTree t + t > 1 > 0` — one gadget, where I was using two (`exp t` and `exp t − t`).
`EMLDerivClosure.lean` adds `invPos`, the reciprocal of a positive tree.

Exactly **one** operation was missing: division by a tree of unknown sign. One identity closes it —

```
a / b = a · b · (1 / b²),     b² > 0 wherever b ≠ 0
```

— the same move as everywhere else in this arc: route a sign-indefinite quantity through one that is
positive for a *structural* reason. `divGen_eval` is the whole of the new mathematics in this
commit; `toEML` and `toEML_eval` are then one clause per constructor.

**Lesson, third time today:** before building, grep the corpus for the thing you are about to build.
The first two instances were about concluding impossibility from a missing construction; this one is
about not noticing the construction already exists. Same root — reasoning from what is in front of me
rather than from what is in the repository.

### The one side condition that does not lift

`DivSafe T x` — no division in `T` divides by zero at `x`. It is a property of the `L_F` term, not of
the encoding, and `divGen_at_zero` shows it is load-bearing: where the denominator vanishes the
translated tree evaluates to `0` **for every numerator**, so matching `a / b` there would require
`a / 0 = 0` for all `a`, which MachLib's field axioms do not provide (`mul_inv` is stated only for
nonzero arguments).

The forward direction has to *discharge* `DivSafe`, so `toFTerm_divSafe` proves the emitted terms are
safe: `EFall` divides only by `EF(u² + 1)` whose value is `exp(u² + 1) > 0`, and `EF`'s own
denominator is `exp(2w) − exp(w)` with `w > 0` (`EF_denom_ne_zero`).

`F_unary_basis` is now `⟨toFTerm t, toFTerm_eval t⟩` — the compiler is an explicit function rather
than an existence proof, because the equivalence theorem needs to state things *about* the emitted
term. The claim registry caught the change: `proof_uses` still named `EFall_eval`, which the new
proof term does not mention.

### Why this matters beyond bookkeeping

`x + 1` costs depth exactly 4 in the EML primitive basis. In `L_F` addition is primitive and `x + 1`
needs no transcendental call at all. The class is identical; the syntactic complexity is not. That
is the finite-depth paper's "exact depth is a property of the presentation" with a specimen sharp
enough to be uncomfortable — and it makes the *simulation overhead* between the two presentations
the next question worth measuring.

## [Unreleased] — 2026-08-20 (g)

### `F` is a unary basis for EML — globally, unconditionally, and obstruction (B) is refuted

`F_unary_basis` — **every EML tree is computed at every real point by a term of `L_F`.** Constants,
the variable, four field operations, one unary symbol `F(x) = exp x + log x`. No domain, no ray, no
sign hypothesis, no positivity, no runtime selector; `L_F` still has no conditional.

Two facts, both sitting in the file already, do all the work.

**`decoder_log` has no hypothesis.** `F u − exp u = log₀ u` for every real `u`, *totalised branch
included* — because `F` is itself built from the totalised `log`, so the branch information is
latent in the primitive rather than lost. This is exactly the escape route flagged when obstruction
(B) was raised ("`F` descends from a totalised construction, so some branch information may already
be latent"). It was the one that works.

**`EF` needs its argument positive — and the argument is ours to choose.** `u + u² + 1` and `u² + 1`
are positive for *every* real `u`, so

```
exp u = EF(u + u² + 1) / EF(u² + 1)
```

decodes `exp` everywhere with no case split (`FTerm.EFall_eval`). `log₀` follows.

So `log_totalised_F_representable`: **`log₀` — the piecewise, discontinuous, totalised primitive —
is a single branch-free `L_F` term across its own sign change.** That is precisely what obstruction
(B) said could not be done, and (A) and (C) fall to the same construction.

### Every sign hypothesis in the file was unnecessary

The positive fragment, `EvStable`, the eventual theorems, the depth-≤3 bound: all are
`F_representable_everywhere` with an unused hypothesis. They are kept as the record of the search —
and because `EFshift` and `EFupper`, the two one-sided repairs, are what suggested the two-sided
one. The affected prose carries in-place ⚠ markers rather than being edited away.

**This is the same error as (f), one level up.** There I concluded a *hypothesis* was too weak from
three failed *constructions*. Here I concluded a *language* lacked the power to express `log₀` from
the absence of one *feature* (a conditional). Both times the missing thing was a construction, and
both times the failure had a visible shape I did not interrogate — the three routes all wanted the
argument on one side of a threshold; the obstruction argument all rested on `L_F` having no
selector, while the primitive it is built from is itself a selector.

### Verification

Independent re-implementation in Python at 60 decimal digits: `EFall` matches `exp` to 7.9e-61 worst
relative error over `u ∈ [−12, 3]`; `LFall` matches the **totalised** `log₀` to 1.0e-59, returning
exactly `0` at `u = −3, −1, −0.5, 0` and the true `log` above. Convict specimen in the same run:
bare `EF` is *wrong* at those points (`EF(−1) = 0.5304` vs `exp(−1) = 0.3679`; `EF(0) = 0.5850` vs
`1`), so the shift does real work and the theorem is not a restatement of what was already
available. `sorryAx` absent from all three new footprints.

### What is now open

`F` is a basis. **Is it a minimal one?** `EFall` spends three `F` evaluations per `exp` and four per
`log₀`, and the dilation identity needs at least two scales — one is not rationally sufficient.

> **⚠ Both numbers are wrong, and were wrong in a specific way — see 2026-08-20 (i).** They float
> between syntax-tree occurrences and distinct evaluation-DAG queries, which is exactly the
> ambiguity that had to be removed before "minimal" could mean anything. In the DAG measure `EF`
> costs 3 and `LF` costs 3 as well (they *share* `F(u)`), and the global `EFall` costs 6, not 3.
> And the whole count is superseded: two queries suffice globally.
Whether three is necessary, and whether some other single function does better, is untouched.
Nothing here says `L_F` is a *small* language, only that it is a complete one.

## [Unreleased] — 2026-08-20 (f)

### ⚠ CORRECTION — `EvSign` was enough all along; the gap was in the instrument

Yesterday's entry located a gap in the left child and called it a missing stabilization statement.
**It was a missing construction.** The three decoder routes available then — `EF` (needs `a > 0`),
`1/EF(−a)` (needs `a < 0` strictly), `EFshift` (needs a *lower* bound) — all fail at `a x ≤ 0`, and
I read that as the hypothesis being too weak. There is a fourth route:

```
exp a = exp C / exp (C − a),   available whenever a < C
```

An **upper** bound decodes exactly as well as a lower one (`FTerm.EFupper_eval`). So the left child
needs only that `a` be bounded on *one* side, and `EvSign`'s two branches supply precisely that:
`0 < a` bounds it below by `0`; `a ≤ 0` bounds it above by `1`. Both children need the same
hypothesis, and it is `EvSign`'s own shape.

The strict trichotomy asked for yesterday is not needed, and the claim that
`SignHardCase ⟹ eventually F-representable` is false as stated was itself wrong.

### The eventual unary basis theorem, both halves

- `evStable_F_representable` — every EML tree whose internal arguments are **eventually
  sign-definite** on `D` (positive throughout, or non-positive throughout — nothing finer) is
  computed on `D` by a **branch-free** `L_F` term. The translator picks each branch once; `L_F`
  still has no conditional.
- `eventual_F_representable_of_hard` — **`SignHardCase` ⟹ every EML tree is eventually an `L_F`
  term.** At every depth.
- `eventual_F_representable_depth_le_three` — **unconditional at depth ≤ 3.** *(Superseded by
  2026-08-20 (g): unconditional at* **every** *depth, and globally rather than eventually. The depth
  bound was an artefact of assuming a sign hypothesis was needed at all.)* The node itself never
  needs a sign; only its two children do. So `evSign_depth_le_two`, which is unconditional, covers
  the children of every node in a depth-≤3 tree — the representability theorem reaches exactly one
  level deeper than the sign theorem it consumes.
- `log_eventually_F_representable` — `log` itself, no hypothesis. `logTree var` has depth 3.

`stable_signs_F_representable` and `stable_signs_refined_F_representable` are now corollaries rather
than separate inductions; `node_step` is the single node argument both the global and the eventual
theorems consume.

**`FRepresentable D f` is now a named predicate**, and the theorems conclude it rather than an
inline existential. Not cosmetic: the claim auditor demanded it. With the existential written out,
Lean prints the conclusion as `T.eval x = t.eval x` with `T`'s type elided, so no token in the
conclusion says the witness is a term of `L_F` — the gate could not tell this theorem from one that
merely exhibits *some* agreeing function. Naming the predicate puts the language back in the
conclusion where the claim can bind to it.

Four claims registered (198 → 202). The gate fired on all three of the non-trivial ones before it
passed: `FTerm.eval` absent from the conclusion, and a hypothesis count of 1 where the record said
0.

**Discrimination.** The identical script at depth ≤ 4 is *rejected*, and it fails at exactly one
line — the `evSign_depth_le_two` supply, not the subtree closure — so the specimen names the reason
the bound is 3. `xPlusOneTree.depth = 4` compiles, so depth 3 is a real frontier and not a bound
that happens to cover everything interesting. `sorryAx` absent from all five footprints.

## [Unreleased] — 2026-08-20 (e)

### Eventual representation closes; the gap to `SignHardCase` is located exactly

`stable_signs_F_representable` — **every EML tree whose internal arguments keep one sign on `D` is
computed there by a branch-free `L_F` term.** No runtime selector is needed: the *translator* picks
the branch once. Six cases per node, and the totalisation collapses two of them, because `log₀` is
`0` on both non-positive branches.

The trichotomy is kept **strict** deliberately. "Eventually non-negative" is not "eventually
positive or identically zero", and `EF`/`LF` consume strict positivity.

### Comparing to `EvSign` child by child — and the two children differ

`EvSign f = (eventually 0 < f) ∨ (eventually f ≤ 0)`.

- **Right child: `EvSign` is enough, on the nose.** Both non-positive cases give `log₀ = 0`, so they
  collapse and `f x ≤ 0` suffices. `stable_signs_refined_F_representable` weakens the hypothesis to
  exactly this shape.
- **Left child: `EvSign` is not enough.** `exp` needs `a > 0`, or `a < 0` **strictly** (at `a = 0`
  the denominator `exp(2·0) − exp(0)` vanishes), or a lower bound for `EFshift`. `f x ≤ 0`
  distinguishes none of these.

**So the missing statement is precisely: a term eventually non-positive is eventually *strictly*
negative, or eventually zero.** Strictly stronger than `EvSign`, not implied by it, and a sharper
question than `SignHardCase` — it asks for a trichotomy where `SignHardCase` delivers a dichotomy.

> **⚠ SUPERSEDED by 2026-08-20 (f).** No such statement is needed. The left child was short of
> routes, not short of hypotheses: `exp a = exp C / exp (C − a)` decodes from an *upper* bound, and
> `a ≤ 0` supplies one. The paragraph below headed "still not registered" is likewise void — the
> implication is now proved.

`SignHardCase ⟹ eventually F-representable` is therefore **still not registered**, and now for a
stated reason rather than caution: it is false as it stands, because the left-child case is not
supplied.

### Obstruction (B) downgraded to a hypothesis

"`log₀` is unrepresentable in `L_F` because there is no selector" was over-claimed. Absence of an
explicit conditional does not prove a piecewise function undefinable, and `F` descends from a
totalised construction so branch information may already be latent in the primitive. Turning it into
an impossibility theorem needs an invariant every `L_F` term satisfies and `log₀` violates —
continuity across the sign change being the obvious candidate. None is offered, so it stands as
evidence.

## [Unreleased] — 2026-08-20 (d)

### `L_F` has a type, and the positive fragment has a basis theorem

"Basis" is now a claim about a defined object. `FTerm` is constants, `x`, the four field operations,
and one unary symbol `F` — **no conditional, no sign test**, which is what makes the totalised branch
a language-level obstruction rather than a bookkeeping detail.

- `FTerm.EF`, `FTerm.LF` — the decoders **as terms of the language**, with `EF_eval` / `LF_eval`
  discharging them wherever the argument is positive.
- `PositiveInternal D t` — every `eml` node in `t` has *both children* strictly positive on `D`.
  Structural, not "the function is positive", because that is what the decoder actually consumes.
- `positive_fragment_F_representable` — **every tree in that fragment is computed on `D` by a term
  of `L_F`.** One line of induction per node: `eml a b ↦ EF(â) − LF(b̂)`.

### The two children are not symmetric, and the asymmetry is the totalisation

`FTerm.EFshift_eval`: **the left child needs only a known lower bound, not positivity** —
`exp u = exp(−C)·exp(u + C)`, so a shift removes the constraint. Obstruction (A) was a limitation of
the *instrument* and is repaired.

The right child has no such repair. `log₀` is genuinely piecewise, and `L_F` has no selector, so a
single term cannot follow a value that switches definition on a sign. Obstruction (B) is a statement
about the *language*, not the decoder.

Obstruction (C) — a child that changes sign — is (B) made unavoidable unless the sign eventually
stabilises, which is what `SignHardCase` would supply. That gives it a **second potential consumer**
beyond all-depth tameness. **Deliberately not registered as an implication**: the remaining step,
translating the totalised branch once its sign is known, has not been checked, and this arc has
supplied enough warnings about obvious next compositions.

### Wording corrected before it hardened

"Two scales suffice, one never does" is replaced by: **one scale is not rationally sufficient; some
two-scale pairs are; the criterion is open.** `(2,3)` and `(2,4)` both work, by *different*
eliminations. And on `x > 0` the polynomial `Pₙ` is injective, so a single scale already *determines*
`y` — determinacy and rational recoverability are different properties and only the second was ever
at issue.

## [Unreleased] — 2026-08-20 (c)

### Dilation calculus at depth ≤ 1, and a proved blind spot

`dilation_depth_le_one`: `Δₙ f(x) = f(nx) − f(x)` on the five closed forms gives five distinct
shapes — `0`, `(n−1)x`, `−log n`, `exp(nx) − exp x`, `exp(nx) − exp x − log n`. The separation is
**exact**, not asymptotic, and `α` versus `c − log x` is already resolved by one non-trivial scale
(`0` for every `n`, versus `−log n ≠ 0`).

Every depth argument in the corpus so far has the shape *syntax ⟹ growth envelope* and concludes by
comparing magnitudes. This has the shape *syntax ⟹ exact annihilation identity* and concludes by
comparing algebraic form. Whether it yields exclusions is open; that it is a different mechanism is
not.

`dilation_blind_to_translation`: **`Δₙ(x + c) = (n−1)x`, with no dependence on `c`.** The new
instrument cannot distinguish `x + c` from `x`, so it cannot reach the negative-translation
obligation. Recorded as a theorem because a tool's blind spot should be proved rather than suspected
— it keeps two research threads from being conflated later.

### Obligation registered: `NegativeTranslationGrowingLeft`

Deliberately narrow. Not "negative translations" — one branch of one case: a depth-3 node for
`x + c`, `c < 0`, where the left exponential already dominates `exp x` and the two sides cancel. The
bounded-left branch is closed. Ledger now carries **11 rows**; the gate fired correctly on the
first attempt, when the Lean table had been updated but the CHANGELOG mirror had not.

## [Unreleased] — 2026-08-20 (b)

### A unary decoder for `exp` and `log` — `MachLib/EMLUnaryBasis.lean` (new)

`F(x) = eml(x, 1/x) = exp x + log x` on `(0, ∞)`. The **multiplicative finite difference**

```
    Δₙ F(x) = F(n·x) − F(x) − log n  =  exp(n x) − exp x
```

annihilates the logarithm **exactly** — no error term, no ray, no hypothesis beyond positivity —
because `log` turns dilation into translation and the `− log n` removes what is left.

Two scales then recover everything (`dilation_diff`, `decoder_exp`, `decoder_log`,
`unary_decoder`):

```
    Δ₃F / Δ₂F − 1 = exp x           F(x) − exp x = log x
```

**Why three scales.** With `Δ₂` alone, `y = exp x` satisfies the quadratic `y² − y = Δ₂` and is
pinned only up to a root choice; no *rational* expression in `Δ₂` isolates it. The third scale makes
recovery rational because `y³ − y = (y² − y)(y + 1)` factors through the second. Minimality — for
which finite `S ⊆ ℕ` is `exp x` rationally recoverable from `{F(nx) : n ∈ S}` — is **open**, and is a
clean algebra question about `yⁿ − y`.

### What this is not

- **Not a cheap tree.** `F`'s right child computes `1/x`, and `d(1/x) = 4`, so `F` is not a
  low-depth object. The theorem is about the *functions*.
- **Not yet a basis.** Recovering the two primitives is weaker than recovering every `eml` node from
  unary `F` data. That is the next question and it is not addressed here.
- **Not a new lower-bound instrument yet.** The dilation operator annihilating `log` exactly is
  suggestive — every depth argument so far has compared growth envelopes, and this compares
  *structure* — but no exclusion has been derived from it.

The identity was supplied rather than discovered here; it was re-derived and checked numerically
before formalising, since the original derivation was not available to this session.

## [Unreleased] — 2026-08-20

### The mirror band — half proved, and the other half is the cancellation problem

`MirrorBand f := BelowIdentityUnbounded f ∧ super-logarithmic`. The mirror of `IntermediateBand`:
`f x < x` in place of `x < f x`, everything else kept.

`mirrorBand_not_depth_three_bounded_left` — **no depth-3 node with bounded left exponential lies in
the class.** Two branches, split by the totalisation:

- right child positive: `depth_le_two_decay_on_ray` caps `−log (B x)` at `C + log x`, so the node is
  at most `K + C + log x` — killing super-logarithmicity;
- right child non-positive: its logarithm is `0`, the node **is** `exp (A x) ≤ K` — killing it more
  cheaply, and needing no decay bound at all.

**The growing-left case is not a mirror of anything and is left open.** There `exp (A x) ≥ exp x`
and `log (B x)` are both near `exp x` and cancel; that is the difficulty `ExpExpGapBelow` and
`BoundedCellApproach` exist for. I had claimed this half "needs no new instrument". That was wrong,
and the analysis that shows why is in the module: `log x` is reachable at depth 3 through *both*
branches, so `Hlog` has to cut both, and only one of the two cuts cheaply.

### Two corrections made during the proof, both mine

- **`set` is not a MachLib tactic.** My own note says grep before reaching for one; I reached first.
- **A lemma I introduced to bridge the totalised branches was false.** `exp (−C) ≤ C + log x` fails
  for very negative `C`. It was briefly `sorry`-ed to isolate the gap, and the gap turned out not to
  exist — those branches never needed a decay bound, only `C + exp (−C) ≥ 1` and `log x ≥ 0`. The
  false lemma is deleted; `sorry` count in the module is `0`.

Recording the second because the failure mode is specific: a `sorry` placed to *locate* a gap is
fine, but it must be removed by discovering the gap is not there — not left standing because the
build went green.

## [Unreleased] — 2026-08-19 (j)

### The Positive Translation Theorem — `x + 1` was a stratum, not a specimen

`MachLib/EMLDepthTameness.lean`.

```
    c > 0   ⟹   d_(0,∞)(x + c) = 4        exactly
    c = 0   ⟹   d(x)           = 0        it is `var`
    c < 0   ⟹   d_(0,∞)(x + c) ∈ {3, 4}   open which
```

`x_plus_c_band`, `x_plus_c_not_depth_le_three`, `x_plus_c_depth_exact_four`.

**The magnitude of the translation is irrelevant.** Every positive shift, however small, costs
exactly four levels; the shift by zero costs none. The discontinuity is at the *presence* of the
translation, not its size.

**The upper bound needed nothing new.** `eml_const_offset_closure` was already unrestricted in `c` —
the whole question was the lower bound, and that is where the sign enters.

### The asymmetry is now formal, not suspected

For `c < 0` the band's third condition `x < f x` fails **structurally**, not inconveniently:
`x + c < x` everywhere. What survives is the weaker below-identity class, giving `d ≥ 3` —
`x_plus_neg_c_belowIdentity`, `x_plus_neg_c_not_depth_le_two`.

So the two sides are genuinely different at the present state of knowledge, and whether the negative
gap `{3,4}` is real or an artefact of the missing instrument is **open**. That is the first question
this family raises which the existing machinery cannot answer, and it is a better question than the
one we started with.

### `IntermediateBand` has paid for itself

It was introduced to repair a broken sharpness composition. It has now proved an entire
*parameterised family* of exact lower bounds, which is the test of whether an abstraction is a
complexity invariant or a theorem-specific device. It is the former.

Discrimination: the depth-4 analogue of the positive lower bound is **provably false** (so the bound
is sharp), and `c = 0` is **provably not excludable** — `x + 0` is `var`, at depth `0`, so the
hypothesis `c ≠ 0` is doing real work rather than being defensive. `sorryAx` absent.

## [Unreleased] — 2026-08-19 (i)

### The general Apollonius reduction closes — abandoned twice as "the coefficients explode"

`Geometry/Apollonius/Elimination.lean`. `quadratic_of_linear` and `solves_iff_quadratic`:
**for an arbitrary triple and an arbitrary mode**, a centre determined affinely by the radius
reduces the remaining tangency to a single quadratic in `r`, with coefficients

```
    A = X₁² + Y₁² − D²
    B = 2UX₁ + 2VY₁ − 2D²·svπ
    C = U² + V² − D²π²
```

where `D` is the determinant, `(X₀,X₁)`, `(Y₀,Y₁)` the Cramer numerators, `U = X₀ − Dp`,
`V = Y₀ − Dq`. No hypothesis about the configuration beyond `sv² = 1`; non-collinearity enters only
where `D ≠ 0` is needed to produce the affine centre.

**The previous diagnosis was wrong and is now falsified.** The explosion came from expanding the
geometry into coordinates *before* normalising. Over the abstract Cramer data the reduction is a
short identity in eight atoms with no constant above `1`, and it closed on the second try — the
first failure was a syntactic regrouping (`X₀ + X₁r − Dp` does not contain `X₀ − Dp`), not a
capability limit.

### Numeral abstraction principle

Recorded as doctrine, because it has now closed four separate blockers:

> When proving a polynomial identity over `MachLib.Real`, expose only `0` and `1` to normalisation
> where practical. Replace derived concrete numerals by parameters, discharge their arithmetic
> relationships separately, and instantiate only after the symbolic identity has closed.

Two corollaries, each of which cost a build:

- **Definitions are not atoms.** `mach_mpoly` unfolds them and then faces whatever was inside.
- **Proof cost is not mathematical sharpness.** `√2 < 2` beats `5√2 < 8` here not because it is a
  better inequality but because it needs `2 < 4` rather than `50 < 64`, and constant-only
  comparisons are what the normaliser cannot do at all.

Full corpus builds, 634 jobs. 198 claims PASS, 10 ledger rows OK, aggregator 631/937.

## [Unreleased] — 2026-08-19 (h)

### All 23 exhibit coordinates Lean-checked — the doubled class closes

`Geometry/Apollonius/Coordinates.lean`. `be4_tangent` and `be5_tangent`, six more tangencies,
`sorryAx` absent. **Every concrete circle on `monogate.org/proofs/apollonius` is now checked in
Lean**, across all three configurations.

### What actually unblocked it, after six failed attempts

One rule, applied consistently instead of incrementally:

> **Abstract every numeral before handing an expression to the normaliser.**

`doubled_bridge` contains no numeral except `1` — the scale `n`, the divisor `dd`, the separation
`sep` and the external constants `S`, `B` are all parameters related only by hypotheses. It compiled
on the first attempt after three wiring attempts had each died on a different concrete constant.

The same rule closed every remaining piece: `neg_sq`, `prod_sq`, `sq_collapse`, `lt_of_sq_lt`,
`mul_one_add`, `double_it`, `sep_helper` are all generic, and each replaced a call that had been
evaluating `9`, `81`, `784` or `50` inline.

### The three diagnoses that were wrong, and the one that was right

- **"Coefficient magnitude."** No — solutions 1 and 8 close with `8`; an attempt failed with `18`.
- **"Constants are trees, so large ones are unreachable."** No — constants never *distributed* are
  free.
- **"`mach_mpoly` can't do this arithmetic."** No — the same identity with a universally quantified
  atom closes instantly. What failed was `mach_mpoly [h]` where `h` is a **def**: it unfolds.
- **Right:** the normaliser is cheap in variables and expensive in constants, and *definitions are
  not atoms*.

Choosing the loose bound `√2 < 2` over the tight `5√2 < 8` matters for the same reason: the loose
one needs `2 < 4`, the tight one `50 < 64`, and constant-only comparisons are what the normaliser
cannot do at all.

Full corpus builds, 634 jobs.

## [Unreleased] — 2026-08-19 (g)

### The `√34` quartet falls to a factorisation — 21 of 23

`Geometry/Apollonius/Coordinates.lean`. Four more points, twelve more tangencies, `sorryAx` absent.

**The residual factors, and that is the whole story.**

```
    2c² + t² − c²t² − 1  =  1 − (c² − 1)(t² − 2)
```

The direct route clears both denominators with `144 = 16·9` and puts constants like `288` inside
every one of the twelve identities; the normaliser refuses. The factored form leaves the twelve
identities with **no constant but `1` and `2`**, and collapses the entire arithmetic burden into one
side fact proved once — `(c²−1)(t²−2) = 1`, which for `c = 5/4`, `t = √34/3` is `(9/16)(16/9)`.

Even that is discharged without forming `144` in any goal the normaliser must expand: scale each
factor separately (`16(c²−1) = 9`, `9(t²−2) = 16`) and cancel. `prod_one_of_scaled` is the reusable
piece.

**The lesson, stated once more because it keeps paying:** do not hand the normaliser a large
identity and raise limits. Find the form in which the large constants never meet.

### The last two: not done, and three facts recorded so the next attempt does not rediscover them

The doubled `(inner,outer,outer)` class, `r = 25/7 ± 45√2/28`.

1. **One lemma covers both** — solution 5 is solution 4 under `s ↦ −s`.
2. **A factor of `9` runs through everything** — `28x = −9(5+4e)`, `28(r−1) = 9(8+5e)`. With
   `u = 5+4e`, `v = 8+5e` every constant stays under `80`; leaving the `9` in forms `2025`, `3240`,
   `5184` and fails.
3. **`v = u·e` exactly**, since `(5+4e)e = 5e + 4e² = 8 + 5e` when `e² = 2`. So the internal
   tangency is `2u² − u²e² = u²(2 − e²) = 0` — no constant but `2`.

Still open: the two external tangencies carry `115` and `128`. They factor —
`(128+45e)² − (115+36e)² = 81(13+9e)(3+e)` and `(13+9e)(3+e) = u²` — so a difference-of-squares step
holds the constants under `57`. Derived here, not yet carried out in Lean.

**Blocked on presenting three identities, not on geometry and not on `natCast`.**

## [Unreleased] — 2026-08-19 (f)

### Both Soddy circles of `d = 5/2` — 17 of 23, and the last six are located precisely

`Geometry/Apollonius/Coordinates.lean`. The outer and inner Soddy circles of the third
configuration are Lean-checked. Their residual is `2c² − c²s²`, which is zero for **any** `c` once
`s² = 2` — so these two points need no numeric value at all, and are cheaper than any point in
either earlier configuration. The separation is `2c` exactly, which is why.

### The remaining six are blocked on arithmetic presentation, and both routes are written down

**The `√34` quartet.** Residual `2c² + t² − c²t² − 1` with `c = 5/4`, `t = √34/3`. It **factors**:

```
    2c² + t² − c²t² − 1  =  1 − (c² − 1)(t² − 2)
```

and `(c²−1)(t²−2) = (9/16)(16/9) = 1`. Clearing both denominators the direct way needs `144 = 16·9`
and a numeral check `18·25 + 16·34 − 25·34 − 144 = 0` that exceeds the normaliser even though every
step is elementary. The factored form needs only `(16c² − 16)(9t² − 18) = 144`, whose constants are
all at most `18`. Untried, and the obvious next attempt.

**The doubled `(inner,outer,outer)` class.** `r = 25/7 ± 45√2/28`, centre `−45/28 ∓ 9√2/7`. Scaling
by `28` leaves `567·(s² − 2)`, and `567 = 81·7` factors out of the whole identity: writing
`45 + 36s = 9(5 + 4s)` and `72 + 45s = 9(8 + 5s)` drops the inner computation to constants of at
most `80`. Also untried.

Both are bounded and mechanical, and blocked on arithmetic presentation rather than on geometry —
which is the same sentence as three attempts ago, except that this time the route is written out
rather than guessed at.

## [Unreleased] — 2026-08-19 (e)

### The exceptional locus is fully checked — 15 of 23 exhibit points

`Geometry/Apollonius/Coordinates.lean`. All **seven** solutions of `d = 2√2, ρ = 1` — the
configuration where one class degenerates from quadratic to linear and the count drops to seven —
are now Lean-checked. Twenty-one more tangencies, `sorryAx` absent. This is the exhibit's *default*
view, so the page a visitor lands on is now fully green.

**Two irrationals, but three atoms would have been a mistake.** The coordinates involve `√2`, `√3`
and `√6`. `√6` is *not* a third atom — it is `√2·√3`, and treating it as a product keeps every
identity in two variables with `s² = 2` and `u² = 3` as the only facts. Four of the seven solutions
(all the `√6` ones) then share a single residual, `2s² + u² − s²u² − 1`, across all twelve of their
tangencies.

**The degenerate class's circle needed three devices at once**, and is the template for anything
similarly awkward: `q = √2/4` compressed with `8q² = 1`; the rational radius `3/2` compressed as `g`
with `2g = 3`; and the separation passed as its own variable `dd` with `dd = 8q`, because the
consumer's circle carries it as `2√2` and those are equal without being syntactically equal. Then
×4 to clear both denominators, with the squaring split in two so no single `mach_mpoly` call has to
distribute `(q − 8q)²` and reconcile `200` at once.

**One more misread limit.** The first failure here was `maximum recursion depth`, not a timeout —
raisable with `set_option maxRecDepth`. Reading the error rather than assuming the previous cause
saved another wrong diagnosis. Three failure modes have now appeared in this module and they need
different fixes: `acLt` blowup (compress the constant), `maxRecDepth` (raise it), and plain
`maxHeartbeats` (split the step).

Still computed-only: the eight points of `d = 5/2`. Their coordinates carry denominators of `7`,
`12` and `28` over `√2` and `√34`; the technique is proved out, the constants are just larger.

## [Unreleased] — 2026-08-19 (d)

### All eight flagship Apollonius coordinates Lean-checked — and the wall was misdiagnosed twice

`Geometry/Apollonius/Coordinates.lean`. Twenty-four tangencies (eight circles × three), against the
geometric predicates, zero residual symbolically. `sorryAx` absent from all eight.

**The technique, which is the transferable part.** Six of the eight have irrational centres with
denominators. Written naively every identity dies in `Lean.Meta.acLt` — the AC term ordering `simp`
uses — because distribution generates nested `(1+1)` constant trees. `maxHeartbeats 4000000` does
not help: the growth is in the ordering, not the arithmetic.

**Compress the constant into the variable.** Not `3 + 3h` with `h = √2/2`, but `3 + v` with `v = 3h`
and the single fact `2v² = 9`. The `3` never enters the distribution, no constant above `4`
survives, and the identity closes at once. Same for the `√21` quartet: `κ = √21/3`, `3κ² = 7`.
All twelve of those identities share one residual, `7 − 3κ²`.

### Three wrong diagnoses, corrected

Recorded because each cost an attempt and each was stated confidently.

1. **"The limit is coefficient magnitude."** No: solutions 1 and 8 close with `8`, and an attempt
   failed with `18` written in five nodes.
2. **"Constants are syntax trees, so large constants are unreachable."** Closer, still wrong.
   Constants that are never *distributed* — the `4` of the centre separation — cost nothing. The
   cost is `acLt` on nested constant trees under distribution.
3. **"`mach_mpoly` cannot do this arithmetic."** Refuted by specimen: the same identity with a
   universally quantified atom closes instantly. What actually failed first was `mach_mpoly [h]`
   where `h` is a **def** — it unfolds to `rt2 / (1+1)` and the normaliser then faces a quotient.
   *The normaliser's atoms are variables, not definitions.*

A fourth, more embarrassing one: an early version discharged the residual with `rw [← z]`, turning
the `0` of `u - v = 0` into the residual expression — which also rewrote the `0` inside every
`(c - 0)` term. That timeout was read as a scale limit. It was a rewrite hitting more occurrences
than intended.

**The general lesson**, since this is the second time an apparent capability limit turned out to be
a structuring mistake: a timeout is a hypothesis, not a measurement. Test it with a specimen that
isolates the suspected cause before recording it as a limit.

Gates: 198 claims PASS, 10 ledger rows OK, aggregator 631/937, `sorryAx` absent.

## [Unreleased] — 2026-08-19 (c)

### The Apollonius count, in list-cardinality form — and the disclaimer was wrong about why

`MachLib/Geometry/Apollonius/Enumeration.lean` (new). The public exhibit carried:

> **NOT PROVED — list-cardinality form.** MachLib is Mathlib-free and has no `Finset` layer; the
> count is a derivation from per-mode theorems plus the antipodal pairing, not a
> `List.length = 8` theorem.

**The premise was true and the inference was wrong.** `List`, `List.length` and `List.Nodup` are
Lean **core**, not Mathlib, and a finite enumeration needs no `Finset` at all. `Mode` is a structure
of three two-element enumerations carrying `DecidableEq`, so the mode half of the count is not
merely provable but *decidable*.

| new | states | axioms |
| --- | --- | --- |
| `allModes_length` | `allModes.length = 8` | **none** |
| `allModes_nodup` | no mode listed twice | **none** |
| `allModes_complete` | no mode missing | `propext` only |
| `canonical_plus_anti_length/_nodup/_complete` | `4 + 4 = 8`, disjointly | none / none / `propext` |
| `two_solutions_per_class` | each class contributes two distinct positive-radius solutions | Real base |
| `eight_solutions` | **a `List` of length 8, `Nodup`, every entry a genuine solution** | + `Classical.choice` |

Three facts depending on **no axioms whatsoever** is worth recording: the eight-ness of the mode set
is pure computation, and was being described in prose.

**Also already true and overlooked:** `canonicalModes_length : = 4`, `canonicalModes_nodup` and
`mem_canonicalModes_iff` have been in `Mode.lean` since the original arc. The *four*-class half of
the count was already in list-cardinality form when the disclaimer said none of it was.

**Why `eight_solutions` is an existential over lists rather than a `noncomputable def`.** The roots
arrive from `QM_two_roots_of_gp` as an existential, so a definition would have to thread
`Classical.choose` through its own signature. Producing the list inside the statement keeps choice
out of every signature while still delivering an actual `List` whose `length` reduces to `8` by
computation.

**`Nodup` is the clause that makes the length mean anything** — eight entries are a count only once
no entry repeats. Distinctness has two independent sources: within a class, the two roots of the
class quadratic differ (same mode, different radii, or opposite modes via `anti_ne`); across
classes, the four canonical modes and their four antipodes are eight distinct modes, which is
`canonical_plus_anti_nodup` and decides.

Still NOT proved, and still disclosed: the eight concrete coordinates for a specific configuration.
MachLib proves the count and its structure, not those particular numbers.

## [Unreleased] — 2026-08-19 (b)

### Citable exact-depth declarations: `d(log x) = 3`, `d(x + 1) = 4`

Filed against `1op/reports/LEDGER-DEFECT-T30.md`. The 1op site refused to publish two exact-depth
results because no single declaration stated them — the lower bound for `log x` existed only as an
immediate consequence of the transition machinery, and a renderer must cite a declaration rather
than reconstruct an argument. That refusal was correct. This is the repair.

New in `EMLDepthTameness.lean`:

| declaration | states |
| --- | --- |
| `log_belowIdentityUnbounded` | `log x` is unbounded above and eventually strictly below the identity |
| `log_x_not_depth_le_two` | no tree of depth ≤ 2 agrees with `log x` on `(0,∞)` |
| `log_x_depth_exact_three` | both halves, **with the domain in the statement** |
| `x_plus_one_depth_exact_four` | both halves for `x + 1`, likewise |

**Why `log_belowIdentityUnbounded` had to exist.** `belowIdentityUnbounded_at_depth_three` already
proved the class non-empty at depth 3 — but it returns an *existential*, so nothing downstream can
recover which tree it exhibited, and no consumer wanting "`log x` specifically" can get there from
it. An existence proof is not a citable fact about a named object.

**Domains are in the statements, deliberately.** An unlabelled `d(x+1) = 4` is a different and
unsupported claim; the corpus already carries one live defect of exactly that shape
(`x_sq_ray_not_depth_le_three`, where a `(0,∞)` floor was paired with a `(1,∞)` witness). The two
new `*_depth_exact_*` theorems quantify the agreement clause explicitly so the pairing cannot drift.

**Discrimination checks.** The depth-3 analogue of `log_x_not_depth_le_two` is *provably false*
(`logTree var` witnesses it, specimen compiles), so the bound is not vacuous. `sorryAx` absent from
both new exact-depth footprints. 198 claims PASS, 10 ledger rows OK.

## [Unreleased] — 2026-08-19

### `d(x + 1) = 4` exactly — a missing conjunct was blocking the lower bound

`MachLib/EMLDepthTameness.lean`. Found while drafting §5 of the finite-depth-tameness manuscript,
which is the intended function of writing the paper against the corpus rather than from memory.

**The defect.** `superlinear_subexp_not_depth_le_two` takes three band hypotheses
(`H1` unbounded, `H2` sub-exponential, `H3` superlinear). `superlinear_subexp_not_depth_le_three`
takes **four** — the extra one being `Hlog : C + log x < f x` infinitely often. But
`band_exclusion_fails_at_depth_four` certified `x + 1` against only the first three. So the depth-4
refutation was aimed at the *depth-2-shaped* statement, not at the depth-3 theorem it was being
paired with for sharpness. A refutation of a weaker claim does not refute the stronger one, and the
sharpness argument did not close.

**The repair.** `x + 1` does satisfy `Hlog`; it had never been proved. Substituting `x = exp w`
turns the goal into `C + w < exp w + 1`, and `two_mul_add_le_exp` supplies `w + w + (C+2) ≤ exp w`.
Choosing `w := exp T + exp X` dominates `T`, `X` and `0` at once, which is what the three side
goals need. `band_exclusion_fails_at_depth_four` now carries all four conjuncts.

**The consequence, which was not the point of the repair.** With four hypotheses certified, the
depth-≤3 band theorem can finally be *instantiated* at `x + 1` — it could not be before, since the
instantiation needs all four. New:

```
x_plus_one_not_depth_le_three : no tree of depth ≤ 3 agrees with x + 1 on (0,∞)
```

With `xPlusOneTree_depth = 4` this pins `d(x + 1) = 4` exactly. The addition-closure question is
settled in both directions: EML *is* closed under `+1` (which already refuted the natural conjecture
that it is not), and the cost is exactly four levels. The upper bound was known since the closure
refutation; **the matching lower bound was open, and a missing conjunct was what kept it open.**

**Discrimination checks, because a new exact-depth result is exactly where a vacuous theorem would
hide.** The depth-4 analogue of `x_plus_one_not_depth_le_three` is *provably false* — `xPlusOneTree`
witnesses it, and that specimen compiles — so the bound is not vacuous. The identical proof script
is rejected at `depth ≤ 4` with a type mismatch, so the bound is not being silently coerced.
`sorryAx` absent from all three new footprints; 198 claims and 10 ledger rows still green.

**Refactor note.** The four hypothesis proofs moved into `x_plus_one_band_hyps` so that the
refutation and the exclusion consume the same certified facts rather than two drifting copies. That
is the structural reason the defect existed: the hypotheses were inlined in one theorem and
therefore could not be reused by, or compared against, the other.

**`IntermediateBand` — the band is now an object.** The four conditions are a `def`, and
`intermediateBand_not_depth_le_three` is the exclusion stated against it. Supplying three quarters
of the premise is now a **type error** rather than a reading error — verified with a specimen that
passes only `H1` and is rejected. `x_plus_one_band_hyps : IntermediateBand (fun x => x + 1)`.

The raw four-argument `superlinear_subexp_not_depth_le_three` is deliberately **kept**, not
replaced: its registered claim pins `statement_mentions` including `exp`, which folding the
conditions into a definition would hide from the auditor. So the raw form stays the audited surface
and the named form is the composable one. Both are proved; they are definitionally the same theorem.

**A gate gap, recorded not built.** `tools/claim_audit/BACKLOG.md` (new) records what this defect
shows: every registry obligation — `conclusion_mentions`, `statement_mentions`, `hypotheses_count`,
`proof_uses` — ranges over a **single theorem**, so nothing can assert that a sharpness witness
establishes the premise of the theorem it witnesses against. That relation is about a *pair*.
Building it properly needs a new obligation kind and a `--bless-relations` ceremony, which one
specimen does not justify. The backlog also records a cheap version available now that `IntermediateBand`
exists: register `statement_mentions: ["IntermediateBand"]` on the exclusion and
`conclusion_mentions: ["IntermediateBand"]` on the witness, and the two sides are forced to speak
the same predicate at the cost of two registry rows and no ceremony.

## [Unreleased] — 2026-08-16

### Verified Apollonius: the flagship instantiated — and natCast turned out not to be needed

`MachLib/Geometry/Apollonius/Examples.lean`. Three unit circles at `(0,0)`, `(4,0)`, `(0,4)`.

`flagship_gp` discharges `SymmetricGeneralPosition` for it, and both conjuncts are genuinely
*checked*: `d² = 8ρ²` would need `d ≈ 2.83`, and `d = 4` clears it — but nothing about the picture
makes that obvious, which is exactly the trap the earlier seven-circle counterexample set. An
aesthetically convenient configuration is not automatically a generic one.

`flagship_exactly_two_per_mode` is then the whole symbolic development instantiated at one
configuration: every mode has exactly two signed solutions, attained and no more. With the antipodal
law that is the eight — sixteen signed solutions in eight antipodal pairs, one member of each pair
carrying a positive radius.

**`natCast` was not needed.** The flagship's constants are `4`, `8` and `16`, small enough that the
unary `(1+1)` encoding closes each obligation directly, and the module compiled first try. That is
worth recording next to the earlier failures, because it corrects the scope of the numeral problem
one more time: the wall was never about *input* size. It was about the constants the class
**quadratic generates** — `1.4 × 10⁴` for the scaled `d = 8, ρ = 2` configuration — and inputs of
this size cost nothing at all.

So the diagnostic chain across this arc reads: the wall is real → it is not degree → it is not
presentation → it is nested constants under distribution → and the constants that matter are the
*derived* ones, not the ones you type. Each step narrowed the claim, and the last two narrowed it
after it had already been committed.

The layering the plan asked for holds: theorems live in `SymmetricTriple` over symbolic `d` and `ρ`;
`Examples` supplies values and discharges hypotheses. Numeral plumbing stayed below the generic
development and never leaked upward.

### Verified Apollonius: exactly two signed solutions per mode — the count assembled

`exactly_two_signed_solutions_per_mode` puts both halves together: **attained**
(`QM_two_roots_of_gp` gives two distinct roots, `solution_of_root` realises each) and **no more**
(`at_most_two_of_gp`). Both directions at once, which is what exactly means.

`solution_of_root` is the constructive step that was missing: a root determines a centre through the
locus, and `exists_scaled` inverts `2d·x = …`. That remains the *single* inversion point in the
whole development — no other part of the geometry forms a quotient.

**And that is the eight.** Eight modes × two signed solutions = sixteen signed solutions; the
antipodal law pairs them, `(x, y, r)` in mode `m` with `(x, y, −r)` in `m.anti`; every root is
nonzero (`root_ne_zero`), so each pair has exactly one member with positive radius; and distinct
pairs give distinct circles because `mode_unique` separates modes and `centre_unique` separates
centres. **Sixteen signed, eight geometric.**

**Why the final count is a derivation and not a `List.length = 8` theorem.** `MachLib` is
Mathlib-free and has no `Finset` or cardinality layer. A list formulation would have to construct
eight elements through `Classical.choice` and prove `Nodup` by hand — bookkeeping that would obscure
rather than strengthen what is proved. Every *mathematical* ingredient of the count is a theorem;
what is missing is a container, and the file says so rather than implying more.

That is the honest end of the symbolic branch. What it establishes, for the symmetric family under
`0 < ρ ∧ 2ρ < d ∧ d² ≠ 8ρ²`:

* the three-equation system reduces to a line plus one quadratic, for every mode;
* the eight modes are four antipodal classes;
* each class's quadratic is genuinely quadratic and has positive discriminant;
* each has two distinct roots, both nonzero, both realised by actual solutions;
* solutions of one mode with equal radii are equal circles, and a solution's mode is determined.

And, off the generic path, `oii_at_most_one_radius`: at `d² = 8ρ²` one class degenerates to a linear
equation, so the count drops to seven at an exceptional locus that has nothing to do with the
circles touching.

### Verified Apollonius: attainment for every class

`QMdisc_pos_all` — every one of the eight modes has a positive discriminant under general position.
Six go through `disc_pos_of_lead_neg`; `(o,i,i)` goes through its factored discriminant, and its
antipode `(i,o,o)` through `QMdisc_anti`. The two routes are genuinely different arguments, which is
the honest shape: `(o,i,i)` is precisely the class whose leading coefficient can vanish while its
discriminant does not.

`QMdisc_anti` proves the discriminant is antipode-invariant, component-wise rather than by
re-deriving: `QMlead` is invariant, `QMmid` **negates** and is then squared, `QMconst` never mentions
the mode. So four classes carry four discriminants — the same 8→4 collapse the antipodal law gave for
solutions, now for the discriminant.

`QM_two_roots_of_gp` — **every class attains two distinct real roots**, and `QM_roots_decode` adds
that both are nonzero. With the antipodal law that is the eight: four classes, two distinct roots
each, each nonzero root decoding to one circle in one of the class's two modes, and `mode_unique`
making those circles distinct.

**The sqrt firewall, tested where it counts.** This is where `sqrt` finally enters the development —
at the *candidate* boundary, exactly as designed six commits ago. The footprint confirms the design
held: `MachLib.Real.sqrt` and `MachLib.Real.sqrt_sq_nonneg` appear, and **`sqrt_neg_zero` does
not**. The totalisation branch is unreachable because `QMdisc_pos_all` supplies strict positivity,
so `sqrt_sq_nonneg` fires on a manifestly nonnegative argument. A predicate written with `sqrt` back
at the start would have made that guarantee impossible to state.

**A tactic note worth keeping.** The eight-way dispatch was first written with `first | … | … | …`
and three routes. It failed: `first` cannot backtrack out of an error raised *inside a nested `by`
block*, so a branch whose `mach_mpoly` made partial progress before failing was committed to rather
than abandoned. Replaced with explicit per-case bullets. The general lesson is narrower than "avoid
`first`": `first` backtracks over *tactic failure*, not over *elaboration errors in subterms*.

### Verified Apollonius: the last symbolic blocker falls — split the call, not the budget

`QMdisc_oii_eq : QMdisc (o,i,i) = 32·d²·(d² − 4ρ²)²`, and with it

`QMdisc_oii_pos` — **discriminant positivity from separation alone**. No band split, no appeal to
the sign of the leading coefficient. `d > 2ρ` gives `d² − 4ρ² > 0`, its square is positive, `32d²`
is positive. The class attains two distinct roots throughout `d > 2ρ`, *including* the band
`4ρ² < d² < 8ρ²` where the cheap `lead < 0` argument does not apply.

**How, after two failed assaults.** The degree-3 identity dies in `acLt` as one `mach_mpoly` call —
69 s at 4 000 000 heartbeats. Split into four steps, each expanding **at most one** product, every
step closes in about a second:

    oii_core      (8Y−X)(X−2Y) = 2XY − (X−4Y)²        degree 2
    oii_regroup   4·(4P)·(2XQ) = 32X(PQ)              monomial, P and Q atomic
    oii_midsq     (8Zw)² = 64Z²w²                     monomial
    oii_final     64X²Y − 32X(2XY − E) = 32XE         one distribution, E atomic

The move is to keep each binomial product **atomic** (`P`, `Q`, `E`) until the last moment, so no
call ever distributes two brackets at once. Neither raising budgets nor compressing variables was
the answer; splitting the call was. `natCast` was not needed here after all — worth noting, since
the diagnostic pointed at it and the diagnostic was correct about the *cause* while a different fix
turned out to be available for this particular obstruction.

**The structural payoff.** Discriminant positivity and leading-coefficient non-vanishing are now
visibly **independent** properties with different exceptional loci:

    d² = 4ρ²   kills the discriminant       — the separation boundary
    d² = 8ρ²   kills the leading coefficient — discriminant still positive

which is exactly why the seven-circle configuration is a **degree drop** and not a repeated root.
Folding both into one general-position predicate would have hidden that; deriving them separately
displays it.

### The acLt diagnosis, corrected and sharpened by four specimens

The previous entry said the cause was the unary numeral encoding "whatever the degree". **That was
too strong**, and running the specimens showed why:

| specimen | form | result |
| --- | --- | --- |
| A | nested `64`, pure commutativity, no distribution | **passes, 1 s** |
| A2 | nested `64`, degree-3 identity with subtractions | **fails, 69 s at 4 000 000 heartbeats** |
| B | *same identity*, constants as `natCast` | **completes, 1.9 s** |
| C | flagship numeral obligation, constants as `natCast` | **completes, 2.3 s** |

A is the one that corrects the earlier claim: nested constants are harmless on their own. The
blowup needs them to be **distributed over sums** — every `(1+1)` factor multiplies out across every
summand and the AC-permutation space explodes. A2 versus B isolates the encoding exactly: same
identity, same degree, same term structure, only the constants written differently, and a 4 000 000
heartbeat timeout becomes a 1.9 second completion.

So `natCast` is a **real normal-form improvement**, not a workaround — which is the question worth
having asked before committing to it. But it moves work rather than removing it: B and C both
finish by reporting `1 = 0` / `-1 = 0`, because `mach_mpoly` treats each `natCast N` as an opaque
atom and correctly declines to do arithmetic on them. The constant relations have to be supplied,
via `rw [← natCast_mul]`, where they reduce to `Nat` literal equality and are instant.

That is the documented `NatCastArith` recipe, now with measurements attached and with evidence that
it addresses the actual bottleneck rather than a suspected one.

### Verified Apollonius: the acLt wall diagnosed — it is the numeral encoding

A cheap experiment, and it answered the question the last two commits left open.

Substituting `X = d²`, `Y = ρ²` turns the `(o,i,i)` discriminant identity from degree 6 in `d, ρ`
into **degree 3 in two abstract variables** — the normaliser never has to rediscover a factorisation
inside the original nested expression. The failure *changed*: `maxRecDepth` cleared, and only
`Lean.Meta.acLt` remained, still unmoved at 5× heartbeats on the degree-3 form.

That isolates the cause. It is **not** polynomial degree, and **not** expression presentation — both
were varied and the wall stayed. It is the **unary numeral encoding**: `64` written as six nested
`(1 + 1)` factors generates an AC-permutation space `acLt` cannot search, whatever the degree.
`MachLib.Real` carries `OfNat` for `0` and `1` only, so at this layer there is no other way to write
a constant.

Two independent tasks now agree — the numeral instantiation (constants ~10⁴) and this identity
(constants ~64) — and the variable-compression experiment separates the two candidate explanations
cleanly. `natCast`, where a constant is a single atom, is the thing to try next, and it is now a
*diagnosis* rather than a guess.

The three `(o,i,i)` coefficient identities close and are kept: they are exactly what the assembled
discriminant proof will consume once constants can be written atomically. The target is
`QMdisc (o,i,i) = 32·d²·(d² − 4ρ²)²`, from which positivity follows from **separation alone** —
no band split, and no appeal to the sign of the leading coefficient. That is a better structural
statement than the conditional one currently proved, and it is one identity away.

Worth separating the two exceptional loci, because they do different jobs:

    d² = 4ρ²   the separation boundary — kills discriminant positivity
    d² = 8ρ²   kills the LEADING COEFFICIENT without killing the discriminant

So the seven-circle configuration is not a repeated-root event. It is a **degree-drop** locus: the
class equation stops being quadratic and becomes linear. That is why encoding both conditions into
one general-position predicate would have obscured the phenomenon rather than explained it.

### Verified Apollonius, slice H: attainment machinery, and a wall named

`exists_scaled` and `two_distinct_roots` make attainment *constructive*: given any `s` with
`s² = b² − 4ac` and `s ≠ 0`, the two roots exist and are distinct. The caller supplies the square
root rather than the theorem computing one, and `(−s)² = s²` means the same statement covers both
branches. `exists_scaled` is the single place in this development where a field inverse is formed —
everything above it consumes the scaled equation `u·r = v`.

`disc_pos_of_lead_neg` is the useful trick: `b² − 4ac = b² + 4(−a)c` is a nonnegative square plus a
positive product, so **a negative leading coefficient makes the discriminant positive with no
expansion at all**. Under separation that covers the `(o,o,o)` shape (`lead = −4d²`) and the
`(o,o,i)`/`(o,i,o)` shape (`lead = 16ρ² − 4d² < 0` since `d² > 4ρ²`) — six of the eight modes, for
free.

**The `(o,i,i)` shape is a genuine exception and is recorded as one.** Its leading coefficient
`32ρ² − 4d²` is negative only when `d² > 8ρ²`. In the band `4ρ² < d² < 8ρ²` the discriminant is
still positive — it equals `32d²(d² − 4ρ²)²` — but establishing that requires expanding the
degree-6 identity, and `mach_mpoly` hits the same `Lean.Meta.acLt` wall as the numeral
instantiation: unchanged at **10× heartbeats and 500× recursion depth**. Two independent tasks have
now hit the same limit from different directions, which suggests it is a property of the normaliser
rather than of either problem.

So attainment is proved for every class whose leading coefficient is negative, and the residue is a
single band for a single class — stated, bounded, and not papered over.

### Verified Apollonius, slice G: general position, minimised and derived

`SymmetricGeneralPosition d ρ := 0 < ρ ∧ 2ρ < d ∧ d² ≠ 8ρ²`. Three conjuncts, and the point is how
few that is.

**Deliberately not named `ApolloniusGeneralPosition`.** The predicate mentions only `d` and `ρ`,
which describe the equal-radius family and nothing else; for arbitrary triples the condition must
involve the per-class linear determinant, leading coefficient, discriminant and zero-root exclusion
separately. Naming a family condition globally is how a family theorem later reads as a universal
one.

**Minimised, not assembled.** The first draft had four conjuncts. Three turned out to be
*consequences*:

* **Discriminant positivity.** The three discriminants are `32d⁶`, `32d²(d²−4ρ²)(d²−2ρ²)` and
  `32d²(d²−4ρ²)²`, all positive once `d > 2ρ`, since then `d² > 4ρ² > 2ρ²`. Not a hypothesis.
* **Zero-root exclusion.** The constant term `2d²(d² − 2ρ²)` is mode-independent and nonzero for the
  same reason, so `root_ne_zero` **derives** the `r ≠ 0` that `mode_unique` needs. It was checked
  rather than allowed to disappear because every numerical example happened to have nonzero radii.
* **Two of the three leading coefficients**, `−4d²` and `16ρ² − 4d²`.

Only `32ρ² − 4d²` needs its own conjunct, and that is the non-geometric one, `d² ≠ 8ρ²`, whose
necessity `oii_at_most_one_radius` already established.

`QMlead_ne_zero` covers all eight modes at once. Worth noting *why* one theorem suffices: `QMlead` is
**antipode-invariant** — it depends on the signs only through the products `σ_Aσ_B` and `σ_Aσ_C` — so
eight modes carry only **three** distinct leading coefficients, one per antipodal class shape. Each
is excluded by a different conjunct, so all three conjuncts are load-bearing and none is redundant.

`at_most_two_of_gp` and `mode_unique_of_gp` then hold with **no side condition left over** — the
`QMlead ≠ 0` and `r ≠ 0` obligations are discharged inside rather than carried by the caller. That
`r ≠ 0` could be stated, tracked and finally retired is the payoff of the earlier decision to let the
algebraic layer represent `r = 0` instead of ruling it out by typing.

`quadratic_root_of_disc` and `quadratic_roots_distinct` add the attainment machinery to
`QuadraticRoots`: a root from any `s` with `s² = b² − 4ac`, stated on the scaled root `2a·r = −b + s`
so no quotient is formed, with the two branches `±√disc` being the *same* theorem applied twice.

### Verified Apollonius, slice F: "pairwise separated" is not general position

The natural guess for this family's general-position condition — that the input circles are mutually
external, `d > 2ρ` — is **false**, and the counterexample is not exotic. At `d² = 8ρ²` (`d ≈ 2.83ρ`,
comfortably separated) the `(outer,inner,inner)` class's leading coefficient vanishes, its equation
drops to degree one, and the class contributes **one** solution instead of two. That configuration
has seven tangent circles, not eight.

`oii_at_most_one_radius` proves the structural cause: with the leading coefficient zero and the
middle coefficient `8d²ρ` demonstrably positive, a linear equation with nonzero slope has a unique
root. `QMlead_oii_eq` and `QMmid_oii_pos` supply the two coefficients.

So the condition this family actually needs is `d > 2ρ` **and** `d² ≠ 8ρ²`, and the second conjunct
has no evident geometric reading. That is exactly the kind of thing a derivation finds and a guess
does not — and it is why `ApolloniusGeneralPosition` is *still* not defined. Had the obvious
predicate been written down at the start, it would have carried a false theorem, and the failure
would have surfaced only at the count.

`mode_unique` closes distinctness: **a solution with nonzero radius determines its mode.**
Subtracting the two tangency equations for one input leaves `2rρ(σ − σ') = 0`, and `r ≠ 0`, `ρ > 0`
force the signs to agree. So the eight solutions are eight *distinct circles* rather than eight
labelled ones — a circle cannot be tangent to the same input both externally and internally unless
its radius is zero. Note where the hypothesis bites: `r ≠ 0` is the same degenerate candidate the
algebraic layer deliberately keeps representable rather than ruling out by typing.

### Verified Apollonius, slice E: at most two solutions per mode

`at_most_two_solutions_per_mode` — three solutions of one mode contain a repeat, **as circles, not
merely as radii**. This is the completeness upper bound, and it is where the two halves built
separately finally compose: `at_most_two_radii_M` collapses two of the radii via the degree-2 root
bound, and `centre_unique` — the theorem non-collinearity was derived for — upgrades equal radii to
equal centres.

With the antipodal law that is the eight: four classes, at most two signed roots each, each nonzero
root decoding to one circle.

`QM_expand` puts the quadratic in coefficient form, proved by **exhausting the eight sign
assignments** rather than by carrying `σ² = 1` through a symbolic normalisation. `Sign` is a
two-element type, so the split is finite and each branch becomes a polynomial identity with literal
`±1` coefficients — which `mach_mpoly` closes, whereas threading the square relation through an
opaque atom does not. The earlier `1 = 0` failure was that same obstacle met the other way round.

`centresDet_eq` shows the family's centres have determinant `d²`, so the general-position hypothesis
`Elimination` derived is **automatic** here: the family satisfies it by construction rather than by
assumption, and `not_collinear` discharges it from `d > 0` alone.

`QMlead_ooo_ne` anchors non-vacuity: for `(outer,outer,outer)` the leading coefficient is `−4d²`,
which never vanishes, so the bound applies to that class with no side condition whatever. The other
three classes are the ones carrying a genuine degeneracy, and they carry it visibly.

**What is deliberately not claimed.** That the bound is *attained*. That needs the discriminant
positive and the roots nonzero — a separate question, and the honest place for the remaining
general-position conditions to be forced rather than assembled. "At most eight" is proved for this
family; "exactly eight" is not, and the ledger of this work says so.

### Verified Apollonius, slice D: all eight modes of the family at once

`solvesModeM_iff` generalises the single hand-written class to **every mode simultaneously**, with
the mode's signs carried symbolically. The remaining three classes needed no separate treatment:
the locus and the quadratic depend on the mode only through `σ_A − σ_B` and `σ_A − σ_C`, each of
which is `0` or `±2`, so one theorem covers all of them.

    locus       2d·x = d² + 2ρ(σ_A − σ_B)r,   2d·y = d² + 2ρ(σ_A − σ_C)r
    quadratic   (d² + 2ρ(σ_A−σ_B)r)² + (d² + 2ρ(σ_A−σ_C)r)² − 4d²(r² + 2σ_Aρ·r + ρ²)

Evaluating the signs over the four canonical classes gives three distinct leading coefficients, and
they name their own degeneracies: `−4d²` for `(o,o,o)`, which **never** vanishes; `16ρ² − 4d²` for
`(o,o,i)` and `(o,i,o)`, vanishing exactly at `d = 2ρ` — the mutually externally tangent inputs; and
`32ρ² − 4d²` for `(o,i,i)`, vanishing at `d² = 8ρ²`. The constant term `2d²(d² − 2ρ²)` is the same
for every mode.

This is the first place the general linearisation paid off downstream: `solvesModeM_iff` is proved
*through* `solvesMode_iff_linear` rather than by repeating the elimination, so the symmetric family
now inherits the general result instead of duplicating it.

**Two failure modes that look identical from the build log.** `mach_mpoly` reports "unsolved goals"
both when an identity is false and when it merely failed to normalise a sign. In this file the same
message covered a `-0 = 0` residue (real, closed by `mach_ring`), an associativity mismatch between
two ways of writing `4d²`, and a genuine copy-paste error — the constant for `C = (0, d, ρ)` written
as `d·d + 0·0` instead of `0·0 + d·d`. Only the third was a mistake, and only reading the residual
goal distinguished them. The forward direction had silently survived the same slip because
`mach_mpoly` normalises what `rw` demands syntactically.

### Verified Apollonius, slice C: the linearisation, and general position derived

`MachLib/Geometry/Apollonius/Elimination.lean`, plus `cramer_2x2` and
`quadratic_zero_of_three_roots` in `MachLib/QuadraticRoots.lean`.

`tangentEq_iff_linear`: **the difference of any two tangency equations is linear.** The quadratic
part `x² + y² − r²` is common to every tangency equation and cancels, leaving coefficients built
from the centres, the radii and the two signs. Stated once for arbitrary circles and signs, so
`solvesMode_iff_linear` reduces the three-equation system to one quadratic equation plus a 2×2
linear system — for any inputs and any mode, with no genericity hypothesis at all.

**The general-position condition was computed, not chosen.** Cramer's rule needs its determinant
nonzero; the determinant of this particular system works out to

    4 · ((B.x − A.x)(C.y − A.y) − (B.y − A.y)(C.x − A.x))

which is four times twice the signed area of the triangle of centres. So the hypothesis that appears
is exactly **the three centres are not collinear** — a condition on the centres alone, independent
of the radii and independent of the mode. `linear_det` is that identity. Had
`ApolloniusGeneralPosition` been defined before the elimination it would have been a plausible
guess; this is a derivation, and it is why the definition was deliberately withheld.

`centre_unique` shows the hypothesis is load-bearing rather than decorative: with non-collinear
centres, two solutions of the same mode with the same radius are the *same circle*. The proof is the
homogeneous case of Cramer. This is also the first half of distinctness — after it, telling two
solutions apart reduces to telling their radii apart.

`quadratic_zero_of_three_roots` strengthens the degree-2 bound: three distinct roots collapse the
whole polynomial to zero, rather than merely contradicting a nonzero leading coefficient. That is the
form needed where a reduced equation's coefficients are not known in advance.

**A sign convention that does not survive being ignored.** `mach_mpoly` treats `Sign.val` as an
opaque atom, so it does not know `σ² = 1`, and the `σ²ρ²` term in an expanded tangency equation does
not collapse to `ρ²`. Omitting that fact does not produce a suspicious goal — it produces `1 = 0`.
`Sign.val_sq` and `tangentEq_expanded` supply it once; every elimination step goes through the
expanded form.

What is deliberately **not** here: substituting the Cramer centre back to name the quadratic's
coefficients in full generality. Those are a twelve-variable expression and `mach_mpoly` is the wrong
tool at that scale. The reduction to one equation in `r` alone is proved; naming its coefficients is
a separate step, and `SymmetricTriple` shows what it looks like once the family is concrete.

### Verified Apollonius, slice B2: the roots, and why `√2` is the only irrationality

The class discriminant factors as `8d²(d−2ρ)²(d+2ρ)²` — a perfect square times `8`. So its square
root is `2√2·d·(d²−4ρ²)`, and **the only irrationality any solution of this family carries is `√2`,
for every `d` and every `ρ`**. `ℚ(√2)` suffices; no general algebraic number field is needed, which
is what makes an exact candidate representable at all.

`lead_mul_Q` states it in the informative form. For `r` scaled by the leading coefficient to the
quadratic-formula numerator,

    lead · Q(r)  =  d²(d−2ρ)²(d+2ρ)² · (s² − 2)

*unconditionally in `s`* — no hypothesis that `s` is a square root of anything. The identity says
exactly that the sole obstruction to `r` being a root is `s² ≠ 2`. Stating it this way rather than
as "`Q r = 0` given `s = √2`" keeps the informative object: the right-hand side exhibits the
discriminant's square part, isolates the irrationality into one factor, and **displays the
degenerate locus** `d = 2ρ`, which is precisely the configuration where the three input circles are
mutually externally tangent, the discriminant vanishes, the roots collide, and the class contributes
one circle rather than two.

`Q_eq_zero_of_root` then discharges the scaling, and one theorem covers *both* roots: `s` ranges
over both square roots of `2`, and negating `s` gives the other root.

`sqrt_two_sq` is the only place `sqrt` appears, and it is used safely — `sqrt_sq_nonneg` fires on a
manifestly nonnegative argument, so the totalisation branch is unreachable. The footprints confirm
it: `lead_mul_Q` and `Q_eq_zero_of_root` contain **no `sqrt` axiom at all**, and `sqrt_two_sq`
contains `sqrt` and `sqrt_sq_nonneg` but **not `sqrt_neg_zero`**.

This supersedes the numeral obstruction recorded below rather than solving it: the symbolic route
turned out to be the better theorem, since it holds for every symmetric triple instead of one.

### Verified Apollonius, slice B: one mode class, end to end

`MachLib/Geometry/Apollonius/SymmetricTriple.lean`.

The vertical slice — linear elimination, one quadratic, candidate, positive radius, three checked
tangencies — for a single antipodal class over the symmetric family `A=(0,0,ρ)`, `B=(d,0,ρ)`,
`C=(0,d,ρ)`. `solvesMode_iff` is the elimination: **the three-equation system is equivalent to a
line together with one quadratic in the radius.** Both directions are proved, because forward is
what completeness will consume and backward is what makes a candidate checkable.

The class is `(outer, inner, inner)` and the choice is deliberate. In `(outer, outer, outer)` the
two difference equations lose their `r` terms and the centre is *constant*, so the slice would never
exercise a centre that moves with the radius; here `2d·x = d² + 4rρ` genuinely couples them.

`certified_tangencies` closes the chain into `Circle.lean`'s **geometric** predicates: a positive
`r` on the locus satisfying the quadratic is a genuine circle externally tangent to `A` and
internally tangent to `B` and `C`. `at_most_two_radii` instantiates the degree-2 bound, which is
where it earns its place — without it the class could a priori contribute unboundedly many radii.

**No radical is ever computed.** The candidate is identified by the certificate `Q d ρ r = 0`, never
by a closed form, and `sqrt` is absent from the entire slice's axiom footprint. That is precisely
the freedom the certification layer wants: a candidate carries a root certificate, not an
expression. No division either — the elimination multiplies through by `4d²` and
`QuadraticRoots.mul_left_cancel` undoes the scaling.

The leading coefficient `16ρ² − 2d²` is displayed rather than hidden: it vanishes exactly when
`d² = 8ρ²`, degenerating the class to a linear equation, and nothing above assumes it away.

**A numeral obstruction, measured.** Instantiating the flagship numerically inside Lean is blocked,
and not by an oversight of ours: `MachLib.Real` carries `OfNat` instances for `0` and `1` only, so
`(2 : Real)` does not elaborate. Writing constants as `1+1+…` makes `mach_mpoly`'s AC matching
diverge — the degree-2 identity for `d=8, ρ=2` (constants reaching ~1.4·10⁴ after expansion)
exhausts **4 000 000 heartbeats**, twenty times the default, with no sign of progress. The corpus
gotcha "keep coefficients symbolic — `mach_mpoly` times out on `16·P²`" is exactly this. The route
for a numeric exhibit is `natCast` per `NatCastArith`, where the arithmetic reduces to `Nat`
literal equality; that is the next step, and it is why this slice is symbolic rather than numeric.

### Verified Apollonius, first slice: the antipodal law

`MachLib/Geometry/Circle.lean`, `MachLib/QuadraticRoots.lean`,
`MachLib/Geometry/Apollonius/Mode.lean`.

Apollonius' problem carries eight tangency sign triples, and each triple's algebra reduces to a
quadratic in the radius — naively as many as sixteen algebraic candidates against a classical
generic count of eight. The discrepancy is not resolved by discarding roots. It is a symmetry:
negating the radius and the mode together is the identity on the tangency equation, because every
sign-dependent term carries exactly one factor of `r` while `x² + y² − r²` is even in `r`. So
**the eight modes are four antipodal classes**, each carrying one quadratic whose two roots split by
sign between the class's two modes. Four classes times two roots is eight; there was never a
sixteen.

`tangentEq_antipodal` is that theorem and `eightModes_reduce_to_four` is the equivalence the solver
will rely on — enumerating four classes over a signed radius loses nothing. The four classes are
*derived* (`canonical_xor_anti`, `mem_canonicalModes_iff`), not encoded as a four-constructor
datatype, which would have made the conclusion true by construction.

The naive invariant this replaces is false, and a spike found the counterexample before any checker
hardened around it: for `A = (0,0,1)`, `B = (4,0,2)`, `C = (1,4,3)` the mode `(−1,+1,+1)` carries
two solutions and its antipode none. Two roots per class is invariant; one solution per mode is not.

**Tangency is algebraic, never a `sqrt` equation.** `MachLib.Real.sqrt` is totalised
(`sqrt_neg_zero : x < 0 → sqrt x = 0`) exactly as `log` is, so a predicate written with `sqrt` would
be satisfiable wherever the totalisation fires. Defining tangency as `distSq = (r+s)²` removes that
structurally: `sqrt_neg_zero` is absent from the footprint of `TangentExt`/`TangentInt` because
`sqrt` never appears in them. The geometric reading is a theorem (`tangentExt_iff`) carrying its
nonnegativity side conditions, not a definition.

Degree-2 root bounds are proved directly from the field axioms rather than through
`PolynomialRootCount`, which states in its own docstring that it "does not prove the general
degree/root-count theorem" — it carries degree 1 and *names* the general case as an open target. The
direct proof buys a strictly smaller trust base: the footprint of `quadratic_no_three_distinct_roots`
is the field axioms only — no order, no `sqrt`, no `exp`/`log`.

The axiom split is worth recording: `tangentEq_antipodal` needs **no order axioms at all** (it is a
ring identity), and `canonical_xor_anti` needs **no axioms at all** (`decide` over a finite decidable
type). Order enters only at `decode_of_canonical`, precisely where the sign of the radius is read.

**Epistemic status, kept straight.** The antipodal law and the root bounds are PROVED. The four class
quadratics for the flagship triple `A=(0,0,1)`, `B=(4,0,1)`, `C=(0,4,1)` — discriminants 32, 21, 21,
18, all positive, eight distinct solutions, all residuals exactly zero — are COMPUTED by sympy as a
discovery oracle and are *not* yet checked in Lean. "Exactly eight distinct tangent circles" is not
proved and is not claimed: it needs candidate verification, completeness and distinctness, none of
which exist yet. `ApolloniusGeneralPosition` is deliberately not defined — the proof should force
its definition rather than the definition presupposing the conclusion.

### The bounded-cell chain closes, and `Depth3DecayExp` with it

`boundedEmlCellApproachLarge_holds` is the router: it closes the last open cell of the bounded-cell
chain by dispatching an arbitrary `Q` onto the comparison layer. `Q` splits first — `const` and `var`
close outright, and only `eml P R` reaches the node, where the two child dichotomies leave `P` and `R`
each `const` or `c − log x`. Three of those four pairings were already lemmas; the fourth is the
moving `Q = L + a/x` that `cell_of_moving_Q` routes against all five node shapes.

Two rows above it were reductions carrying no content of their own, so they close in the same step:
`BoundedCellApproach` is a theorem, not a reduction, and the ledger has no **reduced** rows left.

`Depth3DecayExp` follows, by all four cells, dispatched by a trichotomy on the left child. The four
cells had been built one at a time against different hypotheses and never checked for coverage;
`depth_le_one_exp_bounded_or_grows` splits the grandchild with nothing in between, and the two
directions of the depth-≤1 log bound feed the two halves. No new analysis — the gap really was the
dispatch.

The refuted sibling `Depth3DecayHard` is the *stronger* statement (`C + x` against `C + exp x`), and
`depth3DecayExp_of_hard` proves Hard ⟹ Exp. Implication one way, antecedent false, consequent true:
the rung correction is sharp, one exponential, with the truth value flipping across that single step.

Three things the assembly found that the pieces could not. Enumerating the router's cases exposed a
missing fifth node shape; writing its inner dispatch exposed a bracket too loose to decide that
shape's `L = 1` row; and this pass exposed a ray mismatch in
`target_below_one_singly_exponential`, whose hypotheses were stated from `1` while every producer
hands them back past an existential. Generalised in place to a ray.

The obligations gate caught its own negative control twice in one day — its "correct rows stay
silent" specimen named a live open obligation, and both obligations it named were then discharged.
The open specimen is now a synthetic name no theorem can conclude, which is the only status that
does not go stale when the corpus improves.

### The conversion modulus, extracted

`exponent_gap_of_value_gap` — `G ≤ exp u − exp v ∧ u ≤ M ⟹ G · exp (−M) ≤ u − v`. The three cells of
the depth-3 decay decomposition each converted a value gap into an exponent gap by replaying the same
block; that block is now one theorem, and the price of the conversion is a parameter of it.

The modulus rides on the **upper** exponent `u`, not on `v`. That is forced rather than chosen: at all
three sites `v = log (Q x)` is the unknown the cell is trying to bound, so a modulus stated on `v`
would be circular exactly where it is used.

Keeping `M` free rather than collapsing it to `u` is what preserves the cells' different strengths:
`P = const` and `P = var` take `M = u` exactly, while the bounded cell takes `M = K`. **One conversion,
three moduli, no cell weakened** — the bounded cell survives on a decaying `exp(−C−exp x)` value gap
precisely because its modulus is constant, where the `var` cell's `exp(−exp x)` modulus demands a
constant gap. A version that discharged the modulus would prove one and silently lose the other.

Call sites 55 lines → 18. Footprints of all three consumers are unchanged from before the extraction.

### `d(x²) ≥ 4` on the ray — the bracket was malformed

`x_sq_ray_not_depth_le_three`. `4 ≤ d(x²) ≤ 8` had been quoted while its floor was proved for
agreement on `(0,∞)` and its ceiling (`sqTree`) holds only on `(1,∞)`. **A floor proved for a stronger
specification constrains nothing about a weaker one**, so nothing had ruled out a depth-5 tree on the
ray. Both brackets are now internally consistent: `(0,∞): 4 ≤ d ≤ 24` and `(1,∞): 4 ≤ d ≤ 8`.

The band theorem is reused unmodified by instantiating it at `f := t.eval`, which makes its agreement
hypothesis `rfl` and moves the ray restriction into the four witness obligations. Those are factored
into `x_sq_band_hyps` with strict witnesses, because the evidence for the floor never used a point
`x ≤ 1` in the first place.

## [Unreleased] — 2026-08-14

### An obligations ledger, and an honest limit on it

Five propositions have been introduced as named obligations — stated so a partial result can be
committed without overstating it. The ledger now lives at the end of `EMLDepthTameness` rather than
in commit archaeology:

| obligation | status | discharged by |
| --- | --- | --- |
| `TowerLowerBound` | **open** | — (only `TowerLowerBoundUpTo 4`); `towerReducesToSign_iff_towerLowerBound` makes this row and `TowerReducesToSign` ONE obligation |
| `SignHardCase` | **discharged** | `signHardCase_holds` (`EMLAnalyticDischarge`), on `eml_tree_analytic_on_interval` + `analytic_finite_zeros_compact` + `rolle_ct` |
| `DecayFloor` | **reduced** | `decayFloor_of_emlGermApproach` → `EmlGermApproach` — an *equivalence*, not a shrink; a three-row cycle, one open obligation (clamped half: `decayFloor_clamped`) |
| `EmlGermApproach` | **reduced** | `emlGermApproach_of_growthEnvelope` → `GrowthEnvelope` — closes the cycle; the missing input as an *approach* question between two germs, the idiom an external theorem would be cited in |
| `GrowthEnvelope` | **reduced** | `growthEnvelope_of_decayFloor` → `DecayFloor` — the other half of the same cycle |
| `VarLeftEmlRightHard` | **discharged** | `varLeftEmlRightHard_of_band`, for band targets |
| `Depth3DecayHard` | **refuted** | `not_depth3DecayHard` (witness `dep3CounterRight`) |
| `Depth3DecayExp` | **discharged** | `depth3DecayExp_holds` (the corrected rung, `C + exp x`) |
| `ExpExpGapBelow` | **discharged** | `expExpGapBelow_holds` |
| `BoundedCellApproach` | **discharged** | `boundedCellApproach_holds` |
| `BoundedEmlCellApproach` | **discharged** | `boundedEmlCellApproach_holds` |
| `BoundedEmlCellApproachLarge` | **discharged** | `boundedEmlCellApproachLarge_holds` (the router) |
| `TowerReducesToSign` | **open** | — equivalent to `TowerLowerBound` ever since `signHardCase_holds` discharged its antecedent (`towerReducesToSign_iff_towerLowerBound`, `EMLTowerAfterSign`) |
| `NegativeTranslationGrowingLeft` | **discharged** | `negativeTranslationGrowingLeft_holds` (`EMLNegTranslation`), through `PinnedRightChild`; non-vacuity shipped as `growingLeft_growth_hypothesis_satisfiable` |
| `PinnedRightChild` | **discharged** | `pinnedRightChild_holds` — the band pins `A₁` to `u ± 1` and the five depth-≤1 forms are exhausted; the two that reach `exp x` die on the `−x` term |
| `FQueryLowerBound` | **discharged** | `fQueryLowerBound_holds` (`EMLRationalGerm`) |
| `OneQueryDichotomy` | **discharged** | `oneQueryDichotomy_holds` (`EMLCtxDivClamp`) — via `divClamp`, which supplies the two div side conditions the obligation omits; rests on `bipolyNoOscillation_holds` and the totalised `a / 0 = 0` |
| `BoundedGermTranscendence` | **open** | — (typed; both unbounded rates are theorems, constant `S` is a counterexample) |
| `LogQueryLowerBound` | **discharged** | `logQueryLowerBound_holds` (`EMLLogNotRational`) |
| `FQueryLowerBoundDivFree` | **discharged** | `fQueryLowerBoundDivFree_holds` |
| `RatGermTrichotomy` | **discharged** | `ratGermTrichotomy_holds` (`PevLeading`) |
| `OneQueryLevelSet` | **open** | — (the level-1 analogue of `zero_query_level_set`; `q_F(sign) ≥ 2` reduces to it, NOT to `OneQueryDichotomy`) |

Checked by grepping for theorems whose *conclusion* is each proposition, not merely mentions —
the first attempt returned consumers rather than dischargers, which is exactly the error the ledger
exists to prevent. That check is now the CI gate `tools/check_obligations.sh`: a row marked open with
a theorem concluding it is stale, a row marked discharged whose citation does not conclude it is
broken, and an unparseable table exits 2 rather than passing. Two convict specimens must fire and a
correct row must stay silent, so the gate cannot be satisfied by a checker that simply fails
everything.

The fifth row is a correction. This section previously said `TowerLowerBound` "reduces to"
`SignHardCase`; no such theorem exists, and the gap is real — sign-definiteness supplies the *ray* on
which a decay bound can be stated, not the *rate* it consumes. The implication is now the named Prop
`TowerReducesToSign` rather than a sentence that could firm up into an assumption unnoticed.

### `BoundedCellApproach` narrowed to what its consumer actually needs

The Prop quantified over all `P`, making it strictly stronger than
`depth_three_decayExp_bounded_left_of_gap` requires — and a stronger obligation is harder to discharge
for no benefit. It now carries the boundedness hypothesis the consumer already holds, so passing it
through costs nothing and narrows what must be proved to the bounded regime, the only one where the
statement is delicate.

The two regimes it sheds are not hard: for a growing `P` the target `exp(exp(P x))` is *triply*
exponential against a `Q` that `U₂` caps at *doubly* exponential; for `P = var` it is
`ExpExpGapBelow`, now a theorem. Neither was ever the obstacle, and carrying them in the statement
only obscured where the difficulty is.

### `ExpExpGapBelow` is proved — the `P = var` cell holds unconditionally

`expExpGapBelow_holds`, pure assembly: every branch was already a lemma. `const` and `var` clear `1`
via `exp(exp x) ≥ exp x ≥ x + x`; `A = α` and `A = c − log x` go through `expexp_gap_of_bounded`;
`A = x` and `A = exp x − log x` are one convexity step each against the constant floor `Cl ≤ log(B x)`;
and the three `A = exp x − d` sub-cases are `exp_shift_pos_gap`, `depth_le_one_log_gap_pos` and
`exp_shift_neg_exceeds`.

`depth_three_decayExp_var_left` follows immediately, so **three of `Depth3DecayExp`'s four cells now
hold outright** and only bounded-`P` remains, itself reduced to `BoundedCellApproach`.

**The obligations gate caught this.** Proving `ExpExpGapBelow` left its ledger row saying *open*, and
the gate went red with `STALE ExpExpGapBelow: marked open but discharged by expExpGapBelow_holds` —
the exact failure mode it was built for, on a row added four commits earlier. That is the first time
it has fired on real drift rather than on a convict specimen.

### The bounded-left-child branches too, in one lemma

`expexp_gap_of_bounded`: if `exp(A x)` is capped by a constant then the gap to `exp(exp x)` clears
`1`, because `exp(exp x) ≥ exp x ≥ x` grows past any constant while `log(B x)` has a constant floor.
Covers `A = α` and `A = c − log x` at once — the two forms whose exponential is bounded — and never
inspects `B` beyond its depth.

`ExpExpGapBelow` is now down to `A = x`, `A = exp x − log x`, the two trivial top-level constructors,
and the glue. Its crux and all three delicate branches are proved.

### Both `exp x − d` branches of `ExpExpGapBelow` are done

`exp_shift_pos_gap` handles `d > 0` by the same three moves as the `d < 0` case: convexity, then
`d = exp(log d)` to flatten `d · exp(exp x − d)` into `exp(log d + (exp x − d))`, then `self_le_exp`
to make it linear. With `exp x ≥ x + x` and the constant floor `Cl ≤ log(B x)`, the gap is linear in
`x` from below and clears `1` on an explicit ray.

The same three moves prove a **bound** here and a **vacuity** there. That is the useful shape: the
awkward object in both branches is `d · exp(exp x − d)`, doubly exponential and un-dividable, and in
neither case is it ever bounded above — only shown to dominate its own logarithm.

### `ExpExpGapBelow`'s `d < 0` branch is vacuous, not hard

`exp_shift_neg_exceeds`. If the left child is `exp x − d` with `d < 0`, the depth-2 tree's value
already *exceeds* `exp(exp x)`, so it cannot approach from below and the hypothesis is false on a ray.

The proof is where the division-free move earns its place. Convexity gives
`exp(exp x − d) − exp(exp x) ≥ (−d)·exp(exp x)`, and this base cannot divide by `−d` to make that
usable. Writing **`−d = exp(log(−d))`** turns the product into `exp(log(−d) + exp x)`, which
`self_le_exp` bounds below by `log(−d) + exp x` — *linear*, so it compares directly against the linear
ceiling `log(B x) ≤ x + D` and the ray comes out explicitly as `x ≥ D − log(−d)`.

A doubly exponential quantity handled without ever bounding it above: the only fact used is that it
dominates its own logarithm.

### The crux of `ExpExpGapBelow`: a positive depth-≤1 logarithm has a constant floor

`depth_le_one_log_gap_pos`. The grammar cannot produce arbitrarily small *positive* logarithms at
depth ≤ 1: `log β` is an exact constant (and if it is not positive the hypothesis is false); `log x`
and the two `exp x − …` forms diverge; and `c − log x` goes non-positive, so `Log` totalises to `0`
and the hypothesis fails again.

**This is the delicate cell of `ExpExpGapBelow`.** When a depth-2 tree's left child is exactly
`exp x` — the `d = 0` case, and the one that produced the counterexample refuting the previous rung —
the gap to `exp(exp x)` is *precisely* `Log(B x)`. So whether `exp(exp x)` can be approached from
below with a shrinking gap comes down to this lemma, and the answer is a constant floor.

Same asymmetry as `depth_le_one_gap_below`, same cause: nothing in this grammar decays to `0` from
above at depth ≤ 1 except via a shape that crosses into the totalised branch, and crossing makes the
hypothesis false rather than the bound tight.

### The decomposition of `Depth3DecayExp` is complete: two proved, two reduced

`BoundedCellApproach` and `depth_three_decayExp_bounded_left_of_gap` close the last cell, so the
obligation now stands as: growing cell **proved**, `const` cell **proved**, `P = var` and
bounded-`P` each **reduced to one named value-level statement**.

**The two reductions do not unify, and the reason is quantitative rather than incidental.** Both
convert a value gap into an exponent gap by reverse convexity, and the conversion costs a factor
`exp(−exp(P x))`. When `P` is bounded that factor is bounded below by a constant, so a value gap as
weak as `exp(−C − exp x)` suffices. When `P = var` the factor is `exp(−exp x)`, and that same weak gap
would yield `exp(−C − 2·exp x)`, missing the rung — so that cell needs a **constant** value gap, which
is exactly what `ExpExpGapBelow` demands and `BoundedCellApproach` does not.

Same reduction, two strengths, because the conversion factor differs. Reading the two Props side by
side is the cheapest way to see where the difficulty in this obligation actually lives.

### The `P = var` cell reduces to one statement about approaching `exp(exp x)`

`ExpExpGapBelow` — a depth-≤2 value cannot approach `exp(exp x)` from below with a shrinking gap —
and `depth_three_decayExp_var_left_of_gap`, which derives the cell from it.

The target **moves with `x`**, which is why `depth_le_two_gap_below` does not apply and this needed
naming rather than reusing. Reverse convexity turns a value-level gap into an exponent-level one
losing only the factor `exp(exp x)`, so a constant floor `ε` gives `node ≥ ε·exp(−exp x)`, which is
`exp(−C − exp x)` for `C = −log ε`.

**The corrected rung is what makes this work.** The same argument against `C + x` would require
`ε·exp(−exp x) ≥ exp(−C − x)`, which is false. The rung and the `exp(exp x)` target are one
phenomenon seen from two sides — which is the clearest statement yet of why the refuted version was
refuted.

The enumeration behind `ExpExpGapBelow` is routine and its collapse is sharp: writing `Q = exp a − Log b`,
only `a = exp x − d` with `d = 0` is delicate. `d > 0` scales `Q` down by `exp(−d)` and opens a gap of
order `exp(exp x)`; `d < 0` pushes `Q` above `exp(exp x)` so the hypothesis fails; `a = exp x − log x`
divides by `x`, again an enormous gap; every other `a` leaves `Q` far below. At `d = 0` the gap is
exactly `Log(b x)` — a positive constant, or growing, or zero, and zero makes the node vanish.

### Two cells carry over to the corrected rung, as theorems rather than a remark

`depth_three_decayExp_growing_left` and `depth_three_decayExp_const_left`. Since `x ≤ exp x`, every
`C + x` bound is a `C + exp x` bound, so both cells discharged against the refuted `Depth3DecayHard`
transport to `Depth3DecayExp` unchanged.

Worth stating as theorems rather than as the remark it had been twice: **a refutation invalidates a
conjecture, not the lemmas proved on the way to it.** Those cells were proved with the *stronger*
`C + x` bound, so refuting the conjunction cost nothing on them. Two of `Depth3DecayExp`'s four cells
therefore already hold, and only `P = var` and both-children-bounded remain.

### `Depth3DecayHard` is FALSE — the decomposition found its own obligation's counterexample

Take `A = var` and `B = dep3CounterRight = eml (eml var (const 0)) var`, both inside the depth
bounds, with `B x = exp(exp x) − log x`. The totalisation builds `B`: `log 0 = 0`, so
`eml var (const 0)` is exactly `exp x`, and one more node raises it to `exp(exp x)`. Then

```
node = exp x − log(exp(exp x) − log x) = −log(1 − log x / exp(exp x)) ≈ log x · exp(−exp x)
```

which is **positive** — so both hypotheses hold — and **super-exponentially small**, giving
`−log node ≈ exp x − log log x`. The excess `−log node − x` runs
`5.8, 17.0, 50.3, 142.9, 396.8, 1089.0, 2972.2` at `x = 2 … 8`, matching `exp x − log log x` to every
digit computed. No constant `C` can satisfy `−log node ≤ C + x`.

**The rung was wrong, not the idea.** `V₂` reads `C + log x`; reading the progression `log x → x` off
two levels gave `C + x`, but each level costs a whole exponential, so depth 3 needs `C + exp x`. The
corrected statement is `Depth3DecayExp`.

Nothing already proved is affected: `depth_three_decay_growing_left` and
`depth_three_decay_const_left` establish the *stronger* `C + x` bound on their own cells and remain
true. What the refutation kills is the *conjunction* over all four cells.

The four-cell decomposition was built to locate the difficulty, and the cell it isolated as hardest —
`P = var`, the sole occupant of the single-exponential rung — is exactly where the statement fails.
**`not_depth3DecayHard` proves it.** The estimate is elementary: with `ε = exp(−(C+1) − x)`, the node
is at most `ε` once `exp(exp x − ε) ≤ exp(exp x) − log x`, and convexity gives
`exp(exp x) − exp(exp x − ε) ≥ ε·exp(exp x − 1) = exp(exp x − 1 − (C+1) − x)`, which clears
`x ≥ log x` as soon as `two_mul_add_le_exp` fires. So `−log node ≥ C + 1 + x`, contradicting the
promised `≤ C + x`. No numerics enter the proof; the table above is corroboration, not evidence.

The obligations ledger grows a third status, `refuted`, with a **stronger** check than `open`: a
theorem concluding the proposition is a contradiction (CONTRA), *and* the row must be backed by a
theorem concluding its negation (UNBACKED otherwise). Without that second half, "refuted" would be
an assertion with extra confidence — the exact failure the ledger exists to prevent. Two new convict
specimens cover both halves; six fire, one stays silent.

### The `P = const` cell discharged — two of four

`depth_le_two_gap_below` lifts the from-below gap to depth 2 with the same constant `ε`, by the usual
collapse: a growing left child puts the node above `k` with **no enumeration of the right child**,
and when it is bounded the right child's five forms split three-and-two — three divergent logs drag
the node to `−∞`, two with an eventually exact constant log reduce to `depth_le_one_exp_gap_below`.
Every cell is vacuous, clears `1`, or inherits a constant. Nothing is tight.

`depth_three_decay_const_left` then discharges the cell. With a constant left child the node is
`exp c − log(Q x)`, so the question is whether `log(Q x)` can creep up on `exp c` from below faster
than exponentially. It cannot, and the reason is that **nothing in sight is exponentially small**:
`Q x` stays a *constant* below `exp(exp c)`, and `exp_sub_exp_upper` carries that value gap down to
the logarithm losing only a constant factor. The node is bounded below by `ε · exp(−exp c)` — a
positive constant, far stronger than the `exp(−C − x)` the obligation asks for.

Had the gap been `exp(−C − x)` instead, the convexity step would have yielded `exp(−C′ − 2x)` and the
bound would degrade by a factor of `x` per level. That is why `depth_le_one_gap_below`'s conclusion is
a constant and was not weakened to match its from-above mirror.

`Depth3DecayHard` is **not** discharged: two of four cells, unassembled. `P = var` and both-children-
bounded remain, and they are the two that were always hard.

### The `exp`-level from-below gap, and the toolkit for the `P = const` cell

`depth_le_one_exp_gap_below` carries the asymmetry up one exponential: `exp(A x)` cannot approach a
constant `ν` from below with a shrinking gap either, and again the gap is a **positive constant**.
`exp α` is exact; `exp(c − log x)` tends to `0` so the gap tends to `ν`; `exp x`, `exp(exp x − d)`
and `exp(exp x − log x)` all outrun `ν`; and `ν ≤ 0` makes the hypothesis false outright since `exp`
is positive.

The `c − log x` cell is the only one needing care, and the care is in choosing the target. The ray is
set so `exp(c − log x) ≤ exp(log ν − 1)`, which is *strictly* below `ν`, making `ν − exp(log ν − 1)` a
legitimate positive `ε`. The reflex choice `ν/2` would have needed division, which this base does not
have — the log-shift is the division-free substitute and is worth remembering as an idiom.

`exp_sub_exp_upper` (`exp u − exp v ≤ (u − v)·exp u`) completes the pair with `exp_sub_exp_lower`.
The lower form carries an **exponent** gap up to a value; this one carries a **value** gap back down
to the exponent, losing only a constant factor. That is precisely what the `P = const` cell needs:
`μ − log(Q x) ≥ exp(−μ) · (exp μ − Q x)`, so a constant value-gap gives a constant log-gap.

### Approach from below is strictly easier, and the asymmetry is structural

`depth_le_one_gap_below`: where `depth_le_one_approach_constant` bounds the gap below by
`exp(−C − x)`, approaching a constant **from below** leaves a gap bounded by a **positive constant**.
Not a symmetric statement — a strictly stronger one.

One cause. The only decaying shape at this depth is `exp(c − log x) = e^c/x`, and it is **positive**,
so it can push a value *above* its limit but can never let one creep up on a constant from
underneath. Of the five forms, `α` gives an exact constant gap, `c − log x` gives a gap that *grows*,
and `x`, `exp x − d`, `exp x − log x` all eventually exceed `k` so the hypothesis is false.

This is what makes the `P = const` cell of the depth-3 decomposition tractable: a constant gap
survives multiplication by `exp(A x) ≥ exp(−C − x)` without the `x` in the exponent doubling, which
is exactly what an `exp(−C − x)`-sized gap would not do.

### The growing cell of the depth-3 decay obligation: an exponential of headroom

`depth_three_growing_left_node_ge_one` / `depth_three_decay_growing_left`. If the depth-3 node's left
child grows — `P x ≥ exp x − x − C`, which by `depth_two_eml_value_gap` is the only alternative to
being bounded above — then `exp(P x)` is *doubly* exponential while `depth_le_two_log_le_exp` caps
`log(Q x)` at `exp x + K`, only *singly* exponential. The node does not merely stay positive, it
passes `1`, so `−log(node) ≤ 0 + x` outright.

**No cancellation is available in this cell, and the right child is never inspected beyond its
depth.** This branch had been counted with the hard ones on the grounds that both terms sit "at the
exponential scale" — they do not, they are a whole exponential apart. What stays genuinely hard is
the left child being `var` (`exp x` exactly: the single-exponential rung, which the value gap shows
no `eml` node can occupy) or both children bounded.

`Depth3DecayHard` remains **open** — this discharges one of four cells and does not assemble them.

### Approach-rate quantisation at depth ≤ 2

`depth_le_two_approach_constant` lifts the depth-≤1 statement one level: **no depth-≤2 expression
approaches a constant from above faster than exponentially** either.

The proof is not twenty-five cells, and how it collapses is the interesting part. The left child
splits once, on `depth_le_one_exp_bounded_or_grows`, and the halves are answered by different
machinery. When it grows, `exp x ≤ exp(A x)` while the right child's log is capped linearly, so the
node clears `exp x − x − D ≥ x − D` — **the right child is never enumerated on that branch at all**.
When it is bounded, the right child decides, and its five forms split three-and-two: for `x`,
`exp x − d` and `exp x − log x` the log diverges past `K − k` and the hypothesis `k < node` becomes
false, so those cells are *vacuous rather than hard*; the remaining two have an eventually-exact
constant log, so the node is `exp(A x)` against a shifted target.

The totalisation earns its keep in the `c − log x` cell: the log there is not merely small, it is
identically `0` on a ray via `log_nonpos`, so the node is *exactly* `exp(A x)` rather than a
perturbation of it. Third time the convention that is a hazard elsewhere has removed work.

Supporting: `exp_sub_exp_lower` (`exp u − exp v ≥ (u−v)·exp v`, from `one_add_le_exp` and `exp_add`)
is the bridge that carries an exponent gap through exponentiation, with the factor `μ` absorbed into
the constant as `μ · exp(−C−x) = exp(−(C − log μ) − x)` rather than lost.

### Approach-rate quantisation at depth ≤ 1

`depth_le_one_approach_constant`: for every constant `k`, a depth-≤1 expression **cannot approach a
constant from above faster than exponentially** — on a ray, `k < A(x)` forces
`A(x) − k ≥ exp(−C − x)`.

Sharp for a structural reason worth stating: the only decaying shape at this depth is `c − log x`,
and it decays *downwards through* every constant rather than approaching one from above, so it makes
the hypothesis false rather than the bound tight. Breaking the statement would need `exp(−x)`, whose
exponent `−x` is not among the five depth-≤1 forms.

This is the base case of the analysis that re-scopes `Depth3DecayHard`. Via convexity
(`exp u − exp v ≥ (u − v) · exp v`) a bound of this shape on an exponent converts a decay obligation
into a question the classification can answer, which settles that obligation's convergent regime on
paper and leaves only its divergent one. The docstring on `Depth3DecayHard` previously said no
classification of depth-2 expressions existed; `depth_le_two_normal_form` is one, added after the
obligation was named — a stale *under*claim, the variety no gate looks for, since gates are built to
catch prose that outran the corpus rather than prose the corpus overtook.

**Two of the three open ones are cancellation statements**: `SignHardCase` about the sign of
`exp a − log b`, `Depth3DecayHard` about how small it can be. `TowerLowerBound` reduces to the first.
The open problems are one phenomenon met from three directions.

**The limit worth stating.** "Discharged" is machine-checkable — a theorem concludes the proposition
and the claim auditor pins it. **"Open" is not.** Absence of a proof is not a theorem, so that column
is maintained by hand and can rot: if someone discharges an obligation and forgets the row, nothing
fails. That is the third structural gap in the claim architecture found this week, after prose citing
a theorem that did not exist and a missing attribution — all three being things the auditor cannot
see because they are not statements about a theorem's content.

### `V₃` easy branch — and a correction: the decay pattern is a conjecture, not a consequence

The previous commit suggested `V₁ ~ constant`, `V₂ ~ log x`, `V₃ ~ x`, each inherited from the floor
one level below. **That reasoning is valid only on the branch where the right child contributes
nothing**, and attempting the rest showed exactly where it stops.

`depth_le_three_decay_log_nonpos` is the branch that works: with `log (B x) ≤ 0` the node dominates
`exp (A x)`, and the new depth-2 floor `A x ≥ −C − x` gives a **linear** decay bound — one level
worse than `V₂`'s logarithmic one, as predicted.

**`Depth3DecayHard` is the branch that does not**, and it is named rather than assumed. At depth 2,
`V₂` closed because the right child ranges over *five closed forms* and every `log (B x) > 0` branch
was vacuous on a far enough ray. At depth 3 the right child ranges over depth-2 expressions, whose
logarithm can reach `exp x + K` — so `exp (A x) − log (B x)` may be small by **near-cancellation**
rather than by `A` being small, and no floor on `A` alone bounds it.

Worth being blunt: last commit's "the pattern **should** be" was hedged, and the hedge was doing
real work. The floor gives one branch; the other is the cancellation question again, arriving from a
third direction. This is now the fourth proposition in the corpus stated as a named obligation
(`TowerLowerBound`, `SignHardCase`, `VarLeftEmlRightHard`, this), and the second of those to be a
cancellation statement.

### The depth-2 lower envelope — and the answer to whether the type list is needed

`depth_le_two_lower_on_ray`: a depth-≤2 expression satisfies `t(x) ≥ −C − x` on a ray.

The depth-1 companion floors at `−C − log x`. One level of nesting degrades that from **logarithmic
to linear**, and no further, because an `eml` node is bounded below by `−Log(B x)` alone — `exp`
contributes nothing negative — and the depth-1 log ceiling is linear.

**This answers the question raised in the previous commit.** The 5 × 5 asymptotic type list is *not*
what `V₃` needs; the lower envelope is. Tracing the dependency: `V₂`'s bound `−log t ≤ C + log x`
comes from the depth-1 floor `−C − log x`, so the decay bound at depth `j` is governed by the lower
envelope at depth `j−1`, and the pattern should be

```
V₁ ~ constant     V₂ ~ log x     V₃ ~ x
```

one level apart, each inherited from the floor below it. That is a single theorem per level rather
than an enumeration, and it is why following the dependency was worth more than enumerating cells.

The classification programme at depth 2 is therefore, for present purposes, **complete**: sign
(`evSign_depth_le_two`), scale (`depth_two_eml_value_gap`), ceiling (`depth_le_two_log_le_exp`),
floor (this), and a function-level normal form. Whether a finer type list has independent value is
still open, but nothing currently blocked wants one.

### A function-level normal form at depth 2 — first step of the asymptotic classification

`Depth1Form` names the five closed forms as a predicate on **functions**, and
`depth_le_two_normal_form` says: a depth-≤2 expression is a constant, the identity, or
`exp a − log b` with both `a` and `b` in that list. **No tree appears in the third disjunct.**

Deliberately bookkeeping. The content is what it enables: `depth_le_one_classification` is stated
about a *tree*, and every consumer in this file immediately discards the tree, works with the five
forms, and re-derives the case split. After this, "depth ≤ 2" is a statement about functions, and a
depth-2 argument can split on `Depth1Form` per child without mentioning `EMLTree`.

**Where this is going.** The asymptotic classification wants the 5 × 5 cell list quotiented by
growth — roughly `bounded`, `−log x`, `−x`, `eˣ`, `e^{eˣ}` — as a *finite set of asymptotic types*
rather than 25 cases. Two axes of that quotient already exist as theorems (`evSign_depth_le_two` for
sign, `depth_two_eml_value_gap` for scale); this supplies the syntax they would be indexed by.
Whether the type list adds anything beyond those two axes is itself open — the axes were the reason
to want it.

### A candidate invariant beyond growth — and it separates the two functions

Every asymptotic axis in this corpus is blind to the difference between `x + 1` and `x²`: both
eventually positive, both unbounded, both sub-exponential, both above the identity, both outside the
`log x` hole. **Excess over the identity is not blind to it.**

`UnboundedExcess f` — `f x − x` unbounded above on every ray. Not a growth condition: it compares
`f` to `x` rather than placing `f` on a scale.

* `unboundedExcess_implies_above_identity` — it is **strictly stronger** than (H3).
* `x_add_one_not_unboundedExcess` — **`x + 1` fails it**, its excess being the constant `1`.
* `x_sq_unboundedExcess` — **`x²` satisfies it**, since `x·x − x = x·(x−1)`.

**So the depth-4 question is reopened rather than closed.** `band_exclusion_fails_at_depth_four`
refutes the depth-4 band *as stated*; it does **not** refute the band with (H3) strengthened to
`UnboundedExcess`, because the counterexample does not satisfy the strengthened hypothesis. Whether
that version holds at depth 4 is open, and `x²` and `M·x` are the targets it would settle.

This is the first hypothesis in the programme that is **algebraic rather than asymptotic** in
character, which is what the sharpness of the growth axes had been pointing at. It is a candidate,
not a result: nothing yet says the strengthened band is true.

### `d(x²) ≥ 4` is now actually a theorem

`x_sq_not_depth_le_three`. I have been quoting `4 ≤ d(x²) ≤ 8` for several commits on the strength of
the general depth-3 band, but the band had **never been instantiated at `x²`** — the only standalone
fact was `x_sq_not_depth_le_two`, giving `≥ 3`. Instantiating requires discharging all four band
hypotheses for that target, which is where the work is:

* **unbounded** — `K < x ≤ x·x` once `x ≥ 1`;
* **sub-exponential** — `exp_beats_powNat` at `k = 0`, with `powNat x 2 = x·x`;
* **superlinear** — `x < x·x` once `x > 1`;
* **superlogarithmic** — `C + log x < x + log x ≤ x + x ≤ x·x`, using `log x ≤ x` and `2 ≤ x`.

The bracket `4 ≤ d(x²) ≤ 8` (upper bound on `(1,∞)`) is now backed by named theorems at both ends.

**This is the failure mode the claim auditor exists for, and it slipped past** — the auditor binds
prose to a *named theorem*, and every claim I registered pointed at a theorem that was true. The gap
was that the number in my prose was a consequence I had derived in my head and never written down.
Registered claims catch prose drifting from a theorem; they do not catch prose citing a theorem that
does not yet exist.

### Depth of a semantic *class* — the first expressive phase transition, located exactly

Suggested in review, and it turns out the pieces were already there. Instead of asking for `d(f)` of
individual functions, ask for the least depth at which a previously unrealisable behaviour becomes
available.

`BelowIdentityUnbounded f` — unbounded above, yet eventually **strictly** below the identity.
`log x` is the canonical member; `x` itself is excluded, and that exclusion is what makes the class
non-trivial.

* `belowIdentityUnbounded_not_depth_le_two` — **no expression of depth ≤ 2 lies in the class.**
* `belowIdentityUnbounded_at_depth_three` — **`log x` does, at depth 3.**

> **The least depth realising unbounded-yet-below-the-identity behaviour is exactly 3.**

This is a better statement than the two sharpness results it packages, because it is about a class
rather than a witness, and it is the form a hierarchy would be stated in. The `eml`-only caveat that
made `depth_two_eml_value_gap` awkward disappears here: `var` is excluded by the class definition
rather than by a side condition, since `x` is not *strictly* below the identity.

Two transitions are now located:

| depth | what becomes realisable | witness |
| --- | --- | --- |
| 3 | a new *growth scale* — unbounded but below the identity | `log x` |
| 4 | new *algebraic* behaviour inside an existing band | `x + 1` vs `x²` |

The second is not yet a theorem of this shape — that is exactly §6.3, and stating it would require
the invariant that separates `x + 1` from `x²`, which no scale-based axis in the corpus can see.

### Depth 3 is exactly where an intermediate scale appears

`exp_gap_fails_at_depth_three` completes the sharpness table. `exp(log x) = x` is neither bounded nor
eventually `≥ exp x` — it lies **between** the two classes the exponential gap declares exhaustive —
and `log x` sits at depth 3.

So both depth-2 dichotomies are broken by the **same object for the same reason**:

| statement | holds | fails | witness |
| --- | --- | --- | --- |
| exponential gap | depth ≤ 2 | depth 3 | `log x` |
| value gap | depth ≤ 2 | depth 3 | `log x` |
| band exclusion | depth ≤ 3 | depth 4 | `x + 1` |

Each dichotomy says *bounded, or exponential, nothing between*. **Depth 3 is precisely where the
grammar acquires an intermediate scale**, and that single fact accounts for both failures. It is a
cleaner statement than either sharpness result alone, and it was not visible until both witnesses
turned out to be the same function.

The band exclusion then survives one level further because its hypotheses were built to legislate
around exactly this: (H3) excludes the `log x` hole, and it is `x + 1` — a *different* shape, barely
above the identity rather than below it — that finally defeats it.

### The value gap is sharp at depth 2 — `log x` breaks it at depth 3, and that explains (H3)

`value_gap_fails_at_depth_three`. `log x` is computed by `logTree var` at depth **exactly 3**, is
**not** bounded above, and is **not** eventually `≥ exp x − x − C` for any `C`. So the dichotomy of
`depth_two_eml_value_gap` holds at depth 2 and fails at depth 3.

**This explains the band's third hypothesis, which had looked like an artifact.** If the value gap
survived to depth 3, the depth-3 band exclusion would follow from it in one line. It does not, and
the hole that opens is exactly `log x`-shaped: unbounded and sub-exponential, but never above the
identity. **(H3) exists to exclude precisely that hole** — which is why the depth-3 exclusion needed
its own apparatus rather than a dichotomy, and why (H3) was necessary rather than convenient.

Three sharpness results now bracket the theory, each with an explicit witness:

| statement | holds | fails | witness |
| --- | --- | --- | --- |
| value gap | depth ≤ 2 | depth 3 | `log x` |
| band exclusion | depth ≤ 3 | depth 4 | `x + 1` |
| exp gap | depth ≤ 2 | — | (no counterexample known) |

The first two failures are the two shapes the band hypotheses have to legislate around, and they are
different shapes: `log x` is below the identity, `x + 1` is barely above it.

### The value gap at depth 2 — the band exclusion, read positively

`depth_two_eml_value_gap`: a depth-2 `eml` node is either **bounded above** on a ray, or eventually
**at least `exp x − x − C`**. Nothing in between; in particular no such node is polynomially large.

This is the value-level analogue of `depth_le_one_exp_bounded_or_grows`, which speaks about
`exp (A x)` rather than about the node. It is the same content as the depth-2 band exclusion, stated
as a **structural fact about which values the grammar can take** rather than as a refutation — and in
that form it composes, which the refutation does not.

**`var` is a genuine exception**, which is why the statement is about `eml` nodes: `x` is neither
bounded above nor eventually `≥ exp x − x − C`, and it sits at depth 0. That exception is exactly the
one the band's third hypothesis exists to exclude, and exactly the reason `x + 1` refutes the depth-4
version.

Together with `evSign_depth_le_two` this is the second piece of a depth-2 classification: cells
classified by **sign**, then by **scale**.

### Eventual sign-definiteness at depth 2 — unconditional

`evSign_depth_le_two`: **every depth-≤2 expression is eventually of constant sign.** No hypotheses,
no import.

`evSign_of_hard` had reduced sign-definiteness at every depth to one proposition. At depth ≤ 2 that
proposition is not needed: the exp gap splits the left child, and in the bounded branch the
depth-1 classification of the right child decides the sign in five cases — `const β` (constant node,
or `exp(A x) → 0` against `−log β`), `var` and the two exponential shapes (log outgrows the bounded
left child, node eventually negative), and `c′ − log x` (totalised to `0`, node is `exp(A x) > 0`).
In the growing branch the node clears `x` outright.

**This is also a check on the o-minimality reading of §6.1 of the report.** If every term of this
grammar is `ℝ_exp`-definable then *all* terms are eventually sign-definite, so a depth-2
counterexample would have refuted that reading outright. There is none, and the shape of the proof —
every case resolving to a definite scale — is what the definability argument predicts.

It is one instance, not evidence of the general statement. The value is that it is *unconditional*:
the first sign-definiteness result in the corpus that assumes nothing.

### The depth-3 band exclusion is **sharp** — and the "two obstacles" were chasing a false statement

`band_exclusion_fails_at_depth_four`. **`f x = x + 1` satisfies all three band hypotheses and is
computed at depth exactly 4** (`x_plus_one_in_eml`, already in the corpus). So

```
band exclusion:   depth ≤ 2  ✓      depth ≤ 3  ✓      depth ≤ 4  ✗
```

**This retracts the framing of the previous analysis, not any theorem.** Two apparent blockers to a
depth-4 version were identified — the bounded-left branch would need `V₃`, and the `A = var` branch
would need a classification of depth-2 trees. Both readings were correct about the *proof*; both were
irrelevant, because there is no true theorem to reach. I was measuring the difficulty of climbing a
wall with nothing on the other side.

`x + 1` slips through for a reason the hypotheses make plain in hindsight: they constrain **growth**,
and `x + 1` sits at the very bottom of the band — unbounded and above the identity by the smallest
possible margin. Nothing rules out a target that is barely superlinear.

**Consequences.**

* The growth front is **finished**, not stalled. Depth ≤ 3 is the whole theorem and it is optimal.
* `SignHardCase` does **not** gate the growth front after all — that claim, made one commit ago, was
  downstream of the false statement. It gates the tower's uniformity in `n` and nothing else here.
* The depth-2 classification is **not** needed for this, so it drops off the near-term slate.
* `d(x²) ≥ 4` stands, but sharpening it further cannot come from this route: any depth-4 exclusion
  must use a hypothesis that separates `x²` from `x + 1`, and all three band hypotheses fail to.

### **Depth-3 intermediate-growth exclusion** — the band lifts a level

`superlinear_subexp_not_depth_le_three`. Same three hypotheses as the depth-2 band, same arbitrary
`f` — no continuity, monotonicity, definability or formula:

> No `f` that is unbounded above, above the identity at arbitrarily large points, and below
> `exp x − x − C` at arbitrarily large points for every `C`, is computed by any EML tree of
> **depth ≤ 3**.

The scale table said the *floor/ceiling* architecture could not lift the band, and that was true.
This does not use it. Every branch is routed around it:

| branch | tool |
| --- | --- |
| `exp(A x)` bounded | `V₂` caps `B`'s decay |
| `A = const` | `exp x ≤ exp c` forces `x ≤ c` |
| `A = var` | `varLeftEmlRightHard_of_band` — five depth-1 shapes, one hypothesis each |
| `A = eml A' B'`, `A'` bounded-exp | node bounded by a constant, must exceed `x` |
| `A = eml A' B'`, `A'` grows | squeeze **at a point chosen from `H2`** |

The last row is where the correction landed. `depth_two_eml_not_near_identity` wants the squeeze on a
**ray**, and sub-exponentiality only supplies it **infinitely often**, so it cannot be called. The
argument is inlined at the chosen point instead — which is all it ever needed.

**Consequence: `d(x²) ≥ 4`**, and more usefully the exclusion is generic, so it applies to `M·x` and
every `xⁿ` at depth 3 exactly as at depth 2.

**This settles the value-exclusion question (VE) for band targets without the expert.** (VE) was
raised because the floor/ceiling stall looked like a cancellation problem; it was not one — going
around it needed only the depth-1 classification and the exp gap. `SignHardCase` is untouched and
still blocks the tower's uniformity in `n`.

Two arithmetic traps in the assembly, both caught by the build: the final contradiction needs a
**strict** gap, so `two_mul_add_le_exp` must be instantiated at `1 + D' + 1` rather than `1 + D'`;
and `K' − Cl' < x` needs the threshold's `+1`, since `self_le_exp` only gives `≤`.

### `VarLeftEmlRightHard` is discharged — the named obligation becomes a theorem

`varLeftEmlRightHard_of_band` proves it for every band target. `A''` ranges over the five depth-1
shapes and each is handled by exactly the tool the plan predicted:

| `A''` shape | route | refuted by |
| --- | --- | --- |
| `const α` | bounded exponential | (sub-exponentiality, via `varLeftEmlRight_bounded_left`) |
| `c − log x` | bounded exponential | (same) |
| `var` | pinned at `a = x` | **sub-exponentiality** |
| `exp x − d` | pinned at `a = exp x − d` | **unboundedness** |
| `exp x − log x` | pinned at `a = exp x − log x` | **superlogarithmicity** |

**The paper plan matched the formalisation exactly** — five shapes, one hypothesis each, no surprises
and no extra cases. That is the third time paper-before-Lean has paid on this arc, and the first time
the prediction was this detailed.

`log_exp_sub_pinned` is used three times, unchanged, with only the choice of `a` differing. The work
per case is entirely threshold bookkeeping: showing `x + D ≤ exp (a − 1)` and `−exp a ≤ Cl` on a ray.

**What this does and does not finish.** Every branch of the depth-3 exclusion is now proved:
bounded-left, the `eml`-left squeeze, and all of `A = var`. What is *not* yet written is the
**assembly** — a single `superlinear_subexp_not_depth_le_three`. Its one missing step is deriving the
squeeze hypotheses of `depth_two_eml_not_near_identity` from `depth_le_two_log_le_exp`, which the
theorem currently takes as inputs rather than deriving. So the pieces are all present and the capstone
is glue, not mathematics.

### `log (exp a − s)` pinned within `1` of `a`

`log_exp_sub_pinned`: if `s ≤ exp (a−1)` and `−exp a ≤ s`, then `a − 1 ≤ log (exp a − s) ≤ a + 1`.

The workhorse for the one surviving depth-3 branch, where it is applied three times with `a` taken as
`x`, `exp x − d` and `exp x − log x` — the three depth-1 shapes whose exponential is unbounded. Both
side conditions are one application of `exp_add_one_doubles`: `exp (a−1) + exp (a−1) ≤ exp a` gives
the floor, `exp a + exp a ≤ exp (a+1)` the ceiling.

Stated over bare reals rather than about trees, so the three uses instantiate it rather than repeat
it.

Corpus note, recorded once already and hit again the very next commit: **`.trans` does not exist on
this order.** There is no `MachLib.Real.leR.trans`; chain with `le_trans` or by hand.

### `VarLeftEmlRightHard`, bounded-left branch — closed

`varLeftEmlRight_bounded_left` takes the named obligation's easier half. If the surviving shape's own
left child has a bounded exponential, the node `eml A'' B''` is bounded above by `K − Cl`, so *its*
logarithm is bounded by a constant. But that logarithm must equal `exp x − f x`, which
sub-exponentiality forces above `x`, and a constant cannot dominate `x`.

Same move as `depth_three_bounded_left_not_superlog`, one level down. It needs **only
sub-exponentiality** — neither unboundedness nor superlogarithmicity appears, matching the pattern
where those two are reserved for the `exp x − d` and `exp x − log x` shapes.

`log_le_self_pos` fills a real gap: the corpus had `log t ≤ t` only on `[1,∞)`. Below `1` the log is
negative so the bound is free, but that case had never been written down, and the totalised branch
(`log t = 0` for `t ≤ 0`) needs it too.

**What remains of the depth-3 exclusion is now one branch of one proposition**: the surviving shape
where `A''`'s exponential *dominates* `exp x`. That is where the squeeze of the plan lives — pin
`A''` within `1` of `exp x − f x`, then five depth-1 shapes against one band hypothesis each.

### The `A = var` sub-case — two shapes discharged, one named

`var_left_not_band` handles the branch that survived the previous two theorems. With `A = var` the
equation collapses to `Log (⟦B⟧ x) = exp x − f x`, and `B`'s three shapes split cleanly:

* **`B = const c`** — `log c` is constant, so sub-exponentiality forces `x < log c + log c`, refuted
  by evaluating past `exp (log c + log c)`.
* **`B = var`** — forces `x + 1 < log x`, refuted by `log x ≤ x`.
* **`B = eml A'' B''`** — named as `VarLeftEmlRightHard`, not assumed away.

Both discharged shapes die against **sub-exponentiality alone**; neither needs unboundedness or
superlogarithmicity. That is a small piece of evidence about which hypothesis is doing what.

**The whole depth-3 exclusion for band targets now rests on one named proposition.** Its plan is
written (`monogate-research/exploration/eml_depth3_exclusion_2026_08_13/`): squeeze `A''` to within
`1` of `exp x − f x` using the depth-1 log bounds, then kill the five depth-1 shapes — three against
sub-exponentiality, `exp x − d` against unboundedness, `exp x − log x` against superlogarithmicity.

Structural note: this is the third proposition in the corpus stated as *named remaining obligation*
rather than proved (`TowerLowerBound`, `SignHardCase`, now this). All three are registered as claims
so that prose cannot quietly assume them.

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
