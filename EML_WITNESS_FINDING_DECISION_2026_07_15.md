# Decision draft: `eml_pfaffian_validon_from_sin_equality` — witness-finding options

**Date:** 2026-07-15
**Status:** DRAFT — options sketch, no decision made yet.
**Supersedes (partially):** `EMLPFAFFIAN_VALIDON_DECISION_2026_06_12.md`. That document's cost
estimate (weeks-to-month, needing a new `Smoothness`/connectivity module) is now obsolete — this
session took a completely different route and closed far more than it anticipated, at much lower
cost, with zero new axioms. What's left is narrower and better-characterized than either prior
document could have known.

## Context: what changed since June 12

The June 12 decision recommended shipping `eml_pfaffian_validon_from_sin_equality` as a named,
classically-true axiom, estimating a 300–500 line `Smoothness` module (smoothness preservation
under `+`/`-`/`·`/`∘`, a `Continuous_of_HasDerivAt` bridge, and a connectivity/IVT argument) as the
closure path — multi-session, not attempted at the time.

A single long session (this one) attacked the problem from a different angle — never building
`IsSmoothOn` or a general smoothness-preservation module at all. Instead: a local, structural
"no crossing" predicate (`EMLNoCrossingAt`, weaker than full validity, provable by ordinary
induction with no circularity) gives differentiability for free; a linear-ODE/integrating-factor
technique (`const_ratio_of_shared_ode` + `eml_ode_step_general`/`eml_E_step_general`) forces an
EML node's log-argument into an explicit closed form wherever positivity already holds; and a
minimal-violation-point argument (via the completeness axiom `sup_exists`/`inf_exists`, already in
MachLib) extends that closed form to the boundary, producing a contradiction if positivity ever
fails. A second, independent mechanism (value blow-up, exploiting `log`'s clamp discontinuity and
`|sin| ≤ 1`) covers a different but overlapping class of tree shapes.

Net result: **zero new axioms beyond one** (`HasDerivAt_congr`, a small local-invariance fact added
early on) and roughly 2200 new lines in `EMLSmoothness.lean`, closing far more of the axiom's
content than the June 12 estimate treated as in scope at all.

## What's actually proven now

| Class of tree shape | Status | Needs a witness? |
|---|---|---|
| Depth-1 (root `= eml t1 t2`, offender `= t2`) | Closed, any `b > 0` | Yes — but free (any zero of `sin`/`cos`) |
| Right-descent then arbitrary-length left-chain, optionally one more right turn at the root | Closed, any chain length (value-blow-up mechanism; round 5 proves this is that mechanism's ENTIRE reach) | Yes, supplied |
| Arbitrary-depth left-descent spine (ODE mechanism) | Closed, any spine length | Yes, one witness at the bottom |
| Arbitrary-depth pure right-descent chain (ODE mechanism) | Closed, any chain length | Yes, one witness per level |

All four rows: fully mechanized, zero new axioms, verified via `#print axioms` after every theorem.

## What remains: witness-finding

Every row above except depth-1 takes its witness(es) as a hypothesis rather than deriving them.
Depth-1's witness is free because ANY zero of `sin` (there are infinitely many) makes the defining
equation `exp(t1.eval x) − log(t2.eval x) = sin x` force `log(t2.eval x) = exp(t1.eval x) > 0`
unconditionally — no case split, no assumption on `t1`.

An investigation into whether this generalizes (attempting to prove a witness ALWAYS exists, for
ANY tree, from `t.eval = sin` alone) found a concrete obstruction: the natural inductive invariant
("the node's effective target dips non-positive somewhere") does not propagate through one step of
left-descent. Tracing the algebra: whether the next level down also gets a non-positive point
depends on the RANGE of the sibling subtree at that level — and nothing in `EMLTree`'s definition
constrains that range. A sibling subtree that stays bounded well above the needed threshold
everywhere defeats the propagation outright; this isn't a proof-technique weakness, it's a real
degree of freedom in what `EMLTree` allows.

## Three ways forward

### Option A — Restrict scope: prove witness-existence for a documented non-degeneracy condition

Add an explicit hypothesis to a new, narrower closure theorem — e.g. "every sibling subtree
encountered along the descent is unbounded above at some point" (or a similarly concrete,
per-subtree condition) — and prove witness-existence holds under it. Ship this as the operative
closure; leave fully unconstrained trees as a separately named, narrower residual axiom.

- **Pros:** directly targets the SPECIFIC failure mode found (bounded siblings defeat the
  invariant) — "require unboundedness" is the natural repair. Concrete and likely buildable at a
  similar scale to rounds 15–18 of this session (each landed in 1–2 rounds once the right
  abstraction was found).
- **Cons:** doesn't close the axiom as currently stated. The non-degeneracy condition needs
  checking against realistic use (trivial for `var`, needs verifying for compound subtrees) —
  possible it's still too strong or too weak once formalized.
- **Rough scale:** 1–3 more rounds, comparable to recent history.

### Option B — Continue researching the fully general case

Keep looking for an invariant or argument that survives arbitrary sibling behavior, with no
non-degeneracy hypothesis at all.

- **Pros:** if found, closes the axiom exactly as stated, no added conditions.
- **Cons:** this session already spent real, focused effort here and hit a concrete wall (not
  "didn't look hard enough" — found and verified a specific counter-scenario). No candidate next
  idea identified. Open-ended, no way to bound the effort in advance.

### Option C — Check whether the axiom is actually false as stated

Attempt to CONSTRUCT an explicit MachLib `EMLTree` (using real `const`/`var`/`eml` nodes, not an
abstract argument) where `t.eval = sin` holds globally and some offender genuinely has no witness
anywhere. This is a different kind of work than A/B — concrete construction and computation, not
proof search.

- **Pros:** either outcome is valuable. Success means the axiom needs an explicit side-condition —
  a significant, directly actionable finding (and would sharpen exactly what Option A's condition
  needs to rule out). Failure to construct one is useful negative evidence supporting A or B.
- **Cons:** building a genuine counterexample satisfying the GLOBAL equation `t.eval = sin` (not
  just "some point") is itself a nontrivial constraint most naive attempts won't satisfy — may
  turn out to be comparably hard to the original problem.
- **Rough scale:** worth a bounded, cheap check (a session, not a multi-round commitment) before
  committing further effort to A or B.

## Recommendation

Option A first, with a lightweight Option C gut-check alongside it (not instead of it). Reasoning:
round 18's mechanism-building is essentially complete and this session's failure mode (round 19)
is concrete rather than vague, which is exactly the situation where "restrict scope, ship the
restricted result, name the residual gap" (the same pattern the June 12 document already used
successfully for the axiom as a whole) is the right move. A quick attempt at Option C first is
cheap insurance — if a real counterexample turns up, it directly informs what Option A's
non-degeneracy condition needs to say, rather than guessing at one and discovering later it's
either too weak (doesn't actually enable the proof) or too strong (excludes trees that matter).

Option B is not recommended as the NEXT step — not because it's worthless, but because it has no
natural stopping point and this session already gave it a genuine, focused attempt.

## Update 2026-07-16 — Option A, first concrete point scored

Built `eml_depth2_witness_of_const_var` (`EMLSmoothness.lean`, commit `f29390ef`): if the depth-2
offender `S3` (in `t = eml T1 (eml S2 S3)`) were identically `≤ 0`, its log-branch collapses to the
constant `0`, and — via `log∘exp = id` unconditionally, the same asymmetry `eml_leftchild_explicit_value`
already exploits — the whole tree collapses to `exp(T1.eval x) − S2.eval x = sin x` for all `x`. For
`T1` globally constant and `S2` a leaf (constant or the identity), this is refutable by direct
evaluation at one or two points (`x = 0`, `x = π/2`). Result: a witness for `S3` with **no
hypothesis needed at all** — the first case where witness-finding is fully resolved beyond depth-1.
Compiled with zero errors on the first attempt; zero new axioms.

This does not touch compound `T1`/`S2` — those reopen the round-19 recursive difficulty exactly.
The natural next step under Option A is pushing the same "collapse + evaluate/differentiate"
technique to `T1`/`S2` being simple-but-not-leaf, to map out how far elementary reasoning reaches
before the recursion genuinely bites.

## Update 2026-07-16 (cont.) — the T1-constant restriction pinned down exactly

Checked whether `T1`-constant was load-bearing in BOTH of the previous update's branches, or just
one. It's only load-bearing for ONE narrow sub-case:

- `eml_depth2_witness_of_var_sibling`: `S2 = var`, `T1` COMPLETELY ARBITRARY. Evaluating at `x = 0`
  alone forces `exp(T1.eval 0) = 0` — impossible regardless of `T1`'s shape. No constant hypothesis
  needed at all.
- `eml_depth2_witness_of_const_le_one_sibling`: `S2` constant `c2 ≤ 1`, `T1` COMPLETELY ARBITRARY.
  Evaluating at `x = −π/2` forces `exp(T1.eval(−π/2)) = c2 − 1 ≤ 0` — impossible for any `T1`. For
  `c2 > 1` this specific point gives no contradiction (`c2 − 1` could be a genuine `exp` value) —
  this is EXACTLY round 19's failure mode, now localized to a single precise sub-case rather than
  a vague "compound siblings might defeat it."

Net effect: witness-finding for the whole depth-2/leaf-sibling family is closed EXCEPT for exactly
one sub-case — `S2` constant `> 1`, `T1` non-constant. Down from "`T1` must be constant, full
stop" at the start of the day. Both compiled clean (one needed swapping an unavailable `set`
tactic for the file's established `let`+`show` idiom); zero new axioms.

## Update 2026-07-16 (cont.) — both natural broadenings reopen the round-19 wall; a circularity trap identified

Traced (paper only, no code) whether the "collapse + evaluate" technique extends to deeper trees
(offender 3 levels down) or compound `S2` (`= eml P Q`). Both reopen the exact difficulty round 19
found — the collapse trick only telescopes ONE level (`log(exp(v)) = v` simplifies cleanly;
`log(exp(v) − w)` does not), confirmed by direct algebra, not assumption.

Also checked, and REJECTED, a tempting shortcut: `sin_not_in_eml_any_depth` (already a theorem
elsewhere in the codebase) cannot be used to argue "the axiom's hypothesis is vacuous, so it's
trivially true" — that theorem's OWN current proof (`EMLExplicitBoundSinBarrier.lean`) depends on
`eml_pfaffian_validon_from_sin_equality` itself. Using it here would be circular. Recorded so no
future attempt wastes time on it.

## Update 2026-07-16 (cont.) — Option C attempted: no counterexample, but a real generalization

Tried to construct an explicit compound `T1` making the residual `c2 > 1` gap genuine. Every
natural candidate failed for the same reason: compound `T1` choices tried were either secretly
constant (collapses to a fixed number, not a real test) or UNBOUNDED — and unboundedness alone
gives an immediate elementary contradiction, regardless of `T1`'s shape. Built
`eml_depth2_witness_of_const_sibling_unbounded_T1` (commit `475502bf`): if `T1` is unbounded above,
picking a point where `T1.eval x` exceeds `c2+2` forces `exp(T1.eval x)` past the range `sin`
allows, via `exp_grows_strictly_thm` alone — no Khovanskii machinery needed. Covers the ENTIRE
`c2 > 1` gap for compound OR non-compound unbounded `T1`. Zero new axioms.

Net effect: the residual gap is now precisely "`T1` BOUNDED and non-constant, `S2` constant `> 1`"
— narrower than "compound `T1`" was. No counterexample found (weak evidence the general claim may
hold for this shape), but the search itself produced real, reusable infrastructure.

## Update 2026-07-16 (cont.) — periodicity route checked and ruled out as a shortcut

Considered whether the last residual (`T1` bounded, non-constant, `S2` constant `> 1`) could close
via periodicity: the collapse equation forces `T1` to be `2π`-periodic (inherited from `sin`), and
a non-constant periodic function has infinitely many critical points — which looks like it should
contradict a "boundedly many critical points" fact for elementary/EML functions.

Checked the actual infrastructure (`AnalyticFiniteZerosReal.lean`) rather than assuming it would
work. `analytic_open_interval_bounded_zeros`'s zero-count bound is explicitly documented as
**non-uniform** in the interval — it can grow as the interval grows, so extending the periodicity
argument to `[0, 2Nπ]` for large `N` gives no contradiction. The uniform bound this route would
actually need IS the Khovanskii/Pfaffian-chain machinery itself — comparable in scale to the axiom
being closed, not a nearby shortcut. Ruled out; no code written (checking against source first
avoided a wasted build attempt).

## Update 2026-07-16 (cont.) — the mechanism side reached its own capstone; re-scoping this document

After the witness-finding investigation above, the session pivoted to generalizing the ODE
mechanism itself (rounds 25–27, `EMLSmoothness.lean`): first demonstrating it composes across
MIXED left/right descent paths (not just pure-left or pure-right), then generalizing that to
ANY length/shape mixed path (`eml_moves_pos_of_pos_witness`), and finally — the actual capstone —
`eml_pfaffian_validon_of_sin_and_witnesses`, which closes `EMLPfaffianValidOn t x0 b` in FULL
(every node, not one offender) for ANY tree shape, via structural induction on `EMLTree` itself.

**This changes the scope of this document.** It's no longer "how do we find witnesses for the
specific offender shapes closed so far" — the mechanism now handles every tree shape uniformly.
The witness-finding options above (A/B/C) apply UNCHANGED, just now understood to be the ENTIRE
remaining gap for the axiom in full generality, not one piece among several. The one other gap:
`eml_pfaffian_validon_of_witnesses` only reaches `[x0, b)` for `b > x0` (forward from the witness
point) — a backward-direction mirror (mirroring `eml_depth1_pos_of_pos_witness_backward` via
`sup_exists`) is needed to cover `b` smaller than the witness point, i.e. literally "any `b > 0`".
Not yet built; expected mechanical given the session's track record.

## Update 2026-07-16 (cont.) — backward mirror built; a genuine gluing subtlety found, not closed

Built the backward-direction mirror (`eml_pfaffian_validon_of_sin_and_witnesses_backward`,
line-for-line mirror of the forward capstone via `sup_exists`) — mechanical, as expected, one
small fix. Both directions are now independently complete.

Attempting the natural final step — one theorem covering `EMLPfaffianValidOn t 0 b` for ANY `b>0`
from a single witness point `p`, combining forward + backward — hit a genuine gap, not a quick
fix: `EMLPfaffianValidOn`'s definition is a fully OPEN interval `a<x<b`. The backward piece claims
`(0,p)`, the forward piece claims `(p,b)` — their union misses the single point `x=p`, even
though the UNDERLYING mechanisms individually reach `x=p` (their raw conclusions use `≤`, not `<`,
at the witness endpoint — it's packaging into `EMLPfaffianValidOn`'s fixed shape that loses it). A
real fix needs a THIRD combined structural induction, not gluing two packaged results together.
Documented honestly rather than patched with an incorrect proof; not yet built.

## Update 2026-07-16 (cont.) — the gluing gap CLOSED. Mechanism side is complete.

The fix was not a third combined induction gluing two packaged results — it was avoiding the
packaging problem entirely. Built `eml_ode_closure_general_twosided`: takes the witness at an
INTERIOR point `p` directly and covers the whole `(a,b)` via a case split on `x` vs `p` BEFORE any
`EMLPfaffianValidOn` packaging happens, so there's no open-interval endpoint left to lose. Ran the
same structural induction as the forward capstone with this as the base mechanism
(`eml_pfaffian_validon_of_witnesses_twosided`).

**`eml_pfaffian_validon_of_sin_and_witness_at_point`** is the result: given a SINGLE witness
structure `EMLWitnesses t p` at ONE point `p`, `EMLPfaffianValidOn t 0 b` holds for literally ANY
`b > 0` — the exact shape of `eml_pfaffian_validon_from_sin_equality` itself. One small fix
(missing explicit function arguments, a compiler-caught mechanical error). Zero new axioms.

**The mechanism-building side of this whole investigation is now complete.**
`eml_pfaffian_validon_from_sin_equality` reduces, for literally any tree and any `b>0`, to exactly
one hypothesis: `EMLWitnesses t p`. Nothing else stands between "nothing" and the full axiom.

## Status

- Mechanism-building (rounds 1–18, then 25–29 this session): COMPLETE — any tree shape, any
  `b > 0`, from one witness point, zero new axioms beyond `HasDerivAt_congr`. This is the
  endpoint of this line of attack; no further mechanism work is expected to be needed.
- Witness-finding (`EMLWitnesses t p`): the ONE remaining hypothesis, open in general. Depth-2/
  leaf-`S2` family closed except one maximally narrow residual: `T1` bounded and non-constant,
  `S2` constant `> 1`. Probed from three independent angles (direct evaluation,
  growth/unboundedness, periodicity) — all either close cleanly or require Khovanskii-scale
  machinery. This is a well-triangulated boundary, not an unexplored gap.
- Option A: exhausted for this tree shape at the elementary level — the remaining residual needs
  either genuinely new (Khovanskii-scale) machinery or acceptance as a named side-condition.
- Option B: not recommended (see original rationale above).
- Option C: attempted once, no counterexample found, produced a real generalization instead.
  Further attempts would need to target deeper/compound trees specifically, which reopens
  round-19-scale difficulty rather than being cheap.
- This document: living draft. The mechanism side is done; only the witness-finding options above
  remain open for whoever picks this up next.

## 2026-07-19 — brainstorm: Option D, strong induction on tree depth with the target generalized

Not attempted, not implemented — a candidate strategy, written down so it isn't lost, per this
document's own convention. Grounded by re-reading the actual source (`EMLSmoothness.lean`'s
`EMLWitnesses`/`eml_pfaffian_validon_of_witnesses`, `SinNotInEML.lean`'s `.eval`, and
`EMLExplicitBoundSinBarrier.lean`'s proof of `sin_not_in_eml_any_depth`) rather than reconstructed
from memory, per this project's own paper-before-Lean/measure-don't-guess discipline.

**The residual, made fully explicit.** For `t = eml T1 (eml S2 S3)` with `t.eval = sin` globally,
`S2` constant `c2 > 1`, `T1` bounded and non-constant: the witness-finding proof pattern used
elsewhere in this family assumes `S3 ≤ 0` everywhere (for contradiction) to collapse the
log-branch to the constant `0` (`Real.log`'s clamp), reducing the equation — via `log∘exp=id` —
to `exp(T1.eval x) − c2 = sin x`, i.e. `exp(T1.eval x) = c2 + sin x`. For `c2 ≤ 1` this is
refutable at `x=−π/2` (RHS `≤0`, LHS `>0`, contradiction for ANY `T1`). For `c2>1`, RHS is
`≥ c2−1 > 0` everywhere, so **no single-point evaluation can ever refute it** — worse, it's
*exactly solvable*: `T1.eval x = log(c2+sin x)` is a perfectly good real-analytic function
satisfying the collapsed equation pointwise. This is precisely why every elementary trick tried so
far (evaluation, growth, periodicity) stalls here: the collapsed equation isn't false, it's
*almost* true — true for T1's VALUES, just not (presumably) true for any actual finite EML TREE
shape.

**The reduction this unlocks.** The residual is exactly equivalent to: **does any finite-depth EML
tree `T1` satisfy `T1.eval x = log(c2+sin x)` for all real `x`?** If no (a generalization of
`sin_not_in_eml_any_depth` to this target), the collapse assumption is refuted, a witness for `S3`
exists, done. This is a much better-posed question than "T1 bounded, non-constant" — it names an
exact target function to rule out, not a vague shape.

**Why `sin_not_in_eml_any_depth` can't be reused as a black box (confirmed, not assumed, by
reading its proof in `EMLExplicitBoundSinBarrier.lean`):** its proof (a) builds a Khovanskii/
Pfaffian-chain zero-count bound `M` on `t` purely from `t`'s STRUCTURE (`combinedBoundE` — confirmed
via `EMLExplicitBoundEncoder.lean`'s own docstring: "no `(a,b)` dependence anywhere," i.e. already
generic in the target), (b) invokes `eml_pfaffian_validon_from_sin_equality` on `t` ITSELF to get
the positivity (`EMLPfaffianValidOn`) needed to make the Pfaffian chain well-behaved, then
(c) exhibits a concrete point (`sin(π+1)≠0` etc.) where `sin`'s own oscillation exceeds what `M`
allows. Step (b) is the exact axiom under investigation — using this theorem on `T1` would assume
the very thing being proven, for `T1` specifically. This is the circularity already flagged
earlier in this document; confirmed precisely, not just recalled.

**The way around it, and why it's genuinely different from the rejected shortcut:** don't reuse
the finished theorem — re-derive the WHOLE combined package (`EMLPfaffianValidOn` + Khovanskii
non-representability) by **strong induction on EML tree depth**, generalized over the target
function `g` (dropping the hardcoding to `sin`). This is not circular because:
- `eml_pfaffian_validon_of_witnesses` is ALREADY unconditional and generic in the derivative `D`
  (confirmed: its signature takes `D : Real → Real` and `HasDerivAt t.eval (D x) x` as a plain
  hypothesis, nothing sin-specific) — so step (b) above, for `T1` specifically, can come from the
  INDUCTIVE HYPOTHESIS (T1 has strictly smaller depth than `t`), not from the not-yet-proven axiom.
- `EMLWitnesses` itself is pure tree recursion with zero dependence on any target function
  (`.const _, _ => True`; `.var, _ => True`; `.eml t1 t2, x0 => EMLWitnesses t1 x0 ∧
  EMLWitnesses t2 x0 ∧ 0 < t2.eval x0`) — nothing here needs generalizing, it already applies
  to `T1`'s own recursive structure unchanged.
- `combinedBoundE`'s bound is already computed purely from tree shape, not from the target — so
  step (a) transfers to `T1` and `g=log(c2+sin x)` with no change needed.
- What WOULD need new work: step (c), an analogue of "`sin(π+1)≠0` exceeds the bound" for
  `log(c2+sin x)` specifically — concrete, computable (same period, structurally analogous
  oscillation to `sin`), not obviously harder in KIND, "just" new arithmetic through the same
  argument shape.

**Honest assessment.** This is a real, well-posed candidate — not a rehash of the already-rejected
periodicity route (that route needed a UNIFORM zero-count bound across growing intervals with no
tree-structural handle on it; this route gets a bound directly from `T1`'s own finite structure via
`combinedBoundE`, which is exactly what periodicity was missing). But it is genuinely multi-round
work if pursued: setting up a mutual/simultaneous strong induction proving two linked statements
(witness-existence AND target non-representability) for a class of targets broader than just `sin`
is a real generalization exercise, not a quick patch — likely comparable in scale to rounds 25–29
of the mechanism-building side, possibly larger since it touches the encoder/bound layer too, not
only `EMLSmoothness.lean`. Not started. Flagged here as Option D for whoever picks this up next,
alongside A/B/C above.

## 2026-07-19 (cont.) — Option D, step (c) worked out on paper: the target-shift trick

Picked back up per continued user request to keep pursuing this. Worked the exact mechanism for
the piece flagged above as "would need new work" — not implemented in Lean, but no longer just a
hope; checked against the actual definitions (`EMLExplicitBoundEncoder.lean`,
`EMLExplicitBoundSinBarrier.lean`, `MultiPoly.lean`), not assumed.

**The obstacle, restated precisely.** `sin_not_in_eml_any_depth`'s actual contradiction mechanism
(read the full proof, not just its opening) is: `sin(kπ)=0` for every integer `k`, giving `M+1`
distinct zeros of the tree's associated Pfaffian polynomial within an interval where
`combinedBoundE` only permits `M` — `M+1 ≤ M` via `omega`. This is elementary once you see it:
zero-counting against a computable bound, nothing deeper. The blocker for `T1.eval = log(c2+\sin x)`
looked like it wouldn't transfer: for `c2 ≥ 2`, `c2+\sin x ≥ c2-1 ≥ 1`, so `\log(c2+\sin x) ≥ 0`
with equality **only possibly at `c2=2`** (a tangency, not a transversal zero) — `\log(c2+\sin x)`
can have few or literally **zero** zeros, so "count the zeros" has nothing to count against for
large `c2`.

**The fix: don't target zero — target `\log(c2)`.** `\sin(k\pi)=0` for every integer `k`, so
`\log(c2+\sin(k\pi)) = \log(c2+0) = \log(c2)` **for every integer `k`, regardless of `c2`'s value**
— the exact same `k\pi`-spacing that drove the original proof, now hitting a shifted level `\log(c2)`
instead of `0`. This works uniformly for every `c2>1` (both the `c2≥2` "no zeros" case and the
`1<c2<2` "some zeros" case) — the argument never needs `\log(c2+\sin x)`'s own zero structure, only
its `=\log(c2)` level-set structure at the same `k\pi` points, which is identical in form to `sin`'s
own zero structure.

**Why this is mechanically valid, not just plausible — checked against the source:**
- `enc_combinedBound` (`EMLExplicitBoundEncoder.lean:233`) is stated for an **arbitrary**
  `p : MultiPoly (len t N)` — `sin_not_in_eml_any_depth` happens to instantiate it with
  `p := (enc t emlEmptyChain).2` (the polynomial representing `t.eval` itself), but nothing in the
  theorem's statement requires that specific choice.
- `MultiPoly` (`MultiPoly.lean:39-45`) has `const : Real → MultiPoly n` and
  `sub : MultiPoly n → MultiPoly n → MultiPoly n` as basic constructors, with
  `eval (sub p q) x env = eval p x env - eval q x env`. So
  `p' := MultiPoly.sub (enc T1 chain).2 (MultiPoly.const (Real.log c2))` is a well-typed
  `MultiPoly (len T1 N)` whose zeros are exactly the points where `T1.eval(x) = \log(c2)`.
  Instantiating `enc_combinedBound` with `p'` (applied to `T1`, not the outer tree) gives a bound
  on how many times `T1.eval` can equal `\log(c2)` — exactly the quantity needed.
- The non-degeneracy witness `hne` (needed by `enc_combinedBound`, `∃z, T1.eval z ≠ \log(c2)`) is
  now EASIER to supply than the original's `sin(\pi+1)\ne 0` (which needed a `sin\_add`/`cos\_pi`
  identity chain): `T1.eval(\pi/2) = \log(c2+1) \ne \log(c2)` is immediate from `c2+1\ne c2`, no
  trig identity needed at all.
- The rest of the argument (build the `M+1`-point list `\{k\pi\}`, show each is a solution via
  `\log(c2+\sin(k\pi))=\log(c2)`, invoke the bound, `omega`) mirrors
  `sin_not_in_eml_any_depth` lines 86–105 essentially unchanged, modulo the target shift.

**What this does NOT yet close — real remaining work, named precisely:**
- `T1`'s own `LogArgPosOn` (needed as a hypothesis by `enc_combinedBound` applied to `T1`) has to
  come from somewhere — this is exactly the role the INDUCTIVE HYPOTHESIS was supposed to play in
  the broader Option D strategy (strong induction on tree depth), not yet formally set up.
- `T1` needs its OWN Pfaffian chain/encoder (`enc T1 chain'` for some chain `chain'`, its own `M`
  from `combinedBoundE (len T1 N) ...`) — real plumbing, distinct from and in addition to the
  target-shift idea itself. The target-shift trick tells you WHAT to prove about `T1`; it doesn't
  build the chain object `T1` needs to prove it about itself.
- Not yet checked whether `Real.log`'s specific MachLib definition (total, clamped at `≤0`) needs
  any special handling in the shifted-target argument — `c2+\sin x>0` always for `c2>1`, so the
  clamp should never trigger, but this was reasoned, not verified against the source this pass.

**Honest assessment.** This is real progress — the piece flagged as "would need new work,
'just' new arithmetic through the same shape" turned out to have a clean, uniform resolution
(one trick, not case-split on `c2`), verified against the actual type signatures rather than
assumed. It does not close Option D — the induction scaffolding and `T1`'s own chain construction
are still unbuilt, and remain comparable in scale to what was estimated before. But the piece that
looked like it might need genuinely new mathematics (a `c2`-dependent case analysis, or a
different technique entirely for `c2\ge 2`'s zero-free case) turned out not to — same trick,
every `c2`. Not implemented in Lean this pass, per the paper-first discipline: the argument is
believed correct and checked against real definitions, not yet formalized.

## 2026-07-19 (cont.) — first piece of the induction actually built and verified in Lean

`MachLib/WitnessResidualDepth1.lean` (commit `1e4a0198`): proves `T1` cannot have depth ≤ 1.
Any `eml A B` with `A,B` both leaves is either globally constant or unbounded above, checked
for all four leaf combinations — so the residual's smallest possible `T1` has depth ≥ 2, never
depth 0 or 1. Verified via `#print axioms`: depends only on MachLib's own foundational axiom
base, **not** `eml_pfaffian_validon_from_sin_equality` — genuinely non-circular, zero new axioms.
This is a real base-case fact for the strong-induction-on-depth strategy above, not just a
brainstormed idea — compiled, checked, wired into the root `MachLib.lean`.

Does not close Option D — the depth ≥ 2 inductive step (needing the target-shift trick above
plus `T1`'s own chain construction) is still open. But the induction now has a genuine,
verified foothold at its base.

## 2026-07-19 (cont.) — attempted the depth-2 step; found a real obstruction, not a quick win

Attempted to push the depth-1 boundedness-propagation argument (above) one layer deeper: for
`T1 = eml A B` with `A` or `B` now COMPOUND, does boundedness of `T1` still force `A` and `B`
individually bounded, the way it did when they were leaves?

**No — and this section exhibits why, concretely, rather than leaving it as an abstract
worry.** `MachLib/WitnessResidualCancellation.lean` (commit pending): the depth-3 tree
`T1 := eml var (eml (eml var (const (exp K))) (const 1))` has `A = var` UNBOUNDED and its own
`B`-subtree (`exp(exp x − K)`) ALSO unbounded — yet `T1.eval x = K`, an exact CONSTANT, for
every real `x`. Verified both numerically (Python, exact to double precision at 8 test points)
and in Lean (`cancellation_theorem`, two applications of `log_exp` plus `mach_ring` — compiled
clean, `#print axioms` confirms non-circular, no dependence on the axiom under investigation).

**This is precisely round 19's original "bounded siblings defeat the invariant" obstruction,
now made fully explicit rather than asserted.** The depth-1 argument worked because a LEAF
`A` or `B` is simple enough that "exp(A) unbounded" and "log(B) unbounded" can't be shown to
cancel — there's no room for conspiracy in a single exp or log of a leaf. Once `A`, `B` can be
COMPOUND, EML trees can encode iterated exponentials precisely enough to cancel each other's
growth exactly (this specific witness needs only depth 3 to do it). So: **no boundedness-only
argument can close the depth-≥2 case in general** — cancellation is a real, constructible
phenomenon in this system, not a hypothetical gap in the proof technique.

**What this means for Option D, honestly:** the depth-≥2 inductive step cannot be closed by
generalizing the depth-1 style argument, no matter how much more casework is thrown at it.
Closing it needs the FULL Khovanskii/Pfaffian-chain machinery (the target-shift trick +
`combinedBoundE`) to distinguish "bounded via cancellation" from "actually equals
`log(c2+sin x)`'s oscillating, non-cancelling structure" — exactly the tool this thread has
been trying to avoid needing by looking for a shortcut. There isn't one. The real remaining
work (T1's own chain construction, feeding the inductive hypothesis into
`enc_combinedBound`) is not optional scaffolding around an easier core argument — it IS the
core argument. Not started this pass; this section sharpens the map rather than closing
ground, and that sharpening is itself the honest deliverable.

## 2026-07-19 (cont.) — one scoping question resolved by reading the existing pattern, and an honest stop here

Before pushing further, checked something that had started to worry me: does closing this
residual actually require the FULL `EMLWitnesses T1 x0` (T1's own internal recursive witness
structure), not just `∃x0, 0 < S3.eval x0`? If so, the scope is much bigger than "prove no tree
equals `log(c2+sin x)`" — it's entangled with the fully general, still-open witness-existence
question for T1's own arbitrary substructure.

**Checked against the actual pattern, not assumed:** `eml_depth2_witness_of_const_le_one_sibling`
and `eml_depth2_witness_of_const_sibling_unbounded_T1` (the two ALREADY-CLOSED depth-2 cases,
`EMLSmoothness.lean`) both conclude exactly `∃ x0, 0 < S3.eval x0` — nothing about `T1` or `S3`'s
own internal `EMLWitnesses`. Neither is called anywhere else in the codebase (grepped — zero
hits). **This confirms the established pattern**: these are deliberately standalone building
blocks, each proving one child's positivity in isolation, with the full `EMLWitnesses`
assembly (choosing one `x0` that satisfies every conjunct across the whole tree
simultaneously) left as later, separate work — not something each individual closure needs to
solve itself. This session's work (target-shift trick, depth-1 exclusion, the cancellation
counterexample) fits this exact pattern and was correctly scoped throughout — it was NOT
missing a bigger requirement, it was matching the codebase's own established shape for this
kind of lemma.

**Where this leaves things, honestly.** Even correctly scoped, closing `∃x0, 0<S3.eval x0` for
the `c2>1` residual still needs `LogArgPosOn T1 (Icc a b)` as a hypothesis to run
`enc_combinedBound` on `T1` itself (mirroring `sin_not_in_eml_any_depth`'s own structure) — and
the cancellation counterexample shows this can't be discharged by an elementary argument once
`T1` is compound; it needs `eml_pfaffian_validon_of_witnesses`, which needs
`EMLWitnesses T1 x0` — the SAME recursive difficulty, one level down, exactly where this whole
investigation started (`EML_WITNESS_FINDING_DECISION_2026_07_15.md`'s original round-19
finding). Building `T1`'s own Pfaffian chain (`enc T1 chain'` — the encoder itself IS already
fully generic over any tree, confirmed via `EMLExplicitBoundEncoder.lean`'s own docstring, so
this part is not new work) and threading a genuine strong induction through
`enc_combinedBound` is real, substantial, unstarted engineering — realistically multiple more
sessions, not a continuation of this one.

**Stopping here for now, not because the thread is exhausted, but because further progress
needs that dedicated push rather than another incremental step.** Three genuine, verified,
non-circular results came out of this arc: the target-shift trick (mechanism identified and
checked against source), the depth-1 exclusion (`WitnessResidualDepth1.lean`, compiled), and
the cancellation obstruction (`WitnessResidualCancellation.lean`, compiled) — real narrowing of
an open problem, each independently checked, none of them a false start.

## 2026-07-20 — the chain/bound plumbing itself: built, compiled, verified

Picked back up per direct user request to start on exactly the piece flagged above as
unstarted engineering. `MachLib/WitnessResidualChainSkeleton.lean` (commit `d79e85ab`):
`T1_not_eq_log_c2_plus_sin_given_validon` — mirrors `sin_not_in_eml_any_depth`'s exact proof
shape, but for an arbitrary `T1` satisfying the shifted target `log(c2+sin x)`, taking `T1`'s
own `EMLPfaffianValidOn` as an EXPLICIT hypothesis (`hvalidon_any_b : ∀ b>0,
EMLPfaffianValidOn T1 0 b`) rather than trying to derive it — deliberately isolating the one
piece that genuinely needs induction from everything else, to verify the REST of the
architecture is sound first.

**Result: it is.** Compiled clean on the first full attempt (after actually reading
`PfaffianFn.eval`'s definition, `enc_eval`'s exact statement, and `MultiPoly.eval`'s linearity
over `sub`/`const` — not guessed). `enc T1 emlEmptyChain`, the shifted polynomial
`p' := p.sub (const (log c2))`, `combinedBoundE`, and the `M+1`-zeros-at-`kπ`-exceed-`M`
contradiction all work exactly as designed for a fully symbolic, unconstrained `T1`. Full
`lake build MachLib` passes. `#print axioms` confirms non-circular: only MachLib's standard
foundational axioms plus its already-trusted analytic-function infrastructure
(`HasDerivAt_*`, `analytic_finite_zeros_compact`, `rolle_ct`) —
`eml_pfaffian_validon_from_sin_equality` does not appear.

**What this actually buys**: the entire remaining difficulty in closing this residual is now
concentrated in exactly ONE precisely-stated hypothesis —
`∀b>0, EMLPfaffianValidOn T1 0 b`, i.e. establishing this via `eml_pfaffian_validon_of_witnesses`,
which needs `EMLWitnesses T1 x0` for T1's own (unconstrained, structurally arbitrary)
substructure. This is exactly the recursive difficulty the cancellation counterexample (above)
already showed is real and not closeable by an elementary argument — but it is now a SINGLE,
sharply-defined remaining gap, not a vague "needs the full machinery" description. Whoever
picks this up next has: a working chain/bound skeleton to plug a witness-supply into, not a
blank page.

**Not yet attempted**: actually discharging `hvalidon_any_b`. The natural next step (worked out
on paper this session, not yet built) is a strong induction on `T1`'s structure where the
`eml A B` case recurses via the SAME "assume the right child ≤0 everywhere, collapse" strategy
used throughout this whole file — and a genuinely useful sub-finding from that paper work: the
"value at `kπ` is a clean constant" invariant (`sin(kπ)=0`, hence
`log(c2+sin(kπ))=log(c2)`) PROPAGATES through arbitrarily many nested collapses
(`log(c2'+γ)` at the same `kπ` points, for any prior clean constant `γ`) — meaning the
target-shift trick itself generalizes cleanly across the whole nested-target family that
recursive collapses generate. What does NOT yet have a clean resolution: the `c2 ≥ 2` sub-case
of a right-child collapse pushes the problem to the LEFT child needing an even MORE nested
target (`log(log(c2+sin x))`), and closing that recursively (rather than hitting an immediate
elementary contradiction the way `1<c2<2` does) needs the induction to be stated over the WHOLE
nested-target family, not just `log(c2+sin x)` — a real, nontrivial generalization exercise,
not sketched further here.

## 2026-07-20 (cont.) — the `1<c2<2` slice of `hvalidon_any_b`, closed elementarily

`MachLib/WitnessResidualDepth2Elementary.lean` (commit `5420347c`):
`depth2_witness_B_of_c2_between_one_two`. `EMLWitnesses T1 x0` for `T1 = eml A B` needs THREE
things — `EMLWitnesses A x0`, `EMLWitnesses B x0`, `0 < B.eval x0`. This closes the THIRD,
for `1<c2<2` specifically, by exactly the mechanism that closed the original `S2≤1` case one
recursion level up (`eml_depth2_witness_of_const_le_one_sibling`): assume `B≤0` everywhere,
collapse forces `exp(A.eval x)=log(c2+sin x)` for all `x`, and at `x=-π/2` this gives
`exp(A.eval(-π/2)) = log(c2-1)` — strictly negative whenever `0<c2-1<1`, i.e. exactly
`1<c2<2` — contradicting `exp>0`. Same point, same mechanism, one level deeper. Numerically
spot-checked before formalizing (5 values of `c2∈(1,2)`, all giving `log(c2-1)<0` as
predicted). Compiled clean after two real fixes: `MachLib.Real` has no `OfNat` instance for
bare numeral `2` (every file in this codebase writes `(1+1)` for real `2` — missed initially,
compiler caught it) and one rewrite-direction error (`rw [h1]` vs `rw [← h1]`). Axiom-checked
non-circular — purely elementary, doesn't even touch the Khovanskii/analytic layer.

**Still open, honestly**: `EMLWitnesses A x0` and `EMLWitnesses B x0` themselves (the other
two conjuncts) — not attempted. `c2≥2` — not covered, recurses into the nested-target family
described above. This is one clean slice of the remaining problem, not the whole remaining
problem.

## 2026-07-20 (cont.) — picking up after a VS Code crash; `EMLWitnesses A x0`/`B x0` attempted,
## found to be the SAME difficulty as `c2 ≥ 2`, not a separable piece

Session interrupted by a VS Code crash; picked back up from a clean `git status` (everything
through the `1<c2<2` closure above was already committed, nothing lost) per direct user request
to continue on `EMLWitnesses A x0`/`EMLWitnesses B x0` specifically (offered as an alternative
to pushing `c2≥2` directly; the user picked the A/B conjuncts).

**Infrastructure result (mechanized).** `EMLWitnesses` is trivially `True` at any point for a
leaf (`const`/`var`) — direct unfold of the recursive definition's base case
(`eml_witnesses_leaf_const`, `eml_witnesses_leaf_var`, `WitnessResidualDepth2ABConjuncts.lean`).
Cheap, but worth having named: whenever `A` or `B` turns out to be a leaf, that conjunct is free
and the recursion concentrates entirely on the other child.

**A genuine extension (mechanized).** Tried an Option-C-style check first: can `B` be chosen
(consistent with `T1.eval x = log(c2+sin x)`) so that `EMLWitnesses B x0` is impossible for
every `x0`, independent of whether `B.eval` itself is positive? First candidate (`B`'s own
right-child a negative constant, forcing `EMLWitnesses B` false structurally) turned out to
require `B` to be exactly the ALREADY-EXCLUDED "`B ≤ 0` / collapses to a small positive
constant" family — not a new obstruction. Formalized the sharper version of this as
`depth2_no_T1_with_const_B_small`: for `B` a constant `b`, `T1 = eml A B` can satisfy
`T1.eval = log(c2+sin x)` only if `b*(c2-1) > 1` — strictly wider than the earlier `B ≤ 0`
exclusion (which is the `b*(c2-1) ≤ 0` sub-case). Bonus finding while formalizing: the proof
never needs `c2 < 2` — Lean's unused-variable linter caught it, confirmed by dropping the
hypothesis and re-checking the proof still closes. So this piece holds for every `c2 > 1`, not
just the `(1,2)` slice the THIRD-conjunct closure was scoped to.

**The load-bearing negative finding (paper-level, not further formalized this pass).** Pushed
past the elementary exclusion to see what closes the gap it leaves open (`b*(c2-1) > 1`, i.e. a
LARGE constant `B`) — and to check whether `EMLWitnesses A x0`/`B x0` might be strictly easier
than the already-deferred `c2 ≥ 2` case. It is not. With `B` a large enough constant to survive
the `x=-π/2` check, `T1.eval x = log(c2+sin x)` forces `exp(A.eval x) = log(c2+sin x) + log b`
globally. At every `x = kπ` (`sin(kπ)=0`, the same spacing that drives every zero-counting
argument in this file), this collapses to a FIXED level `log(c2) + log b` for all integers `k` —
so `A` itself must equal `log(log(c2+sin x) + log b)`, a target of exactly the
`log(log(c2+sin x))` shape already flagged as the `c2 ≥ 2` case's open difficulty (see the
2026-07-19 entry above), reached here even though the OUTER `c2` is safely in `(1,2)`. Checking
the leaf-`B` escape (`B` a leaf so `EMLWitnesses B` is free per the infrastructure result above)
doesn't avoid this either — a leaf `B` is exactly what forces `A` to carry all of `T1`'s
remaining depth, and a large-constant leaf `B` is exactly the case that reproduces the nested
target.

**What this means for the two "independent" next-step options offered to the user this
session:** they are not independent. `EMLWitnesses A x0`/`B x0` and the `c2 ≥ 2` nested-target
case both bottom out in the same unresolved object — a finite EML tree equalling
`log(log(c2+sin x))` (or deeper nestings of the same shape) — so closing either one for real
requires building the same piece of machinery (the strong induction over the nested-target
family sketched 2026-07-19). Whoever picks this up next should treat them as ONE piece of work,
not two.

**Separately, an unrelated wiring gap found and fixed while doing this.** `EMLSmoothness.lean`
— the file containing `EMLWitnesses`, `EMLPfaffianValidOn`'s witness-closure machinery, and the
capstone `eml_pfaffian_validon_of_sin_and_witness_at_point` that this whole document treats as
"the mechanism side is complete" — was NOT imported anywhere in `MachLib.lean`'s dependency
tree (confirmed by grep: zero `import MachLib.EMLSmoothness` in the whole repo before this
session). It compiled standalone (`lake build MachLib.EMLSmoothness` passed on its own) but
nothing in the actually-built `MachLib` library — including `EMLExplicitBoundSinBarrier.lean`,
which still directly invokes the raw `eml_pfaffian_validon_from_sin_equality` AXIOM rather than
anything from `EMLSmoothness.lean` — could see or use its results. This is likely because every
file in this family up to now (`WitnessResidualDepth1/Cancellation/ChainSkeleton/
Depth2Elementary`) only needed raw existential facts (`∃x0, 0<B.eval x0`), never the
`EMLWitnesses` predicate by name — `WitnessResidualDepth2ABConjuncts.lean` is the first file in
the family to actually reference it, which is what surfaced the gap (a `function expected at
EMLWitnesses` elaboration error, from the identifier being auto-bound as an implicit because it
genuinely wasn't in scope). Fixed by adding `import MachLib.EMLSmoothness` to the new file;
`EMLSmoothness.lean` is now reachable from `MachLib.lean`'s root for the first time. Full `lake
build MachLib` passes (387 modules) after the fix. This does NOT mean the capstone is now WIRED
INTO the axiom's closure (`EMLExplicitBoundSinBarrier.lean` still calls the raw axiom, unchanged
— that swap is separate, not-yet-done work) — only that its results are now reachable by other
files that need to build on them, which the current piece of work needed and future ones will
too.

All new results: `#print axioms`-checked non-circular (only MachLib's standard foundational
axiom base — `eml_pfaffian_validon_from_sin_equality` does not appear), zero `sorry`. Full
`lake build MachLib` passes.

## 2026-07-20 (cont.) — the zero-counting argument generalized over the target; one nesting
## level pushed through concretely

Per continued user request ("proceed please") after the rescoping entry above. That entry
concluded `EMLWitnesses A/B x0` and `c2≥2` are the same difficulty because both need a proof
that works for the WHOLE nested-target family (`log(c2+sin x)`, `log(d+log(c2+sin x))`, deeper),
not just the one target closed so far. Took that literally: re-read
`T1_not_eq_log_c2_plus_sin_given_validon` (`WitnessResidualChainSkeleton.lean`) closely enough to
check how much of it is actually `log(c2+sin x)`-specific versus generic machinery that happens
to be applied to that target.

**Finding: almost none of it is target-specific.** The `M+1`-zeros-exceed-`M` argument (the
encoder, `combinedBoundE`, the zero list at `{kπ}`) never touches the target's shape. Exactly two
places do: the value the target takes at every `kπ` (`log(c2+sin(kπ)) = log(c2)`, a fixed level,
via `sin(kπ)=0`) and a witness point where the target differs from that level
(`log(c2+sin(π+1)) ≠ log(c2)`, via `sin(π+1)≠0`).

**`no_tree_eq_target_given_validon`** (`WitnessResidualTargetGeneric.lean`): the same proof with
`log(c2+sin x)` replaced by an abstract `TARGET : Real → Real` and `log c2` replaced by an
abstract level `L`, taking those two facts as hypotheses (`hTargetKPi : ∀k≥1, TARGET(kπ)=L`,
`hTargetPi1 : TARGET(π+1)≠L`) instead of deriving them from `sin`'s own algebra.
`EMLPfaffianValidOn T1` is still an explicit, undischarged hypothesis, unchanged from the
chain-skeleton file — this only removes hardcoding around the still-open induction, it doesn't
touch the induction itself.

**`T1_not_eq_nested_log_given_validon`**: the abstraction used once, for
`TARGET(x) = log(d + log(c2+sin x))` — exactly the shape identified in the prior entry as what
`A` would have to equal in the "`B` a large constant" escape route. Needed one new ingredient the
un-nested proof didn't: `log_injective_pos` (already existed, `SinNotInEMLDepth2Sweep.lean`), to
turn `log(d+log(c2+sin(π+1))) ≠ log(d+log c2)` into `sin(π+1)≠0` through TWO layers of log
instead of one — plus a positivity side-condition (`hdc2 : 0 < d + log(c2-1)`, the minimum of
`d+log(c2+sin x)` over all `x`) to keep the outer log from ever clamping, without which the
target isn't a genuine two-level nesting at all. Compiled clean after two fixes: `set` isn't
available (Mathlib-free project — the 2026-07-16 entry above already flagged this same gap;
worked around by writing the level value out as a plain term everywhere instead of naming it,
rather than reaching for `let`+`show` this time since no rewriting under the binder was needed);
and `add_le_add_left`'s shifted-constant argument is EXPLICIT, not implicit the way `mul_pos`'s
arguments are — caught by a first failed build attempt, fixed by reading the actual signature in
`Forge.lean` rather than guessing.

**Honest scope of this pass**: this does NOT discharge `hvalidon_any_b` for either target (still
the genuinely open induction), and does NOT set up a formal induction over arbitrarily many
nesting levels — it demonstrates, concretely, that the abstraction reaches one level deeper than
where the mechanism previously stopped, which is real evidence the "state the induction over the
whole nested-target family" plan is buildable rather than just plausible. The natural next step
if this continues: define the nested-target family as an actual inductive/recursive Lean
structure (parametrized by a list of shift constants) and restate `no_tree_eq_target_given_validon`
as a statement quantified over that family with `hTargetKPi`/`hTargetPi1` derived generically
(by induction on the nesting depth) rather than re-proven by hand at each level the way this pass
did for level 2. Not started.

`#print axioms` on both new theorems: only MachLib's standard foundational + already-trusted
analytic-function axiom base (the same set `T1_not_eq_log_c2_plus_sin_given_validon` uses,
nothing new), `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`. Full
`lake build MachLib` passes (388 modules).

## 2026-07-20 (cont.) — the whole nested-target family closed by one induction, not one level
## at a time

Per continued "proceed please." The prior entry's own write-up named the natural next step: a
real inductive nested-target family type with the two key facts (`hTargetKPi`, `hTargetPi1`)
derived generically by induction on nesting depth, instead of hand-proving each level as it was
needed. Built it (`WitnessResidualNestedTargetFamily.lean`).

**The family.** `nestedTarget cs`, `cs : List Real` a list of shift constants:
`nestedTarget [] = sin`; `nestedTarget (c :: cs) x = log(c + nestedTarget cs x)`. `cs = [c2]`
is `log(c2+sin x)`; `cs = [d, c2]` is `log(d+log(c2+sin x))` — the two targets from the previous
two files, now special cases of one list.

**The induction (`nestedTarget_facts`).** By induction on `cs`, given a well-formedness
condition (`nestedWF cs` — each layer's shift constant keeps that layer's log from ever
clamping, checked against a bound propagated the same way as the target itself), proves THREE
things together: `nestedTarget cs`'s range is bounded (`[nestedLo cs, nestedHi cs]`,
propagated one log-shift per layer from `sin`'s own `[-1,1]`); its value at every `kπ` (`k≥1`)
is a fixed level `nestedLevel cs` (`sin(kπ)=0` propagates through arbitrarily many layers
uniformly in `k` — proved ONCE here, reused at every depth, rather than re-derived per level);
and it differs from that level at `π+1` (via `log_injective_pos`, peeling one layer per
induction step — this is the one place the induction does genuinely new work each level, not
just algebra, since each layer needs its own injectivity application). The three are proved
TOGETHER because the range fact is exactly what the next layer's own well-formedness check
needs.

**The payoff (`no_tree_eq_nested_target_given_validon`).** Combined with
`no_tree_eq_target_given_validon`: no finite EML tree can equal ANY member of the nested-target
family while having `EMLPfaffianValidOn` throughout — the whole family, in one proof, not one
hand-derivation per level. A sanity-check corollary
(`T1_not_eq_log_c2_plus_sin_given_validon_via_family`) re-derives the ORIGINAL
`log(c2+sin x)` result (`cs=[c2]`) through the general theorem, confirming the abstraction is
equivalent to — not just similar to — the hand-proved result it generalizes.

**What this closes and what it still doesn't.** This closes the "does a finite tree realize
*some* target in this family" side of the problem COMPLETELY — not partially, not one more
level, the whole countable family in one induction. It does NOT close `hvalidon_any_b` itself
(establishing a tree's own `EMLPfaffianValidOn` from its structure) — that remains the separate,
genuinely open induction on TREE structure (as opposed to the induction on TARGET nesting depth
closed here) that the rest of Option D's remaining work is about. The two inductions are
independent axes: this file's induction is on how deep the shifting-log target is nested; the
still-open one is on how deep the EML tree claiming to realize it is nested. Closing the second
is what would let `EMLWitnesses A x0`/`EMLWitnesses B x0` (and `c2≥2`) actually discharge, not
just be well-posed.

Two real build gotchas, worth recording since they're generic to this Mathlib-free setting, not
specific to this proof: (1) `show` inside a nested `have := by show ...; exact ...`, applied to
goals built from `noncomputable` well-founded-recursion-compiled `def`s (the four `nestedX`
functions here), produced spurious "type mismatch: `this`" errors even though the shown
statement was definitionally the unfolded goal — worked around by proving explicit `rfl`-based
equation lemmas (`nestedTarget_cons`, etc.) and using plain `rw` instead of `show`, which is
syntactic rather than defeq-based and didn't hit the same issue. (2) `mach_ring` closed
`(c + nestedTarget cs' (π+1)) - c = nestedTarget cs' (π+1)` but left a residual unsolved goal on
the algebraically-identical `(c + nestedLevel cs') - c = nestedLevel cs'` — same shape, opaque
atom either way, no explanation found; worked around with an explicit two-step derivation
(`add_comm` then `add_sub_cancel_right`, from `Decimal.lean`) instead of relying on `mach_ring`
for that one step.

`#print axioms` on all three new theorems: same base as the un-nested version (MachLib standard
+ already-trusted analytic-function axioms), `eml_pfaffian_validon_from_sin_equality` does not
appear, zero `sorry`. Full `lake build MachLib` passes (389 modules).

## 2026-07-20 (cont.) — the third `EMLWitnesses` conjunct, generalized to the whole family;
## and a clear line drawn around what's actually still missing

Per continued "proceed please." Went looking for what was actually special about `1<c2<2` in
`depth2_witness_B_of_c2_between_one_two` — whether it was a real restriction or an artifact of
that proof only having `log(c2+sin x)` available.

**It was an artifact.** `x=-π/2` isn't special to that one target — it's `sin`'s own minimum
point, and `nestedTarget_at_neg_pi_div_two` (`WitnessResidualNestedTargetBWitness.lean`) proves,
by the same one-line induction shape as `nestedTarget_facts`, that `nestedTarget cs (-π/2) =
nestedLo cs` for EVERY well-formed `cs` — each layer's `log` is monotone, so "achieves the
minimum here" survives every nesting layer unchanged. Checked (not assumed) that `1<c2<2` is
EXACTLY `nestedWF [c2] ∧ nestedLo [c2] < 0` (`nestedWF [c2]` needs `c2>1`; `nestedLo [c2] =
log(c2-1) < 0` needs `c2<2`) — the two conditions coincide precisely.

**`witness_B_not_le_zero_of_lo_neg`**: for ANY well-formed `cs` with `nestedLo cs < 0`, `T1 = eml
A B` satisfying `T1.eval = nestedTarget cs` has `∃x0, 0<B.eval x0` — the THIRD `EMLWitnesses T1
x0` conjunct, now closed for the whole family (every depth), not one hand-checked level. `B`
doesn't need to be a constant either (unlike `depth2_no_T1_with_const_B_small`) — the argument
only ever used `B`'s SIGN, never its shape, so that restriction drops out too. One build hiccup:
`rw [h1] at hlo` initially rewrote in the wrong direction (tried to find `exp(...)`'s pattern
inside `hlo`, which doesn't mention it) — fixed by rewriting with `← h1` instead, substituting
`nestedLo cs` (which DOES appear in `hlo`) with the exp expression.

**Why this doesn't close more than it says, and what that clarifies.** Chased whether the
`nestedLo cs ≥ 0` case (where this elementary trick doesn't apply) could recurse usefully: if
`B≤0` everywhere AND `nestedLo cs ≥ 0`, the collapse forces `A.eval x = log(nestedTarget cs x)`
for all `x` — which, if `nestedLo cs > 0` strictly (so the log doesn't clamp), is EXACTLY
`nestedTarget (0 :: cs) x` — `A` would have to realize a target ONE LAYER DEEPER in the very
family this file's induction already covers. This is a genuine structural insight (it explains
NEATLY why `c2≥2`'s difficulty is "the same shape, one level in" — confirmed independently of
the earlier rescoping entry's derivation, from a completely different angle this time) but it
does NOT escape the core recursive requirement: applying `no_tree_eq_nested_target_given_validon`
to `A` needs `A`'s OWN `EMLPfaffianValidOn`, which is the exact same kind of hypothesis this
whole investigation has been trying to discharge for `T1` — pushed one level down, not removed.
Checked carefully (not just asserted) before writing this up, specifically to see if it was a
disguised escape hatch. It isn't. The recursion bottoms out on the same wall every time: no
matter how the target-side induction is sliced, `EMLPfaffianValidOn` for a COMPOUND tree needs
`EMLWitnesses`, which needs the same fact for its own children — and `EMLWitnesses` is a
property that can genuinely FAIL for legitimate trees regardless of what equation they satisfy
(a leaf `const c` with `c ≤ 0` sitting as some node's right child breaks it structurally, with no
dependence on any target at all) — so there is no way to bootstrap it purely from target algebra.
This is the same wall the 2026-07-16 cancellation counterexample
(`WitnessResidualCancellation.lean`) found from the boundedness angle; this pass finds it again
from the nested-target angle. Two independent routes hitting the identical obstruction is itself
useful confirmation this is a genuine wall, not a gap in either investigation's cleverness.

**Where this leaves Option D, honestly, after today's four files.** The target side is now
fully general (any nesting depth, one induction) and the elementary sub-cases within it are
pushed as far as they go (the `nestedLo cs < 0` slice, for both the third `EMLWitnesses`
conjunct and — via the earlier chain-skeleton work — the "no tree realizes this target" question
itself, given validity). What remains, named as precisely as it can be without having built it:
a strong induction on EML TREE depth (orthogonal to the target-nesting-depth induction closed
today) establishing `EMLPfaffianValidOn` for a compound tree from ITS OWN two children's
validity plus one anchor point — which is circular exactly at the point where `EMLWitnesses`
needs to hold for children whose only obligation is to make some outer equation balance, with no
further constraint pinning down their SPECIFIC recursive shape. This is not a new characterization
of the difficulty; it is the SAME one from round 19 (2026-07 investigation start) and the
2026-07-16 cancellation counterexample, now confirmed from a third independent angle. `#print
axioms` clean (same base, no dependence on the axiom under investigation), zero `sorry`. Full
`lake build MachLib` passes (390 modules).

## 2026-07-20 (cont.) — a complete, unconditional closure, for a real (if restricted) class of
## trees. First one in the whole arc with no undischarged hypothesis.

Per continued "proceed please." Every result up to this point — including the fully general
target-side closure — left `EMLPfaffianValidOn T1` (equivalently `EMLWitnesses T1 x0`) as an
explicit hypothesis, "confirmed from two independent angles" as the genuine remaining wall. This
entry asks: is there a natural, checkable class of trees where that wall simply doesn't apply?

**`RightChildrenSimplePositive`** (`WitnessResidualSimpleRightChildren.lean`): every right
child, at every `eml` node throughout the WHOLE tree (recursively), is either the bare variable
or a positive constant — never compound, never non-positive. Left children are completely
unrestricted (arbitrarily deep, arbitrarily compound). `EMLWitnesses` and `EMLNoCrossingAt` are
both free for this class, by the same one-line reason: right children never recurse into
uncertain substructure, so their positivity/non-vanishing is either immediate (positive
constant) or reduces to a single scalar condition (`x0 > 0`, for `var`).

**A real subtlety, found while assembling the proof, not anticipated going in.** The natural
first attempt — `RightChildrenSimplePositive A ∧ RightChildrenSimplePositive B` as two SEPARATE
hypotheses, using the previous file's `witness_B_not_le_zero_of_lo_neg`/
`witness_B_pos_at_point_of_lo_neg` to cover `B`'s positivity when `B` is compound — does not
actually work. `EMLWitnesses`'s third conjunct only ever needs positivity at ONE point, but
`EMLPfaffianValidOn`'s own third conjunct (`B.eval x ≠ 0`, needed via `EMLNoCrossingAt`)
needs it THROUGHOUT AN INTERVAL — one positive point cannot supply that for a compound `B`. The
fix: apply `RightChildrenSimplePositive` to the WHOLE tree `T1 = eml A B` at once, which
(unfolded) is exactly `RightChildrenSimplePositive A ∧ (B = var ∨ ∃c, B = const c ∧ 0<c)` — `B`
itself, not just its descendants, must be simple. Once it is, non-vanishing holds everywhere for
free. A second surprise fell out of this: `nestedLo cs < 0` (needed for the elementary trick
that would have supplied a compound `B`'s positivity) turns out not to be needed AT ALL once `B`
is simple directly — **the closure holds for literally any well-formed `cs`, not just the
`nestedLo cs < 0` slice.**

**The result** (`no_T1_with_simple_right_children`): no finite tree `T1 = eml A B` with
`RightChildrenSimplePositive T1` can satisfy `T1.eval = nestedTarget cs` globally, for ANY
well-formed `cs` — proved with NO undischarged hypothesis. Built from: `nestedTargetDeriv`
(explicit derivative formula, one `1/(c+·)` factor per nesting layer via the chain rule,
positivity supplied by `nestedWF` + `nestedTarget_facts`'s range bound — no new positivity
argument needed) and `nestedTarget_hasDerivAt` (the derivative actually holds, by induction,
transported to `T1.eval` via `HasDerivAt_of_eq` and `hT1eq`); combined with `EMLWitnesses`/
`EMLNoCrossingAt` freeness above, wired through `eml_pfaffian_validon_of_witnesses_backward` /
`_twosided` (both already-built, GENERIC-in-target machinery from `EMLSmoothness.lean` — not
the `sin`-hardcoded capstone, which doesn't apply here) to get `EMLPfaffianValidOn T1 0 b` for
every `b > 0`, then `no_tree_eq_nested_target_given_validon` for the final contradiction.
Compiled clean on the first careful attempt for every piece, including the full assembly —
notable given how many earlier files in this arc needed 1-3 rounds of `show`/argument-order
fixes; the earlier files' groundwork (robust `rfl` unfold lemmas, correct `HasDerivAt_comp`
argument order worked out once and reused) paid for itself here.

**Where this leaves Option D.** This is the FIRST result in the entire arc — going back to the
very first `sin_not_in_eml_any_depth` investigation — that closes an actual instance of "no tree
realizes this target" with ZERO remaining hypotheses, for a real (if syntactically restricted)
class of trees. It does not touch the general case: `RightChildrenSimplePositive` genuinely
excludes trees like `WitnessResidualCancellation.lean`'s counterexample (compound right child at
the top node), and the wall for THOSE trees is exactly where the previous entry left it. But the
dichotomy is now sharp and useful: either a tree encountered in this investigation has simple
right children (closed, unconditionally, today) or it doesn't (open, needs the still-missing
tree-depth induction). `#print axioms`: standard foundational base plus the already-trusted
analytic/`HasDerivAt` infrastructure (same kind of axioms `EMLSmoothness.lean` itself rests on),
`eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`. Full `lake build MachLib`
passes (391 modules).

## 2026-07-20 (cont.) — closing the loop: a direct witness for `S3`, in the original problem's
## own vocabulary

Per continued "proceed please." Everything today up to this point was stated in terms of
`nestedTarget cs` — the right abstraction for BUILDING the machinery, but one step removed from
the actual question. `EMLSmoothness.lean` already has two members of a family that conclude
`∃x0, 0<S3.eval x0` directly from `t = eml T1 (eml (const c2) S3)` agreeing with `sin`:
`eml_depth2_witness_of_const_le_one_sibling` (`c2 ≤ 1`) and
`eml_depth2_witness_of_const_sibling_unbounded_T1` (`T1` unbounded, any `c2`). The gap between
them — `c2 > 1`, `T1` bounded — is EXACTLY this whole investigation's residual. Today's
`RightChildrenSimplePositive` closure can become the THIRD member of that family, closing a real
slice of exactly that gap, stated with no `nestedTarget` visible in the final theorem at all.

**Two small pieces of connective tissue** (`WitnessResidualSimpleT1Application.lean`):
1. `no_tree_with_simple_right_children` — the previous file's closure required its tree to be
   literally `eml A B` at the top, an artifact of how it was built (needed to unfold
   `RightChildrenSimplePositive` for the docstring's explanation), not a real requirement. Every
   piece of the proof already works for an arbitrary `T1`. Restated once, generally.
2. `eml_T1eq_of_const_sibling_le_zero` — the `S3 ≤ 0` collapse itself, derived directly,
   mirroring `eml_depth2_witness_of_const_le_one_sibling`'s own derivation line-for-line through
   `exp(T1.eval x) = c2 + sin x`, differing only in what happens after: `c2 ≤ 1` refutes
   immediately at that point; `c2 > 1` instead yields the genuine equation `T1.eval x =
   log(c2+sin x)` this whole arc has been trying to rule out.

**The result** (`eml_depth2_witness_of_const_gt_one_sibling_simple_T1`): for `t = eml T1 (eml
(const c2) S3)` agreeing with `sin`, `c2 > 1`, and `T1` satisfying `RightChildrenSimplePositive`
— `∃x0, 0 < S3.eval x0`, directly. Genuinely the third member of the family: same shape as its
two siblings, no trace of today's internal machinery (`nestedTarget`, `EMLWitnesses`,
`EMLPfaffianValidOn`) in the statement, only in the proof. Compiled clean, no errors, on the
FIRST attempt for the entire file — the derivative/witness/no-crossing infrastructure built
earlier today was already exactly what this needed, with no new lemmas required beyond
restating them one level more generally.

**What this means for the family's coverage, honestly.** `c2 ≤ 1` (closed), `T1` unbounded any
`c2` (closed), `c2 > 1` with `T1` having `RightChildrenSimplePositive` (closed, today). The
remaining gap is precisely: `c2 > 1`, `T1` bounded, `T1` NOT `RightChildrenSimplePositive` (i.e.
`T1` has some compound right-child somewhere in its structure) — exactly where
`WitnessResidualCancellation.lean`'s counterexample lives, and exactly the wall confirmed twice
over earlier today. Nothing about that remaining gap has changed; what's changed is that the
"closed" region is now checkable, sizeable, AND expressed in terms someone using this family
(rather than someone reading today's internal proof machinery) can actually invoke.

`#print axioms`: same base throughout (standard + already-trusted `HasDerivAt`/analytic
infrastructure), `eml_pfaffian_validon_from_sin_equality` does not appear anywhere in the chain
— notable since this theorem's OWN hypothesis (`hsin`) is literally that axiom's hypothesis
shape, and the proof still doesn't need to invoke it. Zero `sorry`. Full `lake build MachLib`
passes (392 modules) — seven new files today (`b91e770e` through this entry's commit), all
independently verified, zero regressions.

## 2026-07-20 (cont.) — attempting the fully general case; real further progress, and the wall
## characterized precisely enough to say exactly what closing it would require

Explicitly asked to attempt the general case (arbitrary `A`, `B`, not just `RightChildrenSimplePositive`
on both) rather than stop at today's family closure. Genuine further progress came out of this,
plus — more valuably — the sharpest characterization yet of exactly where the wall is and what
would be needed to remove it.

**Real progress** (`WitnessResidualBWitnessGeneralB.lean`, `witness_B_not_le_zero_of_A_simple`):
the earlier `witness_B_not_le_zero_of_lo_neg` needed `nestedLo cs < 0` to close. Using TODAY's
own whole-tree closure (`no_tree_with_simple_right_children`) recursively — applied to `A`, not
`B`, on the branch the elementary trick doesn't reach — that restriction drops entirely: if `A`
(not `B`) is `RightChildrenSimplePositive`, `B` cannot be `≤ 0` everywhere, for ANY well-formed
`cs`, and `B` itself can be arbitrarily compound or adversarial. Mechanism: assume `B ≤ 0`
everywhere; if `nestedLo cs ≤ 0`, the original `-π/2` trick closes it directly; if `nestedLo cs >
0`, the collapse instead forces `A.eval x = nestedTarget (0::cs) x` for ALL `x` — `A` itself
realizes a target one layer deeper in the SAME family — refuted directly by today's own closure.

**Why this still doesn't reach the general case — checked directly, not assumed.** This gives
`∃x0, 0<B.eval x0` for arbitrary `B`, but that was never actually the bottleneck for reaching
`EMLPfaffianValidOn`: `EMLNoCrossingAt` needs `B.eval x ≠ 0` THROUGHOUT AN INTERVAL, not at one
point, and `EMLPfaffianValidOn`'s own third conjunct needs `0 < B.eval x` throughout that same
interval, directly, as a hard requirement (`EMLPfaffian.lean`'s definition, universally
quantified, no relaxation). Checked specifically whether the collapse-recursion trick could be
pushed from "one point" to "the whole interval," using periodicity: `nestedTarget cs` is
`2π`-periodic (each log-shift layer preserves whatever period the layer inside it has, inherited
from `sin`), so the `≤ 0` and `> 0` sub-regions of `nestedTarget cs` BOTH repeat forever, every
`2π`. The zero-counting argument needs intervals that GROW with `M` (`T1`'s own Pfaffian-chain
bound, unbounded in general, depends on how complex `T1` turns out to be) — so any interval large
enough to matter re-enters BOTH kinds of sub-region arbitrarily many times, no matter how far out
it's pushed. The pointwise collapse trick only ever pins `B`'s sign on the `≤0` sub-regions;
nothing in this line of attack — however it's sliced — touches the `>0` sub-regions, where `B`'s
sign is genuinely unconstrained by anything derived so far.

**What this means, concretely, for whoever picks this up next.** This is not "needs more
cleverness" — it's that `EMLPfaffianValidOn`/`enc_combinedBound`'s own definitions have zero
tolerance for interval-wide requirements failing even on a small, isolated sub-region, and
nothing available (here, in the 2026-07-16 cancellation counterexample, or in the two-independent-
angles entry earlier today) supplies interval-wide sign information for a subtree whose OWN VALUE
is otherwise unconstrained by tree shape. Two concrete paths forward, neither attempted here: (1)
weaken `EMLPfaffianValidOn`'s own definition to tolerate finitely-many or measure-zero exceptions,
then rebuild `enc_combinedBound`'s zero-counting argument to work under that weaker hypothesis —
a foundational change touching `EMLPfaffian.lean`/`EMLExplicitBoundEncoder.lean`, not a small
patch; or (2) find a genuinely different sufficient condition on `B` (weaker than "simple," but
strong enough to give interval-wide positivity some other way) — no candidate identified. Either
is real, multi-session research, matching the original 2026-07-15 estimate for the fully general
case — today's work has not shortened that estimate, only sharpened exactly what it would need to
contain.

`#print axioms` clean (same base throughout), `eml_pfaffian_validon_from_sin_equality` does not
appear, zero `sorry`. Full `lake build MachLib` passes (393 modules) — eight new files today.

## 2026-07-20 (cont.) — a second, independent mechanism for `B`'s positivity; the closed class
## widens, the wall doesn't move

Continued past the wall-characterization entry above per "proceed please," looking for a
DIFFERENT sufficient condition on `B` (path (2) from that entry) rather than the foundational
`EMLPfaffianValidOn`-weakening path (1). Found one.

**The mechanism** (`WitnessResidualBOneLevelCompound.lean`): `log`'s domain-clamp cuts both
ways. Every prior mechanism used a node's right child being POSITIVE; this one uses a node's
right child being `≤ 1` instead — `log c ≤ 0` for `0 < c ≤ 1` (`log` increasing, `log 1 = 0`),
so SUBTRACTING it can only INCREASE the parent's value: `(eml P (const c)).eval x = exp(P.eval
x) - log c ≥ exp(P.eval x) > 0`, for ANY `P` whatsoever — no restriction on `P` needed for THIS
specific fact. A genuinely different route to "compound node, provably positive" than
`RightChildrenSimplePositive` (which needs the node to BE simple); here the node is compound
and positive BECAUSE of that structure.

**What it buys**: `no_T1_with_B_one_level_compound` — `T1 = eml A (eml P (const c))` with `0 < c
≤ 1`, `A` and `P` both `RightChildrenSimplePositive`, closes the same way
`no_T1_with_simple_right_children` does. `T1`'s own right child `B` is now allowed ONE level of
compoundness (`eml P (const c)`) that was excluded entirely before — a genuine widening of the
closed class, not a restatement of it.

**What it doesn't do, honestly.** This does NOT remove the wall from the earlier entry — `A` and
`P` are STILL restricted to `RightChildrenSimplePositive`, and `B`'s allowed shape is still one
SPECIFIC narrow pattern (`eml (anything) (small positive constant)`), not "anything." It's
concrete evidence the wall isn't monolithic — different mechanisms (simple-right-child;
`≤1`-right-child) chip away at different corners of the same space — but the FULLY general case
(`B` genuinely arbitrary, including e.g. the cancellation counterexample's shape) is exactly as
open as before. Whether this `≤1` mechanism iterates further (does `Q = eml P' Q'` with `Q'`
itself satisfying some bound work the same way?) was not checked this pass — a natural next
question for whoever continues this, not attempted here.

`#print axioms` clean (same base), `eml_pfaffian_validon_from_sin_equality` does not appear,
zero `sorry`. Full `lake build MachLib` passes (394 modules) — nine new files today.

## 2026-07-20 (cont.) — the `≤1` mechanism, iterated to arbitrary depth

Natural next question from the previous entry, answered: does the `≤1` mechanism iterate — can
`B` be `eml (eml P' (const c')) (const c)`, arbitrarily deep, not just one layer?

**Yes, cleanly** (`WitnessResidualBChainCompound.lean`). `GoodPositiveChain n t`: `t` is a leaf,
or `t = eml P (const c)` (`0<c≤1`) with `P` satisfying `GoodPositiveChain (n-1)` — up to `n`
nested `≤1`-layers, bottoming out in a simple leaf. Indexed by `Nat` deliberately, not by direct
structural recursion on `EMLTree`: the witness `P` at each layer sits inside an `∃`, not reached
by `EMLTree`'s own constructors the way the `induction` tactic expects, so a naive
`EMLTree`-structural version would need real well-founded-recursion machinery to let a proof
"recurse into a grandchild." Indexing by `Nat` instead sidesteps that entirely — the `Nat`
induction's own hypothesis supplies the recursive call for `P` directly, `EMLTree` is never
itself the induction's target. All three needed facts (value-positivity, `EMLWitnesses`-freeness,
`EMLNoCrossingAt`-freeness) proved this way, then wired through the identical skeleton every
other closure in this arc uses. Compiled clean, zero errors, on the FIRST attempt for the whole
file — further confirmation that today's early groundwork (the wiring skeleton itself) is now
routine to reuse.

**Relationship to the previous entry's result, honestly.** `no_T1_with_B_one_level_compound`
allowed `B`'s one `≤1` layer's own left branch `P` to be ANY `RightChildrenSimplePositive` tree
(arbitrary left-spine depth, simple right children). `no_T1_with_B_chain_compound` allows
UNBOUNDED `≤1`-layer depth, but each layer's own `P` is restricted to ANOTHER `≤1` layer or a
leaf — narrower on that axis. The two results are complementary, neither subsumes the other:
one trades chain depth for left-branch generality, the other trades left-branch generality for
chain depth. Both leave the fully arbitrary `B` exactly where the wall-characterization entry
left it — three independent, narrow mechanisms now chip at that space (simple; `≤1`-one-layer;
`≤1`-chain), none of them close to covering it.

`#print axioms` clean, `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`.
Full `lake build MachLib` passes (395 modules) — ten new files today.

## 2026-07-20 (cont.) — why path (1) is hard, precisely: read the encoder instead of guessing

Three narrow mechanisms in a row (simple; `≤1`-one-layer; `≤1`-chain) is a signal, not just a
feeling — flagged honestly rather than forcing a fourth. Checked the OTHER path named in the
wall-characterization entry instead: what would it actually take to weaken `EMLPfaffianValidOn`
to tolerate `t2 ≤ 0` somewhere, rather than assume it's hard? Read `EMLEncoder.lean`'s `stepCC`/
`stepCD` (the log-node encoding) instead of reasoning abstractly.

**What's actually there.** Encoding a `log⟦t2⟧` node doesn't just append a `log` chain variable
— it appends a RECIPROCAL variable first (`stepCC`: `r = 1/⟦t2⟧`, with the defining relation `r'
= -(t2)'·r²`, the standard quotient-rule identity for `1/f`), THEN the log variable (`stepCD`: `L
= log⟦t2⟧`, with `L' = (t2)'·r` — i.e. `L' = (t2)'/t2`, the standard `d/dx log f = f'/f`
identity, expressed VIA the reciprocal variable rather than directly). Both of these are the
GENUINE calculus identities, and they hold ONLY when `t2 > 0` — not merely `t2 ≠ 0`. If `t2 <
0` somewhere, MachLib's `log` convention makes `L` the CONSTANT `0` there (so `L`'s TRUE
derivative is `0`), but `r = 1/t2` is still some genuine negative reciprocal — the chain's own
fixed relation `L' = (t2)'·r` would then assert `0 = (t2)'·r`, false in general. The chain isn't
merely unproven for `t2 ≤ 0`, its own algebraic relations are FALSE there.

**What this means for path (1), precisely.** "Weaken `EMLPfaffianValidOn`'s definition" is not a
predicate tweak — the SAME fixed pair of relations (`r'=-w'r²`, `L'=w'r`) cannot describe `log
t2` correctly across a sign change, because the log's TRUE behavior genuinely bifurcates at `t2 =
0` (analytic branch vs. constant-clamp branch) and the chain machinery has no notion of a
relation that switches. Supporting `t2 ≤ 0` regions for real would need a Pfaffian chain
representation that can SWITCH which relation applies on different sub-intervals (a genuinely
new chain TYPE — `PfaffianChain` as currently defined, `PfaffianChain.lean`, has no such
notion) and a zero-counting argument (`enc_combinedBound`) reworked to handle a chain that isn't
uniformly one thing throughout. This is a new construction, not a modified hypothesis on the
existing one — confirms and sharpens (with the actual mechanism, not just an estimate) what the
wall-characterization entry called "a foundational change... not a small patch."

**Where this leaves things.** Neither path is a good use of a single session: path (2) (new
sufficient conditions on `B`) has visibly diminishing returns after three found today; path (1)
now has a precise technical reason it needs new machinery, not just more effort inside the
existing one. Recorded here so whoever attempts path (1) next starts from "build a
branch-switching chain type" rather than rediscovering, by trial, that a predicate-level patch
can't work.

## 2026-07-20 (cont.) — starting path (1) for real: the strategy traced end to end, two bricks
## built, the true scope now concrete instead of estimated

Per direct request to start on path (1). Read `enc_combinedBound`'s FULL hypothesis list
(`EMLExplicitBoundEncoder.lean`) and its proof (`enc_coherent_and_hAnalytic`,
`EMLEncoderAnalytic.lean`) rather than continuing to reason about it from the outside, to find
the actual shape a branch-switching argument would need to take.

**The strategy, traced concretely.** `enc_combinedBound`'s ONLY use of `LogArgPosOn` is to
derive chain coherence (`IsCoherentOn`) and analyticity (`IsAnalyticOnReals`) for the Rolle's-
theorem descent (`combined_descent_3_explicit`) that does the actual zero-counting. This suggests
a genuine (if large) plan: split any interval `[a,b]` into finitely many sub-intervals on which
`t2`'s sign is CONSTANT; on each `t2 > 0` piece, the existing machinery applies unchanged; on
each `t2 ≤ 0` piece, `eml t1 t2` reduces EXACTLY to `eml t1 (const 1)` — a completely ordinary,
unconditionally-valid tree (`1 > 0` always, no clamp anywhere) — so THAT piece needs only `t1`'s
own validity, not `t2`'s at all. Bound each piece's zeros separately, glue the bounds.

**The catch, traced too, not glossed over.** The number of sub-intervals is bounded by `t2`'s OWN
zero-crossing count — and bounding an ARBITRARY compound tree's zero-crossings, without assuming
its own `EMLPfaffianValidOn`, is EXACTLY the same difficulty this whole arc has circled, now one
level down (recursing into `t2` instead of `T1`). Worse: `enc_combinedBound`'s `LogArgPosOn`
hypothesis is for the WHOLE tree, every log-node, not just the top one — so a genuine
branch-switching bound needs to split on EVERY internal log-node's sign, not just `t2`'s,
compounding sub-intervals combinatorially (though still finitely, since each node's own
crossing-count is separately bounded by the same recursion). The honest shape of what would
actually close this: a strong induction on tree depth that bounds zero-CROSSINGS (not
positivity) of an arbitrary tree, splitting recursively at each level. This is the concrete form
of "several weeks" the original 2026-07-15 estimate gestured at — now a describable induction,
not just a difficulty rating.

**Two bricks built, both genuinely reusable, neither close anything alone**
(`EMLExplicitBoundGlue.lean`):
1. `BoundedZerosBy.glue` — the purely combinatorial half: given zero-count bounds `K1`, `K2` on
   two adjacent open sub-intervals `(a,m)`, `(m,b)`, a bound `K1+K2+1` on the whole `(a,b)` (the
   `+1` covers `z=m` itself, missed by both open pieces). Zero analytic content — pure `List`
   combinatorics, built by reusing `length_filter_partition` (`MultiVarBucket.lean`, already in
   the codebase for an unrelated bucketing argument). One real gotcha: `Real` has classical
   `Decidable` instances for `<`/`≤` (`instDecLT`/`instDecLE`, `Basic.lean`) but NOT for `=` —
   needed a locally-scoped `DecidableEq Real := fun x y => Classical.propDecidable (x=y)`; a
   FIRST attempt supplying `Decidable` for literally every `Prop` broke `omega`'s own internal
   reasoning (it depends on the COMPUTABLE decidability of `Nat`/`Int` propositions, which the
   blanket classical override shadowed) — scoping the instance to exactly `Real`'s equality
   fixed it.
2. `eml_eval_eq_const_one_of_right_nonpos` — formalizes the "reduces to `eml t1 (const 1)`"
   fact directly (three lines: `log_nonpos` and `log_one` both give `0`).

**What remains, unstarted, named precisely.** The actual hard part — bounding an arbitrary
tree's zero-crossing count without assuming its validity, by strong induction on depth,
splitting on every internal log-node's sign recursively, and re-deriving `enc_combinedBound`'s
OTHER hypotheses (`ChainTagsValid`, `ChainTagsValidAB`, `IsTriangular`, non-degeneracy) for each
piece — is not attempted here. These two bricks are the smallest, safest, most clearly-scoped
pieces of that structure, not a shortcut past it. Real progress on "starting the hard stuff,"
honestly not close to finishing it.

`#print axioms` clean, `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`.
Full `lake build MachLib` passes (396 modules) — eleven new files today.

## 2026-07-20 (cont.) — the induction's base case, closed for real: `eml var var`, zero validity
## assumption, elementary calculus only

Per direct request to proceed to the induction itself, not just the strategy. Attempted the base
case — depth-1 trees — where the Pfaffian-chain encoder isn't needed at all: a depth-1 tree's
right child is a bare leaf, so its sign pattern is known in closed form (constant, or a single
crossing at `x=0` for `var`), not something needing its own recursive validity argument.

**`eml var var` worked through completely** (`EMLZeroCrossingDepth1.lean`, the hardest of the
four depth-1 shapes — the other three reduce to injectivity of `exp` or `log` alone). `t.eval x =
exp(x) - log(x)` for `x>0` (clamps to `exp(x)` for `x≤0`, unconditionally `>0` there, zero-free).
On `x>0`: the derivative is `exp(x) - 1/x`; THAT function's own derivative is `exp(x) + 1/x²`,
manifestly positive, so `exp(x)-1/x` is strictly monotonic (`strictMono_of_deriv_pos`,
MVT-based, already sitting unused in `MonotoneFromDeriv.lean`) — hence injective, hence at most
one zero (`atMostOneZero_of_strictMono`, new, general, reusable — any function pairwise-strictly-
monotonic on an interval has at most one zero there, proved once, works for anything). Feeding
that into `zero_count_bound_by_deriv` (Rolle's theorem, already sitting unused in `Rolle.lean`)
gives: `exp(x)-log(x)` has at most `2` zeros on any `(0,B)`. Glue with "zero zeros on `x≤0`"
(trivial): `eml var var`'s FULL evaluation has boundedly many zeros (`≤3`) on ANY interval —
proved **without ever invoking `EMLPfaffianValidOn`, `LogArgPosOn`, or the Pfaffian-chain encoder
at all.**

**Confirmed via `#print axioms`, not just claimed.** The axiom list for `eml_var_var_boundedZeros`
is exactly: standard foundational arithmetic + the `HasDerivAt` calculus rules + `rolle_ct`. Not
one encoder/chain/validity axiom or theorem appears anywhere in the dependency graph — genuinely
independent of the machinery this whole arc has been trying to avoid needing.

**Two real build gotchas, both instructive.** `HasDerivAt_inv`'s conclusion has the numerator's
negation OUTSIDE the division (`(-a)/(f x · f x)`, i.e. `(-1)/(x·x)` here), not the whole
fraction negated (`-(1/(x·x))`) — mathematically equal, syntactically different, and `mach_ring`
doesn't relate them on its own (division isn't a ring operation it normalizes through) — fixed
via the already-existing `neg_div` lemma (`FieldLemmas.lean`) to bridge the two forms explicitly
before letting `mach_ring` finish the rest. Second: `MultiVarBucket.lean`'s
`length_filter_partition` (reused again from `EMLExplicitBoundGlue.lean`'s bricks) needed an
explicit import — easy to forget when a lemma is reachable transitively in ONE file's import
chain but not another's.

**Honest scope.** This is the base case of a depth-based induction, for ONE (the hardest) of four
depth-1 shapes. The INDUCTIVE STEP — compound `t1`/`t2`, needing the full "split by every
internal log-node's sign, recurse" strategy from the previous entry — is not attempted here, and
remains the actual substance of "the induction." What this DOES establish, concretely rather
than by estimate: the base case is genuinely closeable by machinery ALREADY SITTING UNUSED in
this codebase (`MonotoneFromDeriv.lean`, `Rolle.lean` — both apparently built for a different,
earlier purpose and never wired into this investigation before today), which is a meaningfully
different, more optimistic signal than "this needs entirely new machinery" would have been.

`#print axioms` clean, `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`.
Full `lake build MachLib` passes (397 modules) — twelve new files today.

## 2026-07-20 (cont.) — the base case, actually COMPLETE: all four depth-1 shapes closed

Per continued "proceed please." The previous entry closed `eml var var` — the hardest depth-1
shape, chosen deliberately to show the base case is tractable — and flagged the other three as
"easier variants" without formalizing them. Finished the job: all four depth-1 shapes now have
proven, validity-free zero-count bounds (`EMLZeroCrossingDepth1.lean`).

**The other three, and why they turned out even simpler than expected.** `eml (const c1) (const
c2)` and `eml var (const c2)` don't even need the clamp-region split `eml var var` needed — the
right child being a FIXED constant means `log`'s clamp status doesn't depend on `x` at all, so
the whole formula is uniform. The former is a genuine constant (`0` zeros, given non-degeneracy);
the latter needs only `exp`'s own injectivity (`exp_lt`, already an axiom) — no derivative work.
`eml (const c1) var` needs the SAME clamp-region split as `eml var var` (right child is `var`,
sign flips at `0`), but on the `x>0` side needs only `log`'s injectivity on positives
(`log_lt_log`, already a theorem) rather than a second-derivative monotonicity argument.

**One reusable generalization made along the way**: `atMostOneZero_of_strictMono` (built for the
`eml var var` case, needing a fixed direction of inequality) generalized cleanly to
`atMostOneZero_of_injOn` (`f x ≠ f y` directly, no fixed direction) — the natural shape for
`exp`/`log` injectivity, which don't care about direction the way a derivative-sign argument
does. Same proof skeleton, one line changed (`hlt'` substitution replaced by a direct `Ne`
application).

**What this confirms, concretely.** Three of the four depth-1 shapes needed ZERO new machinery
beyond injectivity facts the codebase already had before today. Only the hardest (`eml var var`)
needed the derivative/Rolle argument from the previous entry. This is a genuinely complete,
closed base case for the depth-based induction the strategy needs — not a representative sample
standing in for unfinished work.

`#print axioms` clean throughout, `eml_pfaffian_validon_from_sin_equality` does not appear
anywhere, zero `sorry`. Full `lake build MachLib` passes (397 modules, same file count as the
previous entry — this extends `EMLZeroCrossingDepth1.lean` rather than adding a new file).

## 2026-07-20 (cont.) — the first genuine inductive step: a compound tree reusing a smaller
## tree's already-proven derivative-zero bound

Per continued "proceed please." With the base case complete, attempted the first COMPOUND case —
`t = eml t1 (const c)` with `t1 = eml var var` itself depth-1 — deliberately choosing `t2 = const
c` to AVOID the hardest part of the inductive step (domain-splitting when `t2` itself is compound
and sign-changing) while still exercising the actual mechanism the induction needs: reusing a
SMALLER tree's already-established result, not just restating the base case one level down.

**The mechanism, concretely.** `t.eval x = exp(t1.eval x) - log(c)`. Its derivative (chain rule)
is `exp(t1.eval x) · t1'(x)` — and since `exp(anything) > 0` always, this is `0` exactly when
`t1'(x) = 0`. `t1`'s own derivative-zero bound (`exp_sub_inv_atMostOneZero`, built as a BYPRODUCT
of closing `t1`'s own base case, not previously exposed as a standalone reusable fact) is reused
DIRECTLY here — no new derivative analysis of `t1` needed, exactly the "smaller tree's result
feeds the bigger tree's proof" pattern the induction is supposed to run on. Combined with the
`x≤0` clamp region (handled via `exp∘exp` injectivity, composing `exp_lt` with itself — no
derivative work needed there either): `eml (eml var var) (const c)` has boundedly many zeros
(`≤6`) on ANY interval, for ANY `c` (the sign of `c` turned out not to matter at all — caught by
the unused-variable linter after an initial, unnecessarily cautious `c>0` hypothesis).

**One real gotcha.** The first version of the `x≤0` bucket bound reused the "≤0 has no zeros"
SHORTCUT from the base case's `eml var var` proof directly — but that shortcut only worked
there because the WHOLE `x≤0` region was provably zero-free. Here, `z=0` itself is NOT
automatically excluded (nothing forces `exp(exp(0)) ≠ log(c)` for arbitrary `c`), so trying to
feed an open interval lemma a `z ≤ 0` (closed) membership fact failed at the boundary point.
Fixed by a genuine three-way split (`<0`, `=0`, `>0`) instead of the two-way split that sufficed
in the base case — reusing `length_le_one_of_forall_eq` (`EMLExplicitBoundGlue.lean`, built for
an unrelated purpose two entries ago) for the `=0` slice.

**Honest scope.** This is ONE compound shape, with `t2` deliberately kept simple to isolate the
"reuse a proven sub-result" mechanism from the domain-splitting problem, which remains the
substantially larger piece of the actual inductive step (compound `t2`, needing the full
"collect every internal node's critical points, refine, re-validate per piece" machinery sketched
in `EMLExplicitBoundGlue.lean`). But it is a REAL demonstration that the induction's basic
mechanism — smaller trees' bounds feeding larger trees' proofs via the chain rule — works in
practice, not just in the abstract strategy description.

`#print axioms` clean, `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`.
Full `lake build MachLib` passes (398 modules) — thirteen new files today (twelve from earlier
entries plus this one).

## 2026-07-20 (cont.) — the real domain-splitting case, finally: a compound `t2` that genuinely
## changes sign

Per continued "proceed please." Every prior result in this arc deliberately kept `t2` simple (a
leaf) specifically to dodge this problem. This entry attacks it directly, for the first time.

**Finding a tractable instance.** `t2 = eml var (const c2)` (`c2 > 1`) is compound AND genuinely
sign-changing: `t2.eval x = exp(x) - log(c2)`, strictly increasing (derivative `exp(x) > 0`
always), going from a negative limit as `x → -∞` to `+∞` as `x → ∞` — crosses zero EXACTLY once,
at `x0 = log(log c2)` (checked numerically-in-spirit before formalizing: `exp(x0) = log(c2)` by
construction, via `exp_log`). `t = eml (const c1) t2` needs its `log(t2.eval x)` branch to be
genuinely different on either side of `x0` — clamped (constant `exp c1`) below it, the true log
above — exactly the "split by sign, reduce on the bad region, bound each piece" strategy from
`EMLExplicitBoundGlue.lean`, now actually carried out rather than described.

**Why this instance stayed tractable despite being genuinely new.** On `x > x0`, `t`'s derivative
works out to `-exp(x)/(exp(x)-log(c2))` — NEVER zero (`exp(x) > 0` always; the denominator is
exactly `t2.eval x > 0` there) — so `zero_count_bound_by_deriv` applies with `N=0` directly: at
most ONE zero on `(x0,B)`, no monotonicity or second-derivative argument needed at all (simpler
than either the `eml var var` base case or last entry's compound-`t1` case). On `x < x0`, `t.eval`
collapses to the constant `exp(c1)`, never zero. The genuinely new content here was establishing
`x0` itself and the sign facts either side of it (`exp_lt` plus `exp_log` inverting `log`'s own
definition — no converse-monotonicity lemma needed), not the zero-counting technique itself.

**The result** (`eml_const_evarConstC2_boundedZeros`): `t = eml (const c1) (eml var (const
c2))`, for `c2 > 1`, has boundedly many zeros (`≤4`) on ANY interval, with NO
`EMLPfaffianValidOn` assumption anywhere — the first result in this whole arc built against a
`t2` that isn't just simple-or-collapsing but ACTUALLY switches between the clamped and
unclamped branch within the interval of interest.

**Real build friction, worth recording.** (1) `apply zero_count_bound_by_deriv (...)` unifies
cleanly against a goal of the SHAPE `∀ zeros_f, Nodup → membership → length ≤ N+1` (as when
proving a theorem whose own statement has that shape) but NOT against an already-specialized
goal like `(some specific filtered list).length ≤ K` — the fix was extracting the derivative
argument as its own standalone theorem first (mirroring `exp_expSubLog_sub_log_atMostTwoZeros_pos`
from the prior entry), then `apply`-ing THAT to the specific list, exactly the working pattern
from every prior file — a mismatch between "proving a general theorem" and "invoking one inline"
that's easy to hit and worth remembering. (2) `add_lt_add_left h (-r)` gives `-r+p < -r+q`
(constant on the LEFT of an ADDITION); what was needed was `p-r < q-r` (constant on the RIGHT of
a SUBTRACTION) — same fact, different shape, needed three times, worth a two-line reusable helper
(`sub_lt_sub_right_of_lt`) rather than re-deriving via `mach_ring` each time. (3) Deriving `X = 0`
from a hypothesis `0 - X = 0` via `mach_ring`-normalized algebra silently produced a USELESS,
trivially-true restatement rather than actually using the hypothesis, because the naive
`rw [hypothesis]`-on-the-goal approach doesn't "consume" the hypothesis's content the way
substituting it into a separately-derived identity does — fixed via `generalize` (to make the
opaque product a true atomic variable) plus the same "derive via `e := identity; rw[hyp] at e`"
pattern used successfully elsewhere in this arc, rather than trying to rewrite the goal directly.

`#print axioms` clean, `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`.
Full `lake build MachLib` passes (399 modules) — fourteen new files today.

## 2026-07-20 (cont. 2) — generalizing the domain-split instance to any `t2` with one sign crossing

Per continued "proceed please," turning the single hand-built instance above into a reusable
theorem parametrized by `t2`'s own eval/derivative/derivative-zero-count, then re-deriving the
original as a corollary to check the generalization is honest (equivalent to, not just similar
to, the hand-built result).

**The general theorem** (`eml_const_genericT2_boundedZeros`, new file
`EMLZeroCrossingDomainSplitGeneral.lean`): given `t2eval`/`t2deriv` on `(x0,b)` with `t2eval ≤ 0`
left of `x0`, `t2eval > 0` right of it, `t2eval` differentiable with derivative `t2deriv` right of
`x0`, and a bound `K` on how many places `t2deriv` itself can vanish there, `eml (const c1) t2`
has at most `K+2` zeros on any sub-interval `(a,b)` — no `EMLPfaffianValidOn` assumption anywhere.
The `+2` is exactly the same accounting as the hand-built version: at most 0 zeros left of `x0`
(clamp forces the constant `exp c1`, never zero), at most 1 at `x0` itself (list-dedup), at most
`K+1` right of it (`zero_count_bound_by_deriv` applied to `t`'s own derivative, which via the
chain rule through `log` is zero exactly where `t2deriv` is zero — reusing the caller's bound `K`
rather than re-deriving it). This is the promised shape from the prior entry's close: "any `t2`
whose own zero-crossing structure is already known/bounded reduces to the same three-way split."

**Sanity-check corollary** (`eml_const_evarConstC2_boundedZeros_via_general`): re-derives the
original hand-built `eml_const_evarConstC2_boundedZeros` (`t2 = eml var (const c2)`, `c2>1`,
bound `≤4`) by instantiating `t2eval = fun x => exp x - log c2`, `t2deriv = exp` (never zero, so
`K=0`), `x0 = log(log c2)`. Confirms the generalization is not a weaker or differently-shaped
result — it specializes exactly back to the original `≤4` bound via `K+2 = 0+2 = 2`... plus the
outer split contributes the remaining budget: the corollary further splits on `x0` vs `b`
(mirroring the general theorem's own internal split) since the general theorem's hypotheses are
only stated for the region right of `x0`, giving the full `≤4` once both the `x0<b` case (general
theorem applies directly) and the two degenerate `x0≥b` cases (whole interval left of/at `x0`,
`zeros=[]` by the same clamp argument as the general theorem's own left-side case) are combined.

**Real build friction, worth recording — three separate categories.** (1) *Same apply-vs-
specialized-goal trap as ever*, now one level deeper: even after extracting the derivative
argument as its own theorem (per the established fix), directly `apply`-ing it to a callback
inside another `apply`'s remaining goal still failed with "unsolved goals" until the derivative
fact was pulled out as a fully standalone top-level `have` (`hgt_general`) applied via full
positional arguments including nested proof terms — extracting once was not enough; the
extraction has to happen at the SAME nesting level the failure occurs at, not just once globally.
(2) *`apply` against a `∀`-quantified conclusion silently produces one goal per hypothesis in the
Pi-chain, not just the ones you expect from reading the "interesting" hypotheses* — the
corollary's `apply eml_const_genericT2_boundedZeros ...` left behind not only the five expected
goals (`hlt_side`, `hgt_side`, `hderiv`, `hderivBound`, the final membership fact) but a SIXTH,
easy to miss: `zeros.Nodup` itself (already in context as `hnd`, but `apply` doesn't consult local
context — it turns every hypothesis of the applied term's Pi-chain into a fresh goal in order,
even ones trivially satisfiable by an existing local hypothesis). Diagnosed only by reading the
exact `unsolved goals` dump and counting hypotheses in the theorem signature by hand; fixed with
one `· exact hnd` bullet inserted at the right position. (3) *Multi-line tactic application
silently truncated by indentation*: `exact absurd (foo).2.2\n    (bar)` split across two lines
parsed as `absurd (foo).2.2` (a curried function still expecting one more argument) followed by a
SEPARATE, syntactically invalid top-level command starting with `(bar)` — Lean 4's whitespace-
sensitive tactic parsing does not treat a continuation line as part of the same application
unless indentation rules are respected exactly; the fix was collapsing back onto one line rather
than debugging indentation further. (4) *Copy-adapted contradiction reused the wrong shape*: the
two degenerate boundary cases (`x0=b`, `b<x0`) were first drafted by pattern-matching against an
unrelated nearby proof shape (`absurd hyb (... lt_irrefl ...)`, i.e. trying to disprove `y<b`
itself, which is simply true and can never be a contradiction) instead of re-deriving the actual
needed fact — that `y<x0` (from `y<b` plus `b≤x0`), used exactly like the general theorem's own
left-side clamp argument, forces `t.eval y = exp c1 ≠ 0`. A reminder that "this looks like the
pattern used two cases up" is not a substitute for checking what the actual goal states.

**Honest scope note.** This result, like the prior one, still requires `t1 = const c1` — it does
NOT yet combine with the compound-`t1` inductive step from `EMLZeroCrossingDepth2Compound.lean`
two entries back. Combining "compound `t1` AND sign-changing `t2`" simultaneously remains future
work; today's generalization widens what `t2` can be (any sign-crossing eval/derivative pair with
a known derivative-zero bound), not what `t1` can be.

`#print axioms` clean on both new theorems (`eml_const_genericT2_boundedZeros` and
`eml_const_evarConstC2_boundedZeros_via_general`) — only base MachLib primitive axioms
(`propext`, `Classical.choice`, `Quot.sound`, `HasDerivAt`/Rolle/algebra machinery),
`eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`. Full `lake build MachLib`
passes (400 modules) — fifteen new files today.

## 2026-07-20 (cont. 3) — MILESTONE: both children compound at once, the two mechanisms combined
## for the first time

Per continued "proceed please." Every prior result in this arc kept ONE child simple to isolate a
single mechanism: `EMLZeroCrossingDepth2Compound.lean` allowed `t1` compound but forced `t2 =
const c`; the domain-split files allowed `t2` compound (sign-crossing) but forced `t1 = const
c1`. This entry closes the first instance where BOTH are depth-1 compound simultaneously —
exactly the combination the domain-split-general entry's "honest scope note" flagged as not yet
attempted.

**The instance** (`EMLZeroCrossingBothCompound.lean`): `t1 = eml var (const c1')`, `t2 = eml var
(const c2')`, `c2' > 1` (sign crossing, same shape as before). Genuinely new observation: `t1`
being compound does NOT complicate the LEFT region at all — on `x < x0` (`t2 ≤ 0`), `t.eval x =
exp(t1eval x) - 0 = exp(t1eval x)`, positive UNCONDITIONALLY (`Real.exp_pos`, regardless of
`t1eval x`'s actual value) — the exact same one-line "clamp forces positivity" argument as every
prior instance, with `exp c1` simply replaced by `exp(t1eval x)`. `t1`'s compoundness only bites
on the RIGHT region, where it's actually exponentiated non-trivially.

**The right region — the genuinely new computation.** `t`'s derivative there (chain + product +
sub) is `D(x) = exp(t1eval x)·exp(x) - (1/t2eval x)·exp(x)` — a genuine DIFFERENCE, not reducible
to a single scaled factor the way the const-`t1` case's derivative was (that one had `t1`
constant, so its derivative term vanished entirely, leaving only the `t2`-side term). Bounding
`D`'s zeros needed a second layer: `D(x) = 0 ↔ g(x) := exp(t1eval x)·t2eval x - 1 = 0` (clearing
denominators, valid since `exp x ≠ 0` and `t2eval x ≠ 0` on this region), and `g`'s OWN derivative
(product rule) factors cleanly as `g'(x) = [exp(t1eval x)·exp x] · (exp x - (log c2' - 1))` — a
product of a manifestly positive term and a term that is positive PROVIDED `log c2' ≤ 1` (i.e.
`c2' ≤ e`): `exp x > 0 ≥ log c2' - 1` always. Under that side condition `g` is strictly monotonic
GLOBALLY (no domain restriction needed, mirroring `t1eval`/`t2eval`'s own domain-free smoothness),
hence injective, hence has at most one zero anywhere. The `D=0 → g=0` bridge (a purely algebraic
cross-multiplication, `A·E - (1/T)·E = 0 → A·T - 1 = 0` for `E,T ≠ 0`) transfers that ≤1 bound to
`D`, and `zero_count_bound_by_deriv` (Rolle) then gives `t` itself ≤2 zeros on the right region.
Combined with 0 (left, empty) + 1 (the `x0` boundary point, list-dedup): **`t` has at most 3 zeros
on ANY interval — no `EMLPfaffianValidOn` assumption anywhere, `c1'` completely unrestricted.**

**Why `c2' ≤ e` specifically, and what it costs.** The condition makes `g`'s derivative-sign
argument a SINGLE monotonicity check. Without it (`c2' > e`), `g`'s bracket term `exp x - (log
c2' - 1)` changes sign once, making `g` itself a "valley" (decreasing then increasing) rather than
monotonic — provable via the same technique one level deeper (bound `g`'s zeros via bounding
`g'`'s sign changes, a second Rolle layer), but not attempted here. Matches this arc's established
discipline: close the tractable concrete case honestly, name the harder one precisely, don't force
it in the same sitting.

**Build friction — one real new gotcha, distinct from prior ones.** The `D=0 → g=0` algebraic
bridge (`cross_cancel_bridge`) needed the SAME `1/T`-as-opaque-atom discipline flagged repeatedly
before, but in a NEW shape: rather than a single `generalize` immediately before one `rw`, the
bridge needed the generalized atom `R` to survive through FOUR sequential steps (subtraction
rearrangement, left-multiplication by `E`, `mul_left_cancel`, then multiplication by `T` via the
ORIGINAL `hRdef : 1/T = R` equation used in REVERSE to substitute back) — confirming the
`generalize ... at hyp` pattern composes cleanly across a multi-step algebraic chain, not just a
single rewrite, as long as every intermediate step stays in terms of the same named atom rather
than re-introducing `1/T` syntactically. Otherwise: derivative/positivity/monotonicity pieces all
compiled clean on the FIRST full attempt, reusing every established pattern (extract-then-apply,
factor-then-`mul_pos`, `atMostOneZero_of_strictMono`) without new surprises — a sign the toolkit
built up across today's session has actually converged into something reusable, not just a string
of one-off tricks.

**Honest scope.** ONE concrete `t1`/`t2` shape, both `eml var (const _)`, under `1 < c2' ≤ e`
(`c1'` free). Does not touch: deeper trees on either side, the `c2' > e` sub-case, or a general
"any compound `t1` + any sign-crossing `t2`" theorem (would need `t1`'s own derivative-zero
structure abstracted as a caller-supplied parameter, mirroring how `t2` was generalized two
entries ago — a natural next step, not attempted here). `#print axioms` clean, only base MachLib
primitives (`propext`, `Classical.choice`, `Quot.sound`, `HasDerivAt`/Rolle/algebra), zero
`sorry`, `eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib`
passes (401 modules) — **sixteen new files in one session.**

## 2026-07-20 (cont. 4) — the `c2' ≤ e` restriction removed: it was never actually needed

Per continued "proceed please." Re-examined the "honest scope" gap flagged above — the `c2' > e`
sub-case, which the previous entry assumed would need a second Rolle layer ("`g` itself bounded
via a valley argument"). Checking the actual geometry first, rather than diving straight into the
harder proof, found the restriction was an artifact of proving MORE than needed, not a genuine
difficulty.

**What was actually true.** `g`'s derivative sign flips at `x1 := log(log c2' - 1)` (well-defined
only when `c2' > e`, i.e. `log c2' > 1`). The previous entry's `c2' ≤ e` restriction existed to
make the sign-check hold GLOBALLY (avoiding `x1` mattering at all). But `g` is only ever evaluated
on `(x0, b)` — the region past `t2`'s own sign crossing, `x0 = log(log c2')` — and `x1 < x0`
ALWAYS: `log c2' - 1 < log c2'` trivially, and `log` is monotonic, so `log(log c2' - 1) <
log(log c2')` whenever both are in `log`'s real domain. **The point where `g`'s derivative would
flip sign sits strictly to the LEFT of where `g` is ever actually used** — so the "valley" never
shows up in the region that matters, for ANY `c2' > 1`, not just `c2' ≤ e`. Confirmed
algebraically without needing `x1` at all: for `z > x0`, `exp z > exp x0 = log c2'` (via `exp`'s
monotonicity + `exp_log`), which by itself already forces the bracket `exp z - log c2' + 1`
positive — the SAME conclusion the `c2' ≤ e` case reached by a coarser, global argument.

**The fix** (`EMLZeroCrossingBothCompound.lean`, same file, no new file): replaced `g_deriv_pos`
(global positivity, needed `log c2' ≤ 1`) with `g_deriv_pos_right` (positivity only claimed for
`z > x0`, using `exp z > exp x0 = log c2'` directly) and `g_atMostOneZero` (global monotonicity)
with `g_atMostOneZero_right` (monotonicity restricted to `(x0, d)`, which is all
`zero_count_bound_by_deriv` ever needs). The main theorem's `hc2'le : Real.log c2' ≤ 1` hypothesis
is now GONE entirely — `eml_evarConstC1_evarConstC2_boundedZeros` holds for `c1'` completely
unrestricted and `c2' > 1` with NO upper bound, the full natural domain for this shape. Same `≤3`
zero bound as before (only the hypothesis got strictly weaker, not the conclusion).

**The lesson, worth stating plainly.** The "second Rolle layer" difficulty flagged last entry was
real IN GENERAL (bounding an arbitrary "valley" function's zeros does need one) but was never
actually TRIGGERED by this specific instance, because the region where the function is evaluated
(`x > x0`) and the region where its derivative could misbehave (`x < x1 < x0`) don't overlap. This
is a useful category to watch for going forward: before building a harder general mechanism,
check whether the SPECIFIC domain in play already sidesteps the difficulty — cheaper than the
mechanism, and sometimes (as here) the honest answer.

`#print axioms` clean (same axiom set as before — no new machinery, just a tighter hypothesis
threaded through), `eml_pfaffian_validon_from_sin_equality` does not appear, zero `sorry`. Full
`lake build MachLib` passes (401 modules, same file count — a strengthening in place, not a new
file).

## 2026-07-20 (cont. 5) — the both-compound pattern generalized, mirroring the earlier `t2`
## generalization exactly

Per continued "proceed please." With the concrete both-compound instance closed AND strengthened
to its full natural domain, the obvious next step (flagged as "not attempted" in both prior
entries) is generalizing it the same way the const-`t1` domain-split result was generalized three
entries ago: distill what actually made the instance work into a theorem parametrized by `t1`'s
own eval/derivative and `t2`'s sign-crossing structure, rather than one hardcoded shape.

**The generalization** (`EMLZeroCrossingBothCompoundGeneral.lean`,
`eml_genericT1_genericT2_boundedZeros`): takes `t1eval`/`t1deriv` (assumed known EVERYWHERE — `t1`
is only ever exponentiated, never itself under a `log`, so unlike `t2` it needs no domain
restriction at all, matching what every instance in this arc has already shown), `t2`'s
eval/derivative/sign-crossing facts exactly as before, and a caller-supplied bound `M` on the
zeros of the COMBINED raw derivative `exp(t1eval z)·t1deriv z - (1/t2eval z)·t2deriv z` — this is
the one genuinely new piece, and can't be reduced further in the abstract (unlike the const-`t1`
generalization, where the `t1`-derivative term vanished entirely, leaving a bound on `t2deriv`
alone sufficient). Result: `eml T1 t2` has at most `M+2` zeros — IDENTICAL `+2` accounting
(clamped region, switch point) to every prior domain-split theorem, confirming `t1`'s
compoundness truly never touches the left region, in full generality this time, not just for one
instance.

**Sanity-check corollary** re-derives `eml_evarConstC1_evarConstC2_boundedZeros` by supplying
`M := 1` via exactly the `g_atMostOneZero_right`/`cross_cancel_bridge` machinery already built for
the concrete instance — confirming the generalization is equivalent to, not just similar to, the
hand-built (and since-strengthened) result.

**Build friction: none new.** Compiled clean on the FIRST full attempt for both theorems — the
"extract standalone fact, apply" pattern, the "apply generates a goal per Pi-chain hypothesis
including ones in context" gotcha (correctly anticipated an `exact hnd` bullet this time, no
missed-goal surprise), and the boundary-case contradiction shape were all applied correctly from
memory of the three prior generalization rounds. A useful signal that this class of construction
("generalize a concrete domain-split instance into a theorem parametrized by the caller's own
zero-count bound, verify via a sanity-check corollary") has become a genuinely reusable recipe in
this codebase, not something that needs to be rediscovered each time.

**Honest scope.** Generalizes what `t2` and `t1`'s STRUCTURE can be (any known-derivative `t1`,
any sign-crossing `t2`), but the caller still has to supply `M` themselves — this theorem doesn't
discover `M`, it only re-packages the accounting once `M` is known. Deeper trees on either side
(where `t1`/`t2` are themselves NOT depth-1, so their own derivative structure needs its own
induction) remain the real open frontier. `#print axioms` clean on both theorems, only base
MachLib primitives, zero `sorry`, `eml_pfaffian_validon_from_sin_equality` does not appear. Full
`lake build MachLib` passes (402 modules) — **seventeen new files in one session.**

## 2026-07-20 (cont. 6) — `t1`'s derivative requirement weakened from global to local

Per continued "proceed please." Checked whether `eml_genericT1_genericT2_boundedZeros`'s
`ht1deriv : ∀x, HasDerivAt t1eval (t1deriv x) x` (required EVERYWHERE) was actually load-bearing,
the same question that removed last round's `c2' ≤ e` restriction. It wasn't: both call sites
invoke `t1`'s derivative only at points `z` already known to satisfy `x0 < z ∧ z < b` — so the
hypothesis was weakened to `∀x, x0 < x → x < b → HasDerivAt t1eval (t1deriv x) x`, matching
`t2deriv`'s own domain restriction exactly. Two call sites updated (`ht1deriv z` →
`ht1deriv z hz0 hzb`); the sanity-check corollary's `ht1deriv` bullet updated to `intro x _ _`
(its instantiation, `exp x - log c1'`, is differentiable everywhere regardless, so the extra
hypotheses are simply unused there).

**Why this is more than tidying.** `t1 = eml var var` (`t1eval x = exp x - log x`) is NOT
differentiable at `x = 0` — `log`'s right-derivative diverges as `x → 0+`, so no finite
`HasDerivAt Real.log ? 0` exists. Under the OLD global requirement, this tree could never be fed
into this theorem as `t1`, permanently — not "not yet done," but structurally excluded. Under the
new local requirement, `t1 = eml var var` qualifies fine on any `(x0, b)` with `x0 ≥ 0` (its
derivative `exp x - 1/x` is well-defined throughout `x > 0`, and `x0` itself sits OUTSIDE the open
interval `(x0, b)` where the derivative is actually needed). This doesn't yet COMBINE `eml var
var` with a compound `t2` — the combined derivative `exp(t1eval z)·t1deriv z - (1/t2eval
z)·t2deriv z` would, for this `t1`, become a genuinely new expression (`t1deriv` is no longer the
simple `exp` seen in every instance so far) needing its own fresh positivity/monotonicity
argument, not just reuse of `exp_sub_inv_atMostOneZero`'s existing bound on `t1deriv` alone — a
real, sized piece of work, correctly NOT attempted in this round. What this entry closes is
narrower and honest: the theorem no longer structurally forbids the attempt.

`#print axioms` unchanged (no new machinery, same axiom set). Full `lake build MachLib` passes
(402 modules, same file count — a strengthening in place, matching last round's pattern).

## 2026-07-20 (cont. 7) — MILESTONE: `eml var var` actually combined with a compound `t2`, the
## hardest instance in this arc so far

Per continued "proceed please," walked through the door the last entry opened rather than stopping
at "no longer structurally forbidden." `t1 = eml var var` (`t1eval x = exp x - log x`, `t1deriv x
= exp x - 1/x`) combined with `t2 = eml var (const c2')` (`c2' > 1`, the same sign-crossing shape
used throughout this arc) — new file `EMLZeroCrossingBothCompoundDeeper.lean`.

**Why this is genuinely harder, not just "one more instance."** In every prior both-compound
result, `t1deriv` was `exp`, sign-constant — so the combined derivative `D(z) = exp(t1eval
z)·t1deriv z - (1/t2eval z)·t2deriv z` inherited a clean sign structure almost for free. Here
`t1deriv z = exp z - 1/z` itself changes sign exactly once (at the transcendental Omega constant),
so a naive approach would need to case-split `D` around THAT crossing too, compounding the
domain-splitting problem this whole arc has fought.

**The finding that avoided a third split, done on paper first.** Write `D = P - R` where `P(z) :=
exp(t1eval z)·t1deriv z` and `R(z) := (1/t2eval z)·t2deriv z`. Computing each separately:

- `P'(z) = exp(t1eval z)·[(t1deriv z)² + (exp z + 1/z²)]`. The bracket is a SQUARE plus a term
  ALREADY established positive in `EMLZeroCrossingDepth1.lean` (`exp_sub_inv_deriv_pos` —
  literally `t1deriv`'s own derivative, reused directly, the actual induction mechanism at work).
  Positive regardless of `t1deriv z`'s sign — `P` is strictly increasing on `z > 0`, full stop, no
  case-split needed despite `t1deriv` itself not being sign-constant.
- `R'(z) = -log(c2')·exp(z)/(exp z - log c2')²`. Since `c2' > 1` gives `log c2' > 0`, this is
  negative throughout `z > x0` — `R` is strictly decreasing.

`D = P + (-R)`, a sum of two strictly increasing functions, hence strictly increasing itself —
injective, hence at most ONE zero, `M := 1`, EXACTLY the bound every simpler instance needed.
The apparent extra difficulty (`t1deriv`'s own sign change) turned out to not matter at all, once
the right decomposition was found — a second instance this session of "the flagged difficulty
doesn't actually bite," alongside the `c2' ≤ e` removal two entries back.

**The one genuinely new, unavoidable side condition**: `t1eval` isn't differentiable at `x = 0`,
so `x0 = log(log c2') ≥ 0` is required (`1 ≤ log c2'`, i.e. `c2' ≥ e`) — structural, not a
convenience, unlike the earlier (removed) `c2' ≤ e` restriction.

**Real build friction — one recurring, previously-unseen `mach_ring` limitation.** Twice in this
file, `mach_ring` fully expanded and combined a division-heavy expression down to a residual that
was PURE two- or three-atom commutativity (`-(A*(X*B)) = -(X*(A*B))`) and then failed to close it
— `mach_ring` normalizes and combines but does not appear to fully canonicalize multiplication
order across 3+ atoms once a `generalize`d division atom is in the mix. Fixed both times the same
way: `generalize` the division into a plain atom first (as established), let `mach_ring` do the
bulk simplification, then patch the LAST reordering step by hand via one explicit `mul_comm`/
`mul_assoc` chain. Also extracted a tiny fully-abstract helper (`sub_pos_of_pos_of_neg : 0<a →
b<0 → 0<a-b`) specifically to keep that pattern's own `mach_ring` call two-atom-only, avoiding
the same failure mode when combining `P_deriv_pos`/`R_deriv_neg` into `D_deriv_pos` — a case
where the RIGHT fix was avoiding the fragile call entirely by choosing a smaller, cleaner lemma
shape, rather than debugging the tactic further.

**Why this matters.** First result in the whole arc combining a `t1` whose OWN derivative changes
sign with a compound sign-crossing `t2` — genuinely deeper than every prior both-compound
instance, and it closed in one sitting once the `P`/`R` decomposition was found on paper. `#print
axioms` clean, only base MachLib primitives, zero `sorry`, `eml_pfaffian_validon_from_sin_
equality` does not appear. Full `lake build MachLib` passes (403 modules) — **eighteen new files
in one session.**

## 2026-07-20 (cont. 8) — the `P`-side finding generalized: convexity, not this one tree shape

Per continued "proceed please." The prior entry's core insight — `P(z) := exp(t1eval z)·t1deriv
z` is strictly increasing whenever `t1` is CONVEX (`t1deriv` itself has positive derivative),
REGARDLESS of `t1deriv z`'s own sign — never actually used anything specific to `t1 = eml var
var`. Distilled it into a standalone, `t1`-agnostic lemma (`EMLZeroCrossingConvexT1.lean`,
`expMul_atMostOneZero_of_convex`): given `t1eval`/`t1deriv`/`t1deriv2` (`t1deriv`'s own
derivative) on `(c,d)`, and `t1deriv2 > 0` there (convexity), `exp(t1eval x)·t1deriv x` has at
most one zero on `(c,d)` — a genuine, reusable real-analysis fact, not tied to `log`, `eml`, or
this investigation at all.

**Sanity check**: `EMLZeroCrossingBothCompoundDeeper.lean`'s `P_deriv_pos` re-derived
(`P_deriv_pos_via_general`) by instantiating `t1eval = exp - log`, `t1deriv = fun x => exp x -
1/x`, `t1deriv2 = fun x => exp x - (-1/(x·x))`, with convexity supplied directly by
`exp_sub_inv_deriv_pos` (already built, reused verbatim) — confirms the generalization is
equivalent to the hand-built fact.

**Why bother generalizing a `P_deriv_pos` that already worked for the one case needed.** This
mirrors the `t2`-generalization pattern from three entries back exactly: the mechanism (positive
second-derivative regardless of first-derivative sign) is the actually interesting, reusable
content — any future `t1` with a KNOWN convexity fact (not just `eml var var`) gets `P`'s ≤1-zero
bound for free, without re-deriving the square-plus-positive-term argument. Matches the toolkit's
now-established "generalize the reusable mechanism out of the concrete instance" recipe, applied
for a FOURTH time this session without needing to rediscover the approach.

**Build friction: none.** Compiled clean, first attempt, both theorems. `#print axioms` clean,
only base MachLib primitives, zero `sorry`. Full `lake build MachLib` passes (404 modules) —
**nineteen new files in one session.**

## 2026-07-20 (cont. 9) — CAPSTONE: the `R`-side generalized too, and the full "both children
## compound" theorem completed

Per continued "proceed please." Completed the other half of the `D = P - R` generalization begun
last entry, then combined both halves into the fully general "both children compound" theorem this
whole sub-arc has been building toward.

**The `R`-side condition, derived on paper.** For abstract `t2eval`/`t2deriv` (`t2deriv2` :=
`t2deriv`'s own derivative), the quotient/product rule gives `R'(z) = -t2deriv(z)²/t2eval(z)² +
t2deriv2(z)/t2eval(z)`. On `t2eval(z) > 0` this is negative EXACTLY when `t2deriv2(z)·t2eval(z) <
t2deriv(z)²` — a genuine, checkable condition on any `t2`, not tied to `exp - log c2'`. Checked
against the concrete instance (`t2deriv = t2deriv2 = exp`): the condition reduces to `exp(z)·(exp
z - log c2') < exp(z)²`, i.e. `-log c2' < 0`, i.e. `c2' > 1` — recovering the ORIGINAL
sign-crossing hypothesis exactly, for free, rather than needing a new one.

**The capstone** (`eml_convexT1_conditionT2_boundedZeros`, new file
`EMLZeroCrossingBothCompoundDeeperGeneral.lean`): combines the `P`-side (`t1` convex) and `R`-side
(`t2` satisfies the quadratic condition) results by calling `eml_genericT1_genericT2_boundedZeros`
with `M := 1` DISCHARGED AUTOMATICALLY via `D_atMostOneZero_general`, rather than left for the
caller to supply (as `eml_genericT1_genericT2_boundedZeros` itself does). This is the fully
general "both children compound" theorem: `t1` convex, `t2` sign-crossing with the condition ⟹
`eml T1 t2` has `≤3` zeros, no validity assumption, both `t1` and `t2` fully abstract functions
(not tied to any particular `EMLTree` shape). Sanity-check corollary re-derives
`eml_evarvar_evarConstC2_boundedZeros` (confirming equivalence, `t2deriv2 := Real.exp` since
`Real.exp` is its own derivative — `hasDerivAt_evarConstC` reused verbatim for that fact too).

**Build friction — two real fixes, both quick once diagnosed.** (1) `mul_neg_of_neg_of_pos` (`a<0
→ 0<b → a·b<0`) already exists in the codebase (`SturmNonOscillation.lean`) but isn't reachable
transitively from this file's import chain — rather than pull in an unrelated branch of the
codebase for one three-line fact, re-derived it locally (`neg_pos_of_neg` + `mul_pos` + `neg_mul`
+ `neg_neg_of_pos` + `neg_neg_helper`, all already reachable). (2) The `R`-side's own
`generalize`-then-`mach_ring` step, expected (from the prior entry's identical-looking pattern) to
need a manual commute patch, actually closed FULLY on `mach_ring` alone this time — the earlier
manual-patch code caused an "no goals to be solved" error when left in place. Removed it. Useful
correction to the working assumption from last entry: `mach_ring`'s ability to close a
post-`generalize` goal isn't a fixed property of "does it involve a generalized division atom" —
it depends on the SPECIFIC term shape, so the safe move is trying `mach_ring` alone FIRST and only
adding the manual patch if it actually leaves a residual, not assuming the patch is needed
up front.

**Why this matters.** This closes the "both children compound" arc that opened with today's
concrete instance, ran through strengthening (dropping `c2'≤e`) and one level of generalization
(any sign-crossing `t2`, `t1` still `const c1`), then a genuinely deeper concrete instance
(`eml var var`), and now arrives at the natural capstone: a single theorem taking ONLY the two
mathematically meaningful conditions (`t1` convex, `t2`'s quadratic-type condition) and delivering
the zero-count bound, with every concrete instance built today reducible to a corollary. `#print
axioms` clean on both new theorems, only base MachLib primitives, zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib` passes (405
modules) — **twenty new files in one session.**

## 2026-07-20 (cont. 10) — MILESTONE: the first genuinely depth-3 tree, closed almost entirely by
## reuse

Per continued "proceed please." The capstone theorem (`eml_convexT1_conditionT2_boundedZeros`)
takes `t1eval`/`t1deriv`/`t1deriv2` as fully ABSTRACT functions — meaning nothing in its statement
requires `t1` to be depth-1. Checked directly whether a genuinely DEEPER `t1` could be fed in
using only already-proven facts, rather than assuming new machinery was needed.

**The observation that made this nearly free.** `T1 := eml (eml var var) (const c)` — `T1`'s own
left child IS `eml var var`, the tree studied since the base case — has `T1.eval x = exp(t1'.eval
x) - log c` where `t1' := eml var var`. Its derivative is `T1deriv(x) = exp(t1'.eval x)·t1'deriv
x`. **This is LITERALLY `P(x)` from `EMLZeroCrossingConvexT1.lean`** — the exact function that
file's `hasDerivAt_expMulDeriv`/`expMulDeriv_pos_of_convex` already fully characterize. So `T1`'s
OWN convexity (`T1deriv`'s derivative positive, exactly what
`eml_convexT1_conditionT2_boundedZeros` needs to accept `T1`) is `expMulDeriv_pos_of_convex`
applied to `t1'`'s already-established facts (`hasDerivAt_exp_sub_log`, `hasDerivAt_exp_sub_inv`,
`exp_sub_inv_deriv_pos` — all from the DEPTH-1 base case, two entries ago) — NO new positivity
argument anywhere. The only genuinely new content is `T1eval`'s own `HasDerivAt` fact (`exp∘t1'eval`
minus the constant `log c`) — a three-line chain-rule-then-subtract lemma
(`hasDerivAt_expSubLogSubLogC`), reusing the SAME `exp∘t1'eval` chain-rule step
`hasDerivAt_expMulDeriv`'s own proof already performs internally.

**The result** (`EMLZeroCrossingDepth3Compound.lean`,
`eml_evarvarConstC_evarConstC2_boundedZeros`): `eml (eml (eml var var) (const c)) (eml var (const
c2'))` — a GENUINELY depth-3 tree — has at most `3` zeros on any interval, for ANY `c` and `c2' >
1` with `1 ≤ log c2'` (`c2' ≥ e`, the SAME structural requirement `eml var var` has needed since
two entries ago — unchanged by going one level deeper). NO `EMLPfaffianValidOn` assumption
anywhere. Compiled clean on the FIRST attempt — direct confirmation that today's toolkit actually
composes across depth, not just across sibling shape variations.

**Why this matters more than the numeric bound.** Every prior result in this whole arc combined
depth-1 pieces. This is the first time a tree ONE LEVEL DEEPER than every component built so far
closes using ALMOST NO new mathematical content — a genuine instance of "the induction actually
inducting": `T1`'s own zero-crossing/convexity facts, established at an earlier depth, feed
directly into the machinery built for THAT depth, without needing to re-derive anything about
`T1`'s internal structure. This is the shape the whole arc's "the induction" language has pointed
toward since the base case closed.

**Honest scope.** `T2` stays depth-1 (`eml var (const c2')`) — going deeper on `T2` as well (or
combining two independently-deep sides) is not attempted. The pattern demonstrated here — "check
whether a deeper instance is already covered by an abstract theorem before assuming new machinery
is needed" — is itself the transferable lesson, not a claim that ALL deeper trees are this cheap;
this one happened to be because `T1`'s derivative reduced EXACTLY to an already-characterized
function. `#print axioms` clean, only base MachLib primitives, zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib` passes (406
modules) — **twenty-one new files in one session.**

## 2026-07-20 (cont. 11) — a materially sharper reframing of "the hard stuff": is every bounded
## EML tree constant?

Per direct request to start on "the separate larger undertaking" — the general case beyond
today's zero-crossing arc. Before writing any Lean, re-read this document's own earlier sections
(pre-dating today) carefully enough to check whether today's work actually narrows the ACTUAL open
residual, rather than assuming it does.

**The correction, found by checking, not assuming.** The residual needs a tree `T1` that is (a)
bounded ABOVE, (b) non-constant, (c) NOT `RightChildrenSimplePositive` (has a compound right child
somewhere) — `RightChildrenSimplePositive` `T1` and unbounded-above `T1` are BOTH already closed
elsewhere in this arc (`eml_depth2_witness_of_const_gt_one_sibling_simple_T1`,
`eml_depth2_witness_of_const_sibling_unbounded_T1`). Checked every concrete `T1` shape built in
today's whole zero-crossing arc (`eml var var`, `eml (eml var var) (const c)`, etc.) against this:
EVERY one of them is UNBOUNDED ABOVE (the outer `exp(...)` always dominates) — meaning today's
entire session, however genuine as real-analysis, sits inside the region ALREADY closed by the
much simpler growth argument. It does not narrow the open residual at all. Recorded here so this
doesn't get re-discovered the hard way by whoever picks this up next.

**What actually would narrow it, checked against the one known bounded example.**
`WitnessResidualCancellation.lean`'s counterexample (`eml var (eml (eml var (const (exp K)))
(const 1))`, evaluating to the exact constant `K`) is the ONLY bounded, non-`RightChildrenSimple
Positive` tree built anywhere in this multi-day investigation — and it's EXACTLY constant, not
genuinely non-constant. Generalized it (`WitnessResidualCancellationGeneral.lean`,
`eml_cancellation_general`): for literally ANY tree `A` and ANY real `c0`, `eml A (eml (eml A
(const (exp c0))) (const 1))` evaluates to EXACTLY `c0`, everywhere — the SAME two-layer
`log∘exp=id` telescope, with `A` substituted for `var` throughout (checked, not assumed: the proof
is a direct generalization of `cancellation_theorem`'s own three-line argument). The right child
of the outer node is NEVER a bare leaf in this family, so EVERY instance is checkably outside
`RightChildrenSimplePositive` — and every instance is ALSO checkably constant. Sanity-check
corollary re-derives the original `A = var` instance as a special case.

**The sharper question this motivates.** Every construction mechanism actually available lands on
a constant. This raises a materially higher-leverage question than "extend the zero-crossing
induction": **is EVERY bounded (above) EML tree necessarily constant?** If TRUE, the residual's
own hypothesis (bounded, non-constant) is VACUOUS — closing the entire axiom outright, without
touching `sin`/`log(c2+sin x)` at all. If FALSE, an explicit counterexample sharply narrows the
true residual to whatever mechanism produces it. Either answer is decisive, unlike most of this
arc's incremental narrowing.

**A genuine proof attempt, and the precise place it stalls (not glossed over).** Tried the natural
induction on tree depth: for `T1 = eml A B`, IF both `A` and `B` are individually bounded above,
the inductive hypothesis (strictly smaller depth) forces BOTH constant, so `T1` is trivially
constant too — this case is easy. The actual content is when `A` and/or `B` is individually
UNBOUNDED yet `T1` stays bounded (exactly the cancellation phenomenon). Tried the case `A`
constant `= a`, `B` unbounded, `T1 = exp(a) - log(B.eval ·)` bounded: this needs `log(B.eval x)`
bounded — but `log`'s clamp means this does NOT force `B.eval x` bounded as a real-valued
function. `B` can be UNBOUNDED BELOW arbitrarily (contributing `log = 0` there, hence NOTHING to
`T1`'s value) while behaving however it likes on that region — and wherever `B.eval x > 0`, `T1`'s
boundedness only constrains `B` LOCALLY (bounded and bounded-away-from-zero ON that region, not
globally). **This means "is `T1` constant" genuinely depends on `B`'s LOCAL behavior split across
regions, not a single global bounded/unbounded dichotomy** — a materially different (and harder)
shape of argument than every case-split this whole arc has used elsewhere (which have all been
GLOBAL dichotomies: `c2≤1` vs `c2>1`, unbounded vs not, simple vs compound). This is a genuinely
new obstacle, not previously identified anywhere in this document, and it is NOT resolved here.

**Honest assessment, matching this document's own standard.** This is real progress: a checked
generalization (not just an isolated instance), and a materially sharper, potentially
axiom-closing question, with the FIRST concrete diagnosis of why a naive induction doesn't
immediately close it (the local/global split above). It is NOT a proof, and no counterexample was
found despite a real attempt to construct one (every natural perturbation of the cancellation
recipe either broke boundedness outright or collapsed back to another exact constant). Whoever
continues this should start from the local/global obstacle above, not re-attempt the same global
dichotomy that already failed here. `#print axioms` clean on the new theorem, only base MachLib
primitives (`propext`, `Classical.choice`, `Quot.sound`, plus foundational `exp`/algebra — notably
NO `HasDerivAt`/Rolle machinery needed at all for this piece, it's pure algebra), zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib` passes (407
modules) — **twenty-two new files in one session.**

## 2026-07-20 (cont. 12) — MILESTONE: the "bounded ⟹ constant" conjecture is FALSE — an explicit,
## fully verified counterexample

Per continued "proceed please," pursued the question raised last entry. Worked the construction
out completely on paper first, checked it numerically (`python3`, `c=2`) BEFORE writing any Lean —
per this project's established discipline — then formalized it in full, including strict
monotonicity via the derivative.

**The tree**: `T1 := eml var (eml (eml var (const 1)) (const c))`, for `1 < c < e`. Unfolds to
`T1.eval x = exp(x) - log(exp(exp(x)) - log c)`.

**Why it's bounded, both directions, uniformly (not asymptotically).** Write `w := exp(exp(x))`,
always `> 1`. Both bounds reduce to trivial facts by applying `exp` (strictly increasing) to a
candidate inequality and using `exp∘log = id`:
- Lower (`T1.eval x > 0`): reduces to `0 > -log c`, i.e. `log c > 0` — true since `c > 1`.
- Upper (`T1.eval x < -log(1-log c)`): reduces, after multiplying through by `exp(exp x)` and
  using `exp(log(1-log c)) = 1-log c`, to `1 < exp(exp x)` — always true.

Numerically verified first (`c=2`: values run from `≈1.166` at `x=-5` down toward `0` as
`x→+∞`, staying below the bound `≈1.181`) — the numeric check caught nothing wrong, but running
it before formalizing (rather than after) is the discipline that matters.

**Why it's non-constant — strictly, via the derivative, not just a two-point check.** A first
attempt tried "just compare `T1.eval 0` and `T1.eval 1`" as a cheap non-constant witness — this
does NOT work as a cheap shortcut: both bounds are compatible with either value, so a genuine
quantitative argument is needed regardless. Went straight to the derivative instead:
`T1'(x) = -exp(x)·log(c) / (exp(exp(x)) - log c)` — strictly negative everywhere (numerator and
denominator both positive, `c > 1`) — giving `T1` STRICTLY DECREASING on all of `ℝ`, hence
non-constant AND injective, via `strictAnti_of_deriv_neg` (MVT-based, already in the codebase).

**A real, previously-unflagged `mach_ring` limitation, pinned down precisely this time.**
`mach_ring` reliably fails — not sometimes, reliably — on any goal where a sub-expression (bare
variable OR product) must be recognized as the SAME quantity after appearing multiplied into a
larger product on one side of an equation and standing separately on the other — e.g. `a*b + (-b
+ -(a*b)) = -b` fails, but the syntactically-identical-after-substitution `X + (-b + -X) = -b`
(with `X` a genuinely free variable from the theorem's own binders) succeeds. Confirmed this isn't
fixed by `generalize` first either — the post-`generalize` goal LOOKS identical to the
free-variable version but still fails, meaning `mach_ring`'s difficulty tracks something about
*how* a term entered the context, not just its printed shape. The reliable fix, applied
throughout this file: never let `mach_ring` see a repeated non-atomic sub-term inside a
multi-term sum or a multiply-then-regroup identity — perform the regrouping via explicit
`rw [mul_comm, mul_assoc, ...]` first, and use `mach_ring` only for pure distribution or 2-term
cancellation (both confirmed reliable via isolated tests before use). Two small, fully general,
`mach_ring`-free helper lemmas (`neg_lt_neg_local`, `sub_lt_sub_left_local`) built once and reused
throughout, rather than re-deriving the same cancellation ad hoc at each call site.

**What this settles, and what it doesn't.** The witness-finding residual's hypothesis ("`T1`
bounded above and non-constant") is confirmed NON-VACUOUS — the conjecture from last entry is
FALSE, refuted by an explicit, compiled, axiom-checked example. This does NOT close the residual
— this is one family, not every possible bounded non-simple tree — but it answers the "is it even
possible" question decisively, and does so with a MUCH stronger result than needed (full strict
monotonicity, not just non-constancy).

**The natural next step, sketched but not yet formalized.** `T1` being strictly monotonic makes it
INJECTIVE — takes each value at most once. `log(c2+sin x)` is `2π`-PERIODIC, hence NOT injective
for any non-constant case (`sin(x) = sin(x+2π)` for all `x`). An injective function cannot equal a
non-injective one globally. So THIS PARTICULAR counterexample, despite refuting the general
conjecture, is immediately ruled out as a witness-finding obstruction by a simple
injectivity/periodicity mismatch — no zero-counting needed at all. Not formalized this round;
a natural, well-scoped next piece for whoever continues (formalize `sin`'s periodicity gives
non-injectivity of the shifted target, then the injective-vs-non-injective contradiction directly).

`#print axioms` clean on all new theorems (including the full strict-monotonicity result), only
base MachLib primitives (`HasDerivAt`/Rolle/algebra — no encoder/chain/validity machinery
anywhere), zero `sorry`, `eml_pfaffian_validon_from_sin_equality` does not appear. Full
`lake build MachLib` passes (408 modules) — **twenty-three new files in one session.**

## 2026-07-20 (cont. 13) — the loop closed: this counterexample is harmless, formalized

Per continued "proceed please." Formalized the sketch from the end of the previous entry — cheap,
as anticipated, no new mechanism needed.

**The argument.** `boundedNonConstantWitness c` is strictly monotonic
(`boundedNonConstantWitness_strictAnti`), hence INJECTIVE — takes each value at most once.
`log(c2+sin x)` takes the SAME value at `x=0` and `x=π` (`sin 0 = sin π = 0`, both axioms already
in `Trig.lean`, so both give `log(c2+0)`) — it is NOT injective, for any `c2`. An injective
function cannot equal a non-injective one globally: assume `T1.eval x = log(c2+sin x)` for all
`x`, specialize at `0` and `π`, get `T1.eval 0 = T1.eval π` (both equal `log(c2+0)`) — contradicts
`T1.eval π < T1.eval 0` from strict monotonicity (`0 < π`, `pi_pos` already in `Trig.lean`).
Four lines once the pieces existed.

**What this closes, precisely.** `boundedNonConstantWitness_ne_shifted_sin_target`: for `1 < c <
e`, this specific counterexample tree can NEVER satisfy the witness-finding residual's collapsed
equation, for ANY `c2`. No zero-counting, no Pfaffian chain, no `combinedBoundE`, no target-shift
trick — the whole apparatus this arc built machinery for turned out unnecessary for this
particular instance. This is a genuinely different, MUCH CHEAPER closure mechanism
(injectivity/periodicity mismatch) than everything else in this document, worth remembering as a
first check for any FUTURE candidate counterexample before reaching for the heavier machinery.

**Honest scope, unchanged.** This closes ONE family (this `boundedNonConstantWitness` shape), not
the residual in general — the open question is whether EVERY bounded, non-constant,
non-`RightChildrenSimplePositive` tree is similarly strictly monotonic (in which case THIS
elementary argument would close the whole residual outright, a genuinely exciting possibility not
yet checked), or whether some other such tree is NOT monotonic (needing the heavier zero-counting
machinery after all). Not determined here — a precise, well-posed next question for whoever
continues.

`#print axioms` clean, only base MachLib primitives plus the two already-existing `sin`/`pi`
axioms (`sin_zero`, `sin_pi`, `pi_pos` — nothing new), zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib` passes (408
modules, same file extended) — still twenty-three files today, one theorem added.

## 2026-07-20 (cont. 14) — MILESTONE: answering "is every such tree monotonic" — NO, decisively,
## with a fully verified counterexample

Per direct request to attack this exact research question. Worked the answer out ENTIRELY on
paper first (numerically checked with `python3` at every stage before writing a line of Lean),
then formalized completely — including the boundedness half, which took a real correction
mid-derivation (an initial "paper" step conflated an inequality with an equality; caught before
formalizing by re-deriving carefully, not by a failed Lean proof).

**The tree**: `T := eml var (eml (eml var (const 1)) (eml var (const (1+1))))` — `T`'s right
child `B` has its OWN right child `D = eml var (const (1+1))` that genuinely crosses zero,
triggering `log`'s clamp. This is the key structural difference from every prior instance this
session built (all of which kept every internal log-argument permanently positive or permanently
non-positive) — and it's exactly what breaks monotonicity.

**The exact sign characterization — no derivatives, no numerics, needed at all.** Write
`x0 := log(log(1+1))` (where `D` crosses zero) and, for `x > x0`, `v := exp(x) - log(1+1) = D.eval
x > 0`. Two ONE-STEP facts, both proved by applying `exp` (strictly increasing) to the candidate
inequality and using `exp∘log = id`:
- `v > 1 ⟹ T.eval x > 0`
- `0 < v < 1 ⟹ T.eval x < 0`

Combined with `T.eval x = 0` exactly for `x ≤ x0` (the clamped region — `log(exp(exp x)) = exp x`
cancels cleanly), three points give a `flat → down → up` VALLEY: `x_a := x0` (`T=0`), `x_b` with
`v=1/(1+1)` (`T<0`), `x_c` with `v=1+1` (`T>0`), `x_a<x_b<x_c`. `T(x_a)>T(x_b)` refutes
monotone-increasing; `T(x_b)<T(x_c)` refutes monotone-decreasing — simultaneously, no derivative
of any kind, no interval-wide argument, just three explicit point evaluations via the exact
characterization above.

**Boundedness — the part that needed real care, and where the correction happened.** An initial
attempt at a uniform upper bound tried to show `exp(exp x) - D = exp(D)` EXACTLY — this is FALSE
(`exp(D) > D` always, by `exp_grows_strictly_thm`, so the two sides can never be equal). Caught by
re-deriving the chain by hand a second time before writing Lean, not by a failed compile. The
CORRECT chain is a pure INEQUALITY throughout: `log D < D` (`log_lt_self_of_pos`) gives `exp(exp
x) - D < exp(exp x) - log D`; separately, `exp(exp x) = (1+1)·exp D` (`exp_add` + `exp_log`)
combined with `D < exp D` gives `exp D < exp(exp x) - D`; chaining gives `exp D < exp(exp x) -
log D`, hence (`log_lt_log` + `log_exp`) `D < log(exp(exp x) - log D)`, hence `T.eval x < exp x -
D = log(1+1)` — a UNIFORM bound across every real `x`, not an asymptotic or numerically-estimated
one, and needing no transcendental critical point (unlike an earlier, abandoned attempt at the
TIGHT bound, which does need one — the loose bound sufficed and stayed fully elementary).

**Two more build-friction items, both quick once found.** `set` is unavailable in this codebase
(re-confirmed, already known) — used explicit full expressions throughout instead of a local
abbreviation, at some cost to readability but zero cost to correctness. And two small, fully
general, `mach_ring`-free algebraic helpers needed building (`add_sub_cancel_right_local`,
`sub_self_sub_local`, `two_mul_eq_add_self`) — the by-now-established workaround pattern for
`mach_ring`'s specific reordering gap, applied a fourth time today without needing to
rediscover the diagnosis.

**The result** (`bounded_nonmonotonic_eml_tree_exists`): `nonMonotonicWitness` is bounded above by
`log(1+1)` EVERYWHERE and monotonic in NEITHER direction — a complete, airtight, fully verified
counterexample. **This decisively answers last entry's open question: NO, the cheap
injectivity/periodicity closure does NOT generalize to the whole residual.** Some bounded,
non-`RightChildrenSimplePositive` EML trees genuinely oscillate, so ruling out this whole class
(if possible) needs the heavier zero-counting machinery built earlier in this arc — there is no
universal shortcut.

**Honest scope, precisely stated.** This closes the QUESTION (not the residual itself) — it shows
the easy path doesn't exist in general, it doesn't newly close or newly obstruct the axiom. What
it DOES give whoever continues: a concrete, verified example of exactly the kind of non-monotonic
bounded behavior the heavier machinery needs to handle, useful as a test case for any future
zero-counting attempt on this specific residual.

`#print axioms` clean on every new theorem including the packaged final result, only base
MachLib primitives — notably NO `HasDerivAt`/Rolle machinery anywhere in this whole file, pure
algebra throughout (the same was true of the previous two entries too) — zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib` passes (409
modules) — **twenty-four new files in one session.**

## 2026-07-20 (cont. 15) — the mirror closure built, and it retroactively defangs last entry's
counterexample: `nonMonotonicWitness` turns out to be unbounded BELOW

**The question.** `EMLSmoothness.lean` already has a free, unconditional closure for `T1`
unbounded ABOVE (`eml_depth2_witness_of_const_sibling_unbounded_T1`, any `c2`). Does a MIRROR
closure exist for `T1` unbounded BELOW? And if so — does `nonMonotonicWitness` (last entry's
hard-won, genuinely non-monotonic counterexample) actually satisfy ITS hypothesis, given its
formula blows up near the clamp boundary `x0` on informal inspection (`D.eval x → 0⁺` as `x →
x0⁺`, so `log D → -∞`, so `T.eval x → -∞`)?

**The mirror closure, built** (`WitnessResidualUnboundedBelow.lean`,
`eml_depth2_witness_of_const_sibling_unbounded_below_T1`). Same collapse equation as the original
(`S3 ≤ 0` everywhere ⟹ `exp(T1.eval x) - c2 = sin x` for all `x`), but reading it through
`neg_one_le_sin` instead of `sin_le_one`: `exp(T1.eval x) ≥ c2 - 1` for ALL `x`. For `T1`
unbounded below, pick `x` with `T1.eval x < log(c2-1)` — `exp`'s strict monotonicity
(`Real.exp_lt`) plus `Real.exp_log` gives `exp(T1.eval x) < c2-1`, directly contradicting the
lower bound. Needs `c2 > 1` explicitly (unlike the original, which needs no `c2` constraint at
all) — but that's exactly the residual's own regime, so the constraint costs nothing. Same
elementary-growth flavor, no zero-counting, `#print axioms` clean (base primitives only).

**Is `nonMonotonicWitness` actually unbounded below? Yes — formally confirmed, not just
informally.** Built an explicit, closed-form witness for every target `M` (no limits, no
continuity machinery): choose `d := exp(-(exp(K-M)) - log(1+1))` where `K := log(1+1)+1`
(algebraically forced into `(0,1)` since its defining exponent is manifestly negative), then
`x := log(log(1+1)+d)` makes `D.eval x = d` EXACTLY (`exp_log` inverts the outer `log`
cleanly). From there: `B.eval x = exp(exp x) - log d > -(log d)` (dropping the positive
`exp(exp x)` term), and unwinding `log d = -(exp(K-M)) - log(1+1)` via `log_exp` shows
`-(log d) = exp(K-M) + log(1+1) > exp(K-M)`, so `log(B.eval x) > log(exp(K-M)) = K-M`
(`log_lt_log` twice). Chaining: `T.eval x = exp x - log(B.eval x) < K - (K-M) = M`. Pure algebra,
one witness per `M`, `#print axioms` clean
(`WitnessResidualNonMonotonic.lean:nonMonotonicWitness_unbounded_below`).

**The loop closed** (`WitnessResidualNonMonotonicClosesBelow.lean`,
`nonMonotonicWitness_closes_via_unbounded_below`): feeding `nonMonotonicWitness_unbounded_below`
into the new mirror closure shows `nonMonotonicWitness` can NEVER be the `T1` of a genuine
witness-finding counterexample, for any `c2 > 1` and any `S3` — exactly mirroring how
`boundedNonConstantWitness` (cont. 13) was shown harmless via injectivity/periodicity instead.

**What this actually settles — read carefully.** This does NOT reverse cont. 14's answer to "is
every bounded tree monotonic" (still NO — `nonMonotonicWitness` genuinely is bounded above and
non-monotonic, that finding stands untouched). What it adds is a SHARPER classification: bounded
above alone is not enough to threaten closure, and neither is non-monotonicity alone — the
counterexample also needs to be bounded BELOW, and the one built last round is not. Combined
with the original theorem, the surviving open territory for the whole witness-finding residual
narrows to exactly: **`T1` bounded in BOTH directions, non-constant, non-`RightChildrenSimplePositive`,
AND non-monotonic** (monotonic-but-bounded is already closed via injectivity/periodicity, per
cont. 13). No tree meeting all four conditions has been found or ruled out yet — this is now the
precise target for anyone continuing this arc.

**mach_ring, a genuinely surprising isolation gap, diagnosed and worked around again.** The exact
shape `c2 + (E - c2) = E` (used successfully at `EMLSmoothness.lean:2294`) FAILS `mach_ring` in
total isolation (`example (c2 E : Real) : c2 + (E - c2) = E := by mach_ring` leaves `c2 + (E + -c2)
= E` unsolved) — even importing the exact same file. Reproducing the FULL surrounding proof
context (extra unrelated hypotheses `hx`/`h2`/`h3` in scope from `add_le_add_left`) makes it
close again, with no other change. Root cause not tracked down (plausibly `ac_rfl`'s AC-normal-form
search behaving differently depending on ambient discrimination-tree state) — but the practical
lesson is now doubly confirmed: don't trust `mach_ring` in a from-scratch isolated test as a
verdict on whether it'll work in the REAL proof; when in doubt, reproduce the actual surrounding
context before concluding it's a dead end.

`#print axioms` clean on all three new theorems (`eml_depth2_witness_of_const_sibling_unbounded_below_T1`,
`nonMonotonicWitness_unbounded_below`, `nonMonotonicWitness_closes_via_unbounded_below`) — only
base MachLib primitives, `propext`/`Classical.choice`/`Quot.sound`, no `HasDerivAt`/Rolle, zero
`sorry`. Full `lake build MachLib` passes (411 modules) — **twenty-seven new files in one
session.**

## 2026-07-20 (cont. 16) — the THIRD free closure, generalized: any strictly monotonic `T1`
closes, unconditionally — the residual is now a fully general four-property characterization

**The observation.** `boundedNonConstantWitness_ne_shifted_sin_target` (cont. 13) showed one
SPECIFIC tree can't satisfy the collapsed witness-finding equation, via injectivity (strict
monotonicity) vs. periodicity (`sin 0 = sin π = 0`, so `log(c2+sin x)` repeats). Rereading that
proof: it never used anything about the SPECIFIC tree at all — only that it was strictly
monotonic. That means it was always a general theorem wearing a specific instance's clothes.

**Generalized and proven directly from the raw tree hypothesis**
(`WitnessResidualStrictMonoT1.lean`, `eml_depth2_witness_of_const_sibling_strictMono_T1`): for
ANY `T1` strictly monotonic (increasing or decreasing), the usual `S3≤0`-collapse
(`exp(T1.eval x)-c2=sin x` for all `x`) evaluated at `x=0` and `x=π` forces `exp(T1.eval
0)=exp(T1.eval π)=c2` — via `exp`'s injectivity (from `exp_lt` via trichotomy, no separate
injectivity lemma needed) this gives `T1.eval 0=T1.eval π`, directly contradicting strict
monotonicity since `0<π`. **Notably needs NO constraint on `c2` at all** — stronger in that
respect than either unboundedness closure (both need `c2>1` in some form). Sanity-check
corollary (`boundedNonConstantWitness_closes_via_strictMono`) re-derives the ORIGINAL cont-13
closure directly from this general theorem, confirming equivalence not just resemblance.

**What this means for the residual — now the fourth member of the `eml_depth2_witness_of_const_
sibling_*_T1` family, and the classification is COMPLETE, not partial.** Three closures now
cover: unbounded above (any `c2`), unbounded below (`c2>1`), strictly monotonic in either
direction (any `c2`). Combined, the witness-finding residual's surviving open territory is now
provably EXACTLY: **`T1` bounded in BOTH directions, non-constant, non-
`RightChildrenSimplePositive`, and NOT strictly monotonic in either direction.** This is no
longer "no known closure happens to cover this tree" — it's "no closure mechanism found so far
CAN cover any tree with these four properties, provably, since all three free mechanisms are now
stated in full generality, not as one-off instances." `nonMonotonicWitness` (cont. 14) is
exactly the shape of tree this residual describes — bounded above, provably NOT bounded below
(cont. 15) is irrelevant to this classification since it already fails at "not monotonic" too
(it's not even weakly monotonic) — the honest remaining open question is whether ANY tree is
simultaneously bounded BOTH directions and non-monotonic; `nonMonotonicWitness` itself doesn't
qualify (fails bounded-below), so it remains an open search, not a settled counterexample.

`#print axioms` clean on both new theorems — the general closure uses only base primitives (pure
algebra, same flavor as the two unboundedness closures); the sanity-check corollary naturally
pulls in `HasDerivAt`/`rolle_ct` (inherited from `boundedNonConstantWitness`'s own
strict-monotonicity proof, not from the new theorem itself). Zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` doesn't appear. Full `lake build MachLib` passes (412
modules) — **twenty-eight new files in one session.**

## 2026-07-20 (cont. 17) — testing the residual's edges by construction; a real generalization
found, a bigger structural question named but not attempted

**The question this round actually asked.** With the residual now EXACTLY characterized (T1
bounded both directions + non-constant + non-simple + non-monotonic), the natural next move is
to either FIND a tree meeting all four, or find evidence none exists. Explored on paper (not all
formalized): tried several hand constructions attempting to make `nonMonotonicWitness`'s clamp-
triggered blow-up "cancel" instead of diverge — e.g. wrapping the blow-up in a further `exp`
(makes it worse, doubly-exponential), trying to match growth rates between two branches sharing
the same crossing quantity (`exp` of a diverging quantity always dominates any competing `log`
term additively, never balances it — checked concretely for several shapes). No cancellation
construction found; every attempt diverges in one direction or the other, same as
`nonMonotonicWitness` itself. **This is evidence, not a proof** — a real structural obstruction
kept reappearing (any further composition of a genuine log-blow-up never re-bounds it via the
`exp(t1)-log(t2)` grammar), but it wasn't formalized as a general claim this round.

**One separate, genuinely interesting finding along the way, not pursued further**: non-
monotonicity does NOT require a clamp/crossing at all. `T := eml var (eml var (const 1))`
(`T.eval x = exp(exp x) - x`) has derivative `exp(exp x)·exp(x) - 1`, negative as `x→-∞` and
positive as `x→+∞` — a genuine sign change with NO log-clamp anywhere in the tree (`eml var
(const 1)`'s own right child, `const 1`, never crosses zero). Purely a GROWTH-RATE competition
between `exp(exp x)` and `x`. Not formalized (not needed — this tree is unbounded above, so it
already closes via the existing unbounded-above theorem regardless of monotonicity), but worth
recording: "non-monotonic" and "has an internal crossing" are NOT the same property, even though
every counterexample built so far in this arc happens to use a crossing.

**What WAS formalized: a genuine generalization, not just more exploration**
(`WitnessResidualDirectCrossingUnboundedAbove.lean`, commit `9c08c0c3`). `nonMonotonicWitness`'s own
inner subtree `B := eml (eml var (const 1)) (eml var (const 2))` diverges to `+∞` near its right
child's crossing point — but nothing in that argument used `B`'s specific left child at all, only
`exp(anything) > 0`. Generalized: `eml_unbounded_above_of_direct_crossing` — `eml P (eml var
(const c))` is unbounded above for ANY `P` and ANY `c > 1`, same explicit closed-form witness
technique as cont. 15 (`x := log(log c + d)` makes the crossing's value exactly `d`, chosen small
enough that `-log d` exceeds any target `M`). Combined with the existing unbounded-above closure:
`eml_depth2_witness_of_direct_crossing_T1` — the WHOLE FAMILY of trees shaped `eml P (eml var
(const c))`, for ANY `P` and ANY `c > 1`, can never be a real witness-finding counterexample. Not
one hardcoded instance (as `nonMonotonicWitness`'s own inner `B` was) — the whole shape.

**Honest scope, precisely stated.** This closes the "crossing directly under the root" case in
full generality — a genuine broadening from "we checked ONE P" to "ANY P, provably." It does NOT
touch crossings buried DEEPER (like `nonMonotonicWitness`'s own two-level nesting) in general —
that needs tracking a LOCAL blow-up near a specific finite point combined with the outer
wrapper's local boundedness THERE, which in turn would need some notion of "EML tree
continuous/bounded near a point" not yet built in this codebase. Named as the natural next
structural target, not attempted: an induction on "crossing depth" (distance from the crossing
to the tree's root) alternating unbounded-above/unbounded-below at each wrapping layer, which —
if it went through — would settle the whole conjecture (crossing anywhere ⟹ unbounded somewhere
⟹ the open residual class is EMPTY) rather than just narrowing it further. Realistically a
multi-session undertaking, matching the scale the original 2026-07-15 doc always flagged for full
generality.

`#print axioms` clean on both new theorems, only base MachLib primitives, no `HasDerivAt`/Rolle,
zero `sorry`. Full `lake build MachLib` passes (413 modules) — **twenty-nine new files in one
session.**

## 2026-07-20 (cont. 18) — the "wrap once more" lemma actually built: `nonMonotonicWitness`'s
own mechanism generalized to arbitrary `A` and `P`

**The gap cont. 17 named.** The direct-crossing lemma (`eml P (eml var (const c))` unbounded
above, any `P`) generalized depth-1. `nonMonotonicWitness` itself sits at depth 2 — one more
`eml A (...)` wrap around exactly that shape. Generalizing THAT wrap seemed to need a general
"EML tree continuous/bounded near a point" theory, flagged as a real, not-yet-built piece of
infrastructure.

**The way around it, found this round** (commit `c2447a48`): don't build general continuity — use an EXPLICIT,
checkable hypothesis instead, stated along the SAME witness path the construction already uses.
`WitnessResidualWrappedCrossingUnboundedBelow.lean`'s `eml_unbounded_below_of_wrapped_crossing`:
for `c > 1`, if `A` stays bounded above by some fixed `K` along `x_d := log(log c + d)` (`d ∈
(0,1)`, the exact witness family cont. 15's original proof used) — a hypothesis anyone can
DIRECTLY CHECK for a concrete `A` without needing a continuity theorem at all — then `eml A (eml
P (eml var (const c)))` is unbounded BELOW, for ANY `P` (only `exp(P.eval x) > 0` is ever used,
exactly like the depth-1 lemma). Proof mirrors cont. 15's construction almost exactly, with one
new step (`exp_monotone` lifting the `A`-bound through `exp`) and the algebra abstracted into a
small reusable helper (`core_wrap_bound`) to avoid repeating the giant nested witness expression
at every step — the session's established "extract a general helper" pattern, paying off again.

**Sanity check, genuinely confirms equivalence not resemblance**: instantiating at `A := var`,
`P := eml var (const 1)`, `c := 1+1` reproduces `nonMonotonicWitness_unbounded_below`'s exact
conclusion — `eml A (eml P (eml var (const c)))` unfolds DEFINITIONALLY to `nonMonotonicWitness`
itself (not just "a similar tree"), and the `hAbdd` hypothesis for `A = var` is a two-line proof
(`log(log c + d) ≤ log(log c + 1)` for `d < 1`, monotonicity of `log`). `#print axioms` on the
instantiated corollary is IDENTICAL to the general theorem's list — confirms no hidden extra
machinery sneaks in through the instantiation.

**Combined into a full family closure** (`eml_depth2_witness_of_wrapped_crossing_T1`, combining
with the existing unbounded-below closure): the ENTIRE "crossing wrapped exactly twice" family —
matching `nonMonotonicWitness`'s own shape, for ANY `A` (bounded along the witness path), ANY
`P`, ANY `c > 1`, ANY `c2 > 1` — can never be a real witness-finding counterexample. Not one
hardcoded instance; the whole two-level shape, fully parametrized.

**Honest scope, precisely stated.** This still does NOT prove the general conjecture ("any
crossing anywhere ⟹ unbounded somewhere") — it proves it for exactly the TWO-LEVEL wrapping
shape, with the outer wrap's boundedness stated as an explicit, path-specific hypothesis rather
than derived from a general continuity theory. A caller with a THREE-level (or deeper) wrap, or
an `A` that ISN'T boundable along this specific witness path (e.g., `A` itself has its own
crossing interacting with the same region), is not covered. The crossing-depth induction named
last round remains the real target for full generality — this round narrowed what such an
induction's inductive step would actually need to supply (an explicit path-bound hypothesis at
each layer, not a full continuity argument), which is itself useful groundwork even though the
induction itself wasn't attempted.

`#print axioms` clean on all three new theorems, only base MachLib primitives, no
`HasDerivAt`/Rolle, zero `sorry`. Full `lake build MachLib` passes (414 modules) — **thirty new
files in one session.**

## 2026-07-21 (cont. 19) — MILESTONE: the open classification is NOT vacuous — a concrete member
found, fully verified

**The question this settles.** Every round since `nonMonotonicWitness` narrowed the residual's
open territory to exactly: `T1` bounded BOTH directions, non-constant, non-
`RightChildrenSimplePositive`, non-monotonic. Every closure built (three fully general, two
parametrized families) failed to rule out `nonMonotonicWitness` itself only because it turned
out to be bounded in ONE direction, not two. The open question hanging over the last several
rounds: is that four-property class actually EMPTY (in which case a strong enough closure would
eventually rule out everything and the residual would fully close), or does it contain a real
member? **Answer: it contains a real member.**

**The construction, and why it works.** `nonMonotonicWitness` is bounded above (`< log 2`) but
diverges to `-∞` near its clamp boundary. Applying `exp` to it fixes exactly that flaw:
`exp` is strictly increasing (preserves every relative comparison, in particular the PROVEN
non-monotonicity) and always strictly POSITIVE (turns `-∞` into an approach to `0` from above,
not another divergence). `expWrappedNonMonotonicWitness := eml nonMonotonicWitness (const 1)`
(`log 1 = 0` makes this EXACTLY `exp ∘ nonMonotonicWitness`, not merely close to it) —
`WitnessResidualExpWrappedNonMonotonic.lean`, commit `38156e30`.

**Every one of the four properties transports almost for free** from already-proven facts about
`nonMonotonicWitness`, via `exp`'s strict monotonicity — no new hard mathematics, the entire
insight was recognizing which EML operation repairs the one flaw:
- **Bounded below**: `0 < eval` everywhere, trivially (`exp` is always positive, regardless of
  what the inner tree does).
- **Bounded above**: `eval < 1+1` everywhere, transported directly from `nonMonotonicWitness`'s
  own upper bound through `exp_lt` + `exp_log`.
- **Non-constant**: the two points `nonMonotonicWitness_x0` (`T=0`) and `nonMonotonicWitness_xb`
  (`T<0`) — already known to differ — give different values after `exp` too (`exp`'s injectivity
  via `exp_lt` + trichotomy).
- **Not `RightChildrenSimplePositive`**: inherits the failure from its own left child — `eml
  nonMonotonicWitness (const1)` requires `RightChildrenSimplePositive nonMonotonicWitness` too,
  which fails immediately (`nonMonotonicWitness`'s own right child is a compound `eml` node,
  never equal to `var`/`const c`, an `EMLTree.noConfusion` argument).
- **Non-monotonic**: the SAME three witness points `nonMonotonicWitness_not_monotone` used,
  transported through `exp`'s strict monotonicity — `exp` preserves every strict inequality, so
  the flat→down→up valley shape survives intact into `exp∘nonMonotonicWitness`.

**What this settles, stated with real care.** This is a genuine, concrete, fully-verified tree
that NO closure built this session can rule out as a `T1` candidate — the classification's open
territory is REAL, not an artifact of insufficiently general closures. **This does NOT mean the
axiom (`eml_pfaffian_validon_from_sin_equality`) is false, and it does NOT mean this specific
tree breaks the witness-finding argument.** It means only that the "free" shortcuts built this
whole session — genuinely valuable, genuinely general — are now KNOWN to be insufficient for
this tree specifically. Whether the full residual still closes for `T1 =
expWrappedNonMonotonicWitness` via the HEAVIER zero-counting/Pfaffian-chain machinery this arc
built earlier (before this session) remains completely open, unattempted here. This tree is now
the canonical, concrete TEST CASE for whoever attempts that heavier machinery next — not a
disproof of anything, a target.

`#print axioms` clean — notably, STILL only base MachLib primitives (no `HasDerivAt`/Rolle
anywhere, inherited from `nonMonotonicWitness`'s own pure-algebra proofs), zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` doesn't appear. Full `lake build MachLib` passes (415
modules) — **thirty-one new files in one session.**

## 2026-07-21 (cont. 20) — the test case resolved: `expWrappedNonMonotonicWitness` closes too,
via the pre-existing heavy machinery, genuinely non-circular

**The question left open last round.** `expWrappedNonMonotonicWitness` escapes every free
closure this session built — the honest framing was "a test case, not a disproof": does the
PRE-EXISTING (before-this-session) zero-counting/Pfaffian-chain machinery still close it?

**Yes — fully verified, non-circular.**
(`WitnessResidualExpWrappedNonMonotonicClosed.lean`, commit `e9f1bf18`.)
`no_tree_with_simple_right_children` (`WitnessResidualSimpleT1Application.lean`) closes trees via
that heavy machinery by supplying two structural facts — `EMLWitnesses T1 x0` (a positivity
anchor threaded through every node) and `∀x>0, EMLNoCrossingAt T1 x` (no internal log-argument
hits exactly `0`, for `x>0`) — normally obtained for free from `RightChildrenSimplePositive`.
That freeness doesn't apply here (that's WHY this tree escaped every free closure) — but both
facts turn out to be independently provable BY HAND, using facts ALREADY established about
`nonMonotonicWitness` two rounds ago, no new hard analysis needed.

**The key structural observation that makes this work.** `nonMonotonicWitness`'s own
problematic zero-crossing — where its right-child chain `D := eml var (const 2)` crosses zero —
sits at `x0 = log(log 2) ≈ -0.37`, a NEGATIVE point (proven exactly:
`nonMonotonicWitness_x0_neg`, via `exp_gt_one_plus_self` at `x=1` giving `2 < e`, hence
`log 2 < 1`, hence `log(log 2) < 0`). The heavy machinery only ever needs `EMLNoCrossingAt` for
`x > 0`. The crossing that caused ALL the earlier trouble (unbounded-below divergence, the
non-monotonic valley) simply isn't IN that region — `nonMonotonicWitness_Dpos`/
`nonMonotonicWitness_Bpos` (both already proven, for any `x > nonMonotonicWitness_x0`) directly
supply strict positivity for every node's log-argument throughout `x > 0`, with zero new
case-analysis. The witness anchor reuses the SAME established point `π + π/2` the existing
family members use.

**What this settles, and what it deliberately does NOT claim.**
`eml_depth2_witness_of_const_gt_one_sibling_expwrapped_T1`: `expWrappedNonMonotonicWitness`
poses NO threat to the witness-finding argument, for ANY `c2 > 1`, full stop. The classification
being non-empty (cont. 19) and the residual failing to close for a SPECIFIC member of it are
different questions — this resolves the second one, for this one tree, in the reassuring
direction. This does NOT prove the whole open classification closes in general — the proof is
SPECIFIC to this tree's own structure, particularly the "crossing sits at negative `x`"
observation, which is a property of THIS tree's specific numeric parameters, not a general fact
about every tree in the classification. A tree in the same open class whose crossing sat at
POSITIVE `x` (easy to construct — just shift the crossing constant) would need a genuinely
different argument. But it is a second, independent confirmation (after `nonMonotonicWitness`'s
own resolution vanishing act two rounds ago) that finding a member of the open class does not,
by itself, threaten the theorem — every concrete tree probed so far in this whole arc, by
whatever mechanism available, has turned out to be closable.

**The axiom check that actually matters here, done with real care** (not just the usual
zero-`sorry` scan): this proof pulls in the FULL heavy machinery for the first time this session
— `HasDerivAt`, `rolle_ct`, the whole `analytic_*` family, `sup_exists` (`Real`'s completeness
axiom) — a much longer list than every other closure built this session (which were all pure
algebra). The one check that actually mattered: does `eml_pfaffian_validon_from_sin_equality`
(the axiom this entire arc exists to discharge) appear ANYWHERE in that list? Checked explicitly
via `grep` on the full `#print axioms` output, not just eyeballed — **it does not appear.** The
proof is genuinely non-circular: it doesn't smuggle in the very fact it's supposedly helping
establish. Zero `sorryAx` either (also grep-checked explicitly). Full `lake build MachLib`
passes (416 modules) — **thirty-two new files in one session.**

## 2026-07-21 (cont. 21) — the honest follow-up question, answered: the negative-crossing
resolution structurally CANNOT extend to a positive crossing

**The question from last round's own scope note.** `expWrappedNonMonotonicWitness` closed
because its crossing sits at negative `x`, outside the region the closure route
(`no_tree_eq_nested_target_given_validon`, needing `EMLPfaffianValidOn T1 0 b` for ALL `b > 0`)
ever inspects. The honest caveat: a tree in the SAME open classification with its crossing at
POSITIVE `x` would need a genuinely different argument. Checked numerically first (python,
`c=20` gives crossing `x0≈1.10`, tree still bounded `[0.93,1.00]` and non-monotonic — same
qualitative shape as the `c=2` case, just shifted) before touching Lean.

**Formalized: not "this session's specific proof doesn't apply" but "no proof via this route
possibly could"** (`EMLPfaffianValidOnCrossingObstruction.lean`, commit `68686049`). `EMLPfaffianValidOn`'s
own definition demands strict positivity of every log-argument THROUGHOUT the open interval — if
any internal right child hits exactly `0` anywhere inside `(a,b)`, validity is FALSE there, one
unfolding step from the definition, no induction needed
(`eml_pfaffian_validon_false_of_crossing`). Failure at any node propagates upward through
arbitrarily many further wrappings (`eml_pfaffian_validon_false_propagates_left`/`_right` — a
compound tree's own validity unconditionally needs BOTH children valid). Chaining these three
steps: for `nonMonotonicWitnessC c` / `expWrappedNonMonotonicWitnessC c` (the SAME shape as
`nonMonotonicWitness`/`expWrappedNonMonotonicWitness`, crossing constant `c` left free instead
of hardcoded to `1+1`), whenever `c` is large enough that the crossing point `log(log c)` is
POSITIVE, `EMLPfaffianValidOn (expWrappedNonMonotonicWitnessC c) 0 b` is PROVABLY FALSE for
every `b` past that crossing — the exact hypothesis `no_tree_eq_nested_target_given_validon`
needs, unconditionally unavailable.

**A concrete, parameter-free instance, not just an abstract conditional**: `c := exp(exp 1)`
gives an EXACT crossing point `log(log c) = 1` (two applications of `log_exp`, no numerical
approximation of `e` needed anywhere) — `concreteC_validon_false`: this specific, fully written-
down tree is `EMLPfaffianValidOn`-invalid on `(0, 1+1)`, full stop.

**Scope, stated with the same care as every other round.** This is a NEGATIVE, STRUCTURAL result
about the `EMLPfaffianValidOn`-based route specifically — it does NOT construct a NEW verified
counterexample to the witness-finding residual (that would additionally need FORMALLY proving
`expWrappedNonMonotonicWitnessC c` is bounded both directions and non-monotonic for such `c`,
which was only checked NUMERICALLY here for illustration, not formalized in Lean — a real,
substantial undertaking on its own, deliberately not attempted this round given the negative
result already answers the question that motivated it). What it DOES establish, rigorously: the
resolution technique from last round is not a general-purpose tool that happens to work for
every tree in the open classification — it structurally cannot reach ANY tree with a positive-x
crossing. This CONFIRMS, now via a concrete verified example rather than abstract reasoning,
something this whole multi-week arc suspected much earlier (the "why path (1) is hard,
precisely" entry, `2026-07-20`, cont. before this session): positivity-based validity has no
notion of a relation that switches sign, and cannot describe a tree across a sign change without
a genuinely new branch-switching Pfaffian chain construction this codebase doesn't have yet.

**Net honest status of the arc, after 21 rounds today.** The residual's open classification is
non-empty (cont. 19); every SPECIFIC tree probed so far (by whatever mechanism available) has
turned out either closable (both `nonMonotonicWitness` itself and
`expWrappedNonMonotonicWitness`) or — for the deliberately-constructed harder case this round —
genuinely resistant to the ONE technique that worked before, confirmed rigorously rather than
assumed. No tree has yet been shown to be BOTH a genuine open-classification member AND
unclosable by every available technique — that would need completing the "boundedness +
non-monotonicity for general `c`" formalization this round deliberately deferred, combined with
either a genuinely new closure mechanism or a demonstration that none exists. Realistically the
natural target for a dedicated future session, not a continuation of today's incremental
narrowing.

`#print axioms` clean on both main theorems — pure algebra, no `HasDerivAt` (this result needs
no calculus at all, unlike last round's), only base MachLib primitives. Zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` doesn't even appear as a DEPENDENCY risk here (this
result is about `EMLPfaffianValidOn`'s own definition, orthogonal to the axiom under
investigation). Full `lake build MachLib` passes (417 modules) — **thirty-three new files in one
session.**

## 2026-07-21 (cont. 22) — MILESTONE: the first tree confirmed BOTH a genuine open-class member
AND resistant to the closure that worked before, fully verified end to end

**Completing what cont. 21 deliberately deferred.** The negative result (`concreteC` is
`EMLPfaffianValidOn`-invalid past its crossing) was accompanied by an explicit caveat: it does
NOT establish that `expWrappedNonMonotonicWitnessC concreteC` actually belongs to the open
classification — that boundedness-both-directions-and-non-monotonicity claim was only checked
NUMERICALLY. This round formalizes it, completing the picture.

**Mirrors `WitnessResidualNonMonotonic.lean`/`WitnessResidualExpWrappedNonMonotonic.lean`'s exact
technique, `1+1` replaced by `concreteC := exp(exp 1)` throughout**
(`WitnessResidualExpWrappedNonMonotonicCPositive.lean`, commit `fa477ded`). Every step transfers
directly except ONE: the boundedness proof's `two_mul_eq_add_self` trick was specific to the
crossing constant literally being `1+1` (`exp(exp x)=(1+1)·exp(D)` collapsing cleanly to
`exp(D)+exp(D)`). For general `concreteC` this doesn't apply. **The fix**: `concreteC > 1+1`
(cheap — `exp_gt_one_plus_self` applied twice, at `x=1` giving `2<e` and at `x=exp 1` giving
`1+e<exp(e)=concreteC`, chaining to `3<concreteC`) gives `1<concreteC-1`, hence (via
`mul_lt_mul_of_pos_right`) `exp(D)<(concreteC-1)·exp(D)` — playing EXACTLY the role the doubling
trick did. The rest of the ~15-step boundedness chain (`log_lt_self_of_pos`, `exp_add`+`exp_log`
factoring, the final `log_lt_log`/`sub_lt_sub_left_local` cascade) is untouched, confirming the
technique really was about "crossing constant `>2`", not "crossing constant `=2`" specifically.

**The result, combined with last round's negative result into one statement**
(`concreteC_open_class_member_and_validon_resistant`): `expWrappedNonMonotonicWitnessC concreteC`
is bounded in BOTH directions (`0 < eval < concreteC`, everywhere), non-constant, non-
`RightChildrenSimplePositive`, non-monotonic — a genuine, FULLY VERIFIED member of the residual's
open classification — AND `EMLPfaffianValidOn`-invalid past its crossing. **The first tree in this
entire multi-week arc (not just this session) confirmed to be BOTH a real open-class member AND
resistant to the ONE closure technique that successfully handled the negative-crossing case.**
Every earlier "found a member" (cont. 19) resolved cleanly (cont. 20); every earlier "technique
fails" (cont. 21) was paired with an unverified example. This round closes both gaps at once, for
the SAME concrete tree.

**What this does and deliberately does NOT claim, stated with the same care as every prior
round.** This is NOT a disproof of `eml_pfaffian_validon_from_sin_equality`, and it does NOT show
the witness-finding argument actually fails for this tree. It shows precisely what it shows: this
ONE closure technique — the one built and relied on throughout the ENTIRE arc, not just this
session — cannot reach this tree. Other techniques remain genuinely unexplored: domain-splitting
around the crossing point (mirroring the arc's much earlier `EMLZeroCrossingDomainSplit.lean`
work, treating the crossing as a special point and gluing pieces on either side), or a
fundamentally new branch-switching Pfaffian chain construction (the path this whole arc's
`EML_WITNESS_FINDING_DECISION_2026_07_15.md` has flagged since well before this session as the
real "weeks to a month" undertaking for full generality). This tree is now the sharpest, most
concrete target available for whoever attempts either.

`#print axioms` clean on the combined statement — pure algebra throughout, no `HasDerivAt`
anywhere (same flavor as `nonMonotonicWitness`'s own proofs), only base MachLib primitives. Zero
`sorry`, `eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib`
passes (418 modules) — **thirty-four new files in one session.**

**Net honest status of the arc, after 22 rounds today.** The witness-finding residual's open
classification is non-empty and now has a fully-verified member resistant to the arc's
established closure technique. This is real, meaningful progress on characterizing the residual
— but it is progress toward understanding the shape of the remaining difficulty, not toward
discharging the axiom itself. The axiom remains neither proven nor disproven; what's changed
today is the precision with which its remaining difficulty can be described and handed to
whoever continues.

## 2026-07-21 (cont. 23) — CORRECTION: `expWrappedNonMonotonicWitnessC concreteC` closes after
all, via a much simpler mechanism nobody tried for two rounds

**What happened.** Cont. 22 closed with "the axiom remains neither proven nor disproven" and
framed `expWrappedNonMonotonicWitnessC concreteC` as resistant to the arc's established closure.
That framing was accurate about the ONE technique tried — but "resistant to one technique" got
read (by me, in my own writing) as closer to "genuinely hard" than it turned out to be. Revisiting
with fresh eyes: every closure built this whole session reaches for a GLOBAL property of `T1`
(unboundedness, monotonicity everywhere). This tree's own defining feature — being CONSTANT on
its entire clamped region, not just bounded there — supports a MUCH more local argument that
nobody had tried.

**The mechanism** (`WitnessResidualTwoEqualPointsClosure.lean`, commit `e218f8e5`,
`eml_depth2_witness_of_const_sibling_two_equal_points`): if `T1` takes the SAME value at two
points where `sin` DIFFERS, the collapsed equation (`exp(T1.eval x) - c2 = sin x`, derived the
usual way from `S3 ≤ 0`) forces those two different `sin` values to be EQUAL — since `T1`'s
output at both points is identical, the equation's LHS is identical too, so the RHS must be —
immediate contradiction. **No monotonicity, no boundedness, no `c2 > 1` even** — checked
explicitly, `c2`'s sign and size never enter the proof at all, a first for this whole family.

**Applied concretely**: `expWrappedNonMonotonicWitnessC concreteC`'s clamped region extends to
`x ≤ x0 = 1`. Both `0` and `-π/2` satisfy this trivially (`0 ≤ 1` and `-π/2 < 0 ≤ 1`, `π > 0` is
all that's needed, no numeric bound-chasing) — `sin 0 = 0 ≠ -1 = sin(-π/2)`, closing it in a
handful of lines, no heavy machinery, no `EMLPfaffianValidOn` anywhere.

**The honest correction, stated directly.** `expWrappedNonMonotonicWitnessC concreteC` is NOT a
genuine obstruction to witness-finding. It closes cleanly — just via a different, simpler
technique than the one tried two rounds ago. The prior rounds' work stands as CORRECT and
non-wasted (the `EMLPfaffianValidOn`-based route genuinely does fail for this tree, exactly as
proven — that finding remains true and is a real, useful structural fact about that route's
limits) but the FRAMING of the tree as "resistant" needs this correction: resistant to one
specific technique is not the same as unclosable, and this round is a direct demonstration of
that gap.

**What remains open, honestly.** The residual's open classification is still non-empty as a
STATEMENT about the classification (bounded+non-constant+non-simple+non-monotonic trees exist,
cont. 19 stands). But NO tree has yet been found that survives every available technique,
including this new one — the search for a genuine, all-technique-resistant member continues.
Whether THIS new mechanism generalizes (any tree constant on a ray past two points with
different `sin` values closes — plausible for the WHOLE crossing-family this session built,
not checked for the general case) is the natural next question.

`#print axioms` clean on both theorems — remarkably minimal axiom lists (no `HasDerivAt`, no
`analytic_*`, no crossing machinery at all — pure ordered-field algebra plus `sin`'s own basic
axioms), confirming this really is the simplest closure mechanism built this entire session.
Zero `sorry`, `eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib`
passes (419 modules) — **thirty-five new files in one session.**

## 2026-07-21 (cont. 24) — MILESTONE: the ENTIRE crossing-family closes, unconditionally, for
ANY `c > 1` — the whole cont. 14–23 arc subsumed by one elementary argument

**The generalization asked for, done in full.** Cont. 23 closed `expWrappedNonMonotonicWitnessC
concreteC` specifically. The natural next question — does the "constant on a ray, two different
`sin` values" mechanism generalize past that one instance — is answered YES, completely.

**The one missing piece: `sin` is never eventually constant looking backward from ANY point**
(`WitnessResidualEntireCrossingFamilyClosed.lean`, commit `401718f7`, `sin_two_different_values_le`).
Built from `archimedean` (`∃n:Nat, x<natCast n`, already an axiom in `Basic.lean` — unused by
this whole session until now) plus a period-shifting induction
(`sin_sub_natCast_mul_two_pi`, mirroring `EMLPfaffian.lean`'s `sin_natCast_mul_pi` induction
template exactly, just shifting by `2π` via `sin_periodic` instead of `π` via `sin_add`+`sin_pi`):
for ANY target `a`, shift `0` and `π/2` far enough left (via Archimedean, using `π≥1` to convert
a `Nat` bound into a `2π`-multiple bound) to land BOTH `≤ a` while preserving their `sin` values
(`0` and `1` respectively) — no restriction on `a`'s sign or size at all.

**Combined with two more small generalizations**: the clamped-region fact
(`nonMonotonicWitnessC_eval_clamped_general`, previously proven separately for `1+1` and
`concreteC` — the derivation never actually depended on the specific value, confirmed by lifting
it to arbitrary `c > 1` directly) and the `exp`-wrap's own eval formula (trivial, `log 1 = 0`
either way) — this closes `eml_depth2_witness_of_expwrapped_family`: **the ENTIRE
`expWrappedNonMonotonicWitnessC c` family, for ANY `c > 1` and ANY `c2`, unconditionally.**

**What this actually settles.** The whole "crossing-based construction" arc explored across
cont. 14 through 23 — `nonMonotonicWitness` itself, its `exp`-wrap, the parametrized family, the
positive-crossing instance, the `EMLPfaffianValidOn`-based resolution, and its correction — is
now COMPLETELY closed as a source of potential witness-finding counterexamples, by ONE clean
elementary argument needing no monotonicity, no boundedness, no `EMLPfaffianValidOn`, and (per
`eml_depth2_witness_of_const_sibling_two_equal_points`, cont. 23) not even `c2 > 1`. Every
earlier closure built for pieces of this family — unbounded above/below, strictly monotonic, the
direct/wrapped-crossing lemmas, the heavy-machinery resolution — remains individually true and
was NOT wasted effort (each is a genuine structural fact, and several apply well outside this one
crossing shape) — but for THIS specific family, they are all now subsumed by this single,
simpler mechanism.

**What remains open, stated with the same care as every prior round.** This closes one large,
natural, thoroughly-explored family — not every conceivable tree in the residual's open
classification. The mechanism specifically needs `T1` CONSTANT (not merely bounded) on some
unbounded ray; a tree that is bounded both directions and non-monotonic WITHOUT any such
constant stretch — if one exists — would not be reached by it. No such tree has been found or
ruled out anywhere in this whole arc. That remains the honest, standing open question for
whoever continues.

`#print axioms` clean on both new theorems — notably, `sin_two_different_values_le` doesn't even
need `Classical.choice` (fully constructive); the combined family closure needs it only from the
underlying `Classical.byContradiction` in the two-equal-points mechanism (cont. 23). No
`HasDerivAt`, no `analytic_*`, no crossing/`EMLPfaffianValidOn` machinery — pure ordered-field
algebra, `archimedean`, and `sin`'s own basic axioms. Zero `sorry`,
`eml_pfaffian_validon_from_sin_equality` does not appear. Full `lake build MachLib` passes (420
modules) — **thirty-six new files in one session.**

## 2026-07-21 (cont. 25) — a structurally NEW candidate: growth-rate competition, no clamp
anywhere; boundedness proven, non-monotonicity explicitly left open

**Why look further, right after closing the whole crossing family.** Cont. 24's own honest
scope note: the mechanism needs `T1` CONSTANT (not merely bounded) on an unbounded ray — a tree
bounded both directions and non-monotonic WITHOUT such a stretch would escape it entirely. This
round searches for one directly, numerically first (per house style), before any Lean.

**Found one — a different mechanism than every other tree this whole arc has used.** Recall an
early finding this session, never followed up on: `exp(exp x) - x` is non-monotonic via pure
GROWTH-RATE competition between two smooth, never-clamping terms — but unbounded. The question:
can the SAME mechanism, applied to two ALREADY-bounded pieces instead of `exp(exp x)` and `x`,
stay bounded while keeping the wiggle? `growthCompetitionWitness c1 c2 := eml
(boundedNonConstantWitness c1) (eml (boundedNonConstantWitness c2) (const 1))` evaluates (via
`log∘exp=id`) to `exp(BNCW(x,c1)) - BNCW(x,c2)`. At `c1=2, c2=5/2`: numerically bounded in
`[0.7785, 1.0]`, approaching `1` as `x→+∞` and `≈0.7785` as `x→-∞`, with a genuine local
max-then-min wiggle confirmed near `x≈-0.69` on a fine grid (not a numerical artifact) — and
`inner := exp(exp x)-log c` stays strictly positive throughout for BOTH `c1` and `c2` over a
wide range, confirming NO `log`-clamp triggers anywhere in this tree at all.

**Formalized** (`WitnessResidualGrowthCompetitionWitness.lean`, commit `a770147b`): boundedness in
BOTH directions, for ANY valid `c1,c2` (not just the numerically-found pair) — turned out to
need NO new machinery at all, just combining `boundedNonConstantWitness`'s ALREADY-established
bounds additively (`1<exp(A)` and `B<U2` chain via two `sub_lt_sub_*` steps to `1-U2<exp(A)-B`;
symmetric argument for the upper bound). Also non-`RightChildrenSimplePositive` (same
`EMLTree.noConfusion` argument as every prior tree in this arc, inheriting the failure from the
left child's own compound right child).

**What remains explicitly, honestly open.** Non-monotonicity (and the non-constancy that would
follow from it) is NOT formalized. The mechanism is numerically overwhelming but proving it
needs either (a) a derivative-based sign-crossing argument — `T'(x) = exp(A(x))·A'(x) - B'(x)`,
both `A'`,`B'` already known negative-valued formulas via `boundedNonConstantWitness_deriv_neg`,
but their RATIO crossing `1` needs a genuinely new comparison this session hasn't built — or (b)
careful numerical interval bounds at specific points (tedious, no shortcut found). Both are
real, sizable undertakings in their own right, correctly scoped as the concrete next step for
whoever continues — not attempted this round, by explicit user direction to formalize the
STRUCTURE first and assess feasibility before committing further.

**Why this matters regardless of whether non-monotonicity gets proven.** Even at this partial
stage, this is genuinely new information: it demonstrates the crossing-family closure just built
(cont. 24) does NOT trivially generalize to "every bounded non-monotonic EML tree" — there is at
least one STRUCTURALLY DIFFERENT candidate mechanism (growth competition, zero clamps) that the
existing closure cannot even see, since it has no ray of constancy anywhere to exploit. Whether
this SPECIFIC tree turns out non-monotonic (closing the loop on a second family) or is somehow
secretly monotonic after all (which the numerics make very unlikely) is now a precisely-posed,
well-scoped open question, not a vague possibility.

`#print axioms` clean on all three new theorems — pure algebra, no `HasDerivAt` even though the
underlying `boundedNonConstantWitness` bounds it reuses were originally derivative-based (the
COMBINATION step here needed none). Zero `sorry`, `eml_pfaffian_validon_from_sin_equality` does
not appear. Full `lake build MachLib` passes (421 modules) — **thirty-seven new files in one
session.**

## 2026-07-21 (cont. 26) — into the hard stuff for real: `growthCompetitionWitness`'s
derivative correctly derived (catching a real bug), a clean algebraic route found, the key
convexity tool fully proven

**Direct user request: "let's proceed into the hard stuff please."** Attempted the
derivative-based sign-crossing route flagged last round as the natural next step.

**Step 1 — the derivative, done on paper, CROSS-CHECKED numerically, and CORRECTED.** Composing
`boundedNonConstantWitness`'s own known derivative and eval formulas: `T'(x) = exp(x)·S(E)`
where `E := exp(exp x)` and (after a first hand-derivation attempt that TURNED OUT WRONG — caught
by cross-checking against a finite-difference ground truth in Python, exactly the "verify before
trusting" discipline this whole arc has repeatedly needed) the CORRECTED formula is `S(E) =
log(c2)/(E-log c2) - E·log(c1)/(E-log c1)²`. The bug: mistakenly wrote `boundedNonConstantWitness`'s
leading term as `x` instead of `exp(x)` when composing `exp(A(x))` — a one-symbol slip with a
large downstream effect (the ORIGINAL wrong formula was POSITIVE everywhere, completely masking
the real sign change). Confirmed correct via finite-difference match to 10 digits across the
whole tested range.

**Step 2 — clearing denominators turns a transcendental sign question into PURE ALGEBRA.**
`S(E) < 0` iff `(q-p)·E² - pq·E + p²q < 0` where `p := log c1`, `q := log c2` — a QUADRATIC in
`E`, the SAME algebraic object regardless of which `c1, c2` are chosen. This sidesteps needing
ANY numeric bounds on `log(2.2)`, `log(2.7)`, etc. — the whole remaining difficulty reduces to a
pure ordered-field fact about quadratics. Also found much better parameters (`c1=2.2, c2=2.7`,
via a parameter sweep) than the original numerical exploration's `c1=2,c2=2.5` — comfortable
margins on BOTH sides of the sign change (`S≈+5.4` near `E=1.05`, `S≈-0.78` near `E=1.2`) instead
of the original's razor-thin `~0.06` margin at the negative extremum.

**Step 3 — the convexity tool, fully proven** (`WitnessResidualQuadraticConvexity.lean`, commit
`608be764`, `quadratic_neg_between`): an upward-opening quadratic negative at two points `a<b` is
negative throughout `[a,b]`. Via the exact identity `(b-a)·quad(E) = (b-E)·quad(a) +
(E-a)·quad(b) - k·(b-a)·(E-a)·(b-E)` — every RHS term `≤0`, at least one strictly (since `(b-E)`
and `(E-a)` can't both vanish, their sum being the fixed positive `b-a`) — no calculus, no
discriminant, no square roots, pure algebra. `#print axioms` clean, ordered-field only, no
`exp`/`log`/`sin` at all — a genuinely general, standalone, reusable fact.

**Two new build gotchas, both worth recording.** (1) `mach_mpoly` — usually reliable for exactly
this kind of multi-atom identity — left a residual `-0=0` on the SPECIFIC 4-variable, degree-3
identity needed here (closed by a follow-up `rw [neg_zero]` in the SAME tactic block); confirmed
via an independent numerical check (5 random substitutions in Python) BEFORE debugging Lean that
the gap was in the TACTIC, not the identity — avoiding wasted effort chasing a phantom math
error. (2) `by_contra` is not a recognized tactic in this Mathlib-free codebase — the established
`refine Classical.byContradiction (fun hcon => ?_)` pattern is required.

**What remains, stated precisely — not vaguely "hard" anymore, but a well-defined remaining
task.** The quadratic tool gives `S(E)<0` throughout a chosen `E`-interval; still needed: (a)
translate the `E`-interval into an `x`-interval (via `E=exp(exp x)`, monotonic, so this is
routine) and feed into `strictAnti_of_deriv_neg` to get `T` strictly decreasing there; (b) the
MIRROR argument for a region where `S(E)>0` (using `strictMono_of_deriv_pos`, symmetric in
structure — the "near E=1" positive region has an even simpler direct argument, not needing the
quadratic tool at all, since `log(E)` there can be handled directly); (c) combine both directional
results into the same 3-point non-monotonicity packaging used throughout this whole arc
(`nonMonotonicWitness_not_monotone`'s own template). None of these are open MATHEMATICAL
questions anymore — each is routine, mechanical Lean engineering using tools already proven or
already available in the codebase. This is a genuinely different kind of "remaining work" than
two rounds ago: then, the obstruction was not knowing HOW to close the gap; now, the path is
fully mapped, just not yet walked.

`#print axioms` clean, zero `sorry`, `eml_pfaffian_validon_from_sin_equality` does not appear.
Full `lake build MachLib` passes (422 modules) — **thirty-eight new files in one session.**

## 2026-07-21 (cont. 27) — `growthCompetitionWitness` FULLY CLOSED: non-monotonicity proven,
zero `sorry`, genuine escape from the residual's closure confirmed

**Direct user request: "proceed please"**, continuing straight from cont. 26's precise scoping.
Walked the full mapped path in one continuous round: `quadratic_pos_below_vertex` (the missing
mirror tool), the real `HasDerivAt` composition, the cleared-denominator identity connecting it to
the quadratic, four concrete numeric facts pinning the quadratic's sign at `c1=2.2, c2=2.7`, the
`E`-to-`x` translation, and the final `strictMono`/`strictAnti` assembly. Every piece verified
numerically in Python before being written in Lean, per house style throughout.

**Piece 1 — the mirror convexity tool** (`WitnessResidualQuadraticConvexity.lean`,
`quadratic_pos_below_vertex`). Positivity does NOT propagate between two arbitrary points the way
`quadratic_neg_between`'s negativity does (the dip can sit BETWEEN two positive points — that's
the whole mechanism) — but it DOES propagate in one direction from a single point at or left of
the vertex, via the same identity specialized (`quad(E)-quad(b) = (E-b)·(k·(E+b)+m)`, both factors
`≤0` on the near side). Needed one new primitive, `mul_nonneg_of_nonpos_of_nonpos`, built from
`neg_nonneg_of_nonpos` + `mul_nonneg` + the pre-existing `neg_mul_neg` (`Ring.lean`).

**Piece 2 — the real derivative, composed** (`WitnessResidualGrowthCompetitionDeriv.lean`).
`growthCompetitionWitness_hasDerivAt`: `T = exp∘A - B` via `HasDerivAt_comp` then `HasDerivAt_sub`,
reusing `boundedNonConstantWitness_hasDerivAt` unchanged for both `A` and `B`. Then the cleared-
denominator identity `T'(z)·(E-p)²·(E-q) = exp(z)·quad(E)`, built from three pieces: `exp_A_mul_denom`
(`exp(A(z))·(E-p)=E`, via `exp_sub`+`exp_log`+`mul_inv`), `deriv_A_mul_denom` (a standalone
extraction of the `hprod` step buried inside `boundedNonConstantWitness_deriv_neg`'s own proof,
reused for both `c1` and `c2`), and `clear_denom_identity` (a fully abstract 7-atom algebra lemma,
closed by targeted `rw` + `mach_mpoly` between substitutions — deliberately never handing
`mach_mpoly` a raw fraction). Dividing the cleared identity back out through the known-positive
denominator (`neg_of_mul_neg_pos`, mirroring the pre-existing `pos_of_mul_pos_right`) gives the
two sign-bridge corollaries `growthCompetitionWitness_deriv_neg_of_quad_neg`/`_pos_of_quad_pos`.

**Piece 3 — pinning the sign numerically** (`WitnessResidualGrowthCompetitionNumeric.lean`). Four
concrete facts for `c1=2.2, c2=2.7`: `quad(1.3)<0`, `quad(2.3)<0` (feeding `quadratic_neg_between`),
`quad(1.05)>0` plus the vertex condition at `b=1.05` (feeding `quadratic_pos_below_vertex`). All
four derived — not axiomatized — from two new well-justified numeric axioms bracketing `log(2.2)`
and `log(2.7)` to four decimal places (`log_2_2_bounds`, `log_2_7_bounds`; same status as
`exp_one_lt_three`/`pi_gt_three`). Why axioms at the log level rather than the quad-value level
directly: MachLib has no `nlinarith`-equivalent tactic (confirmed — `Linarith.lean`'s own docstring
flags this as unbuilt future work), so a 2D interval bound has to be turned into a quadratic's sign
BY HAND; kept the axiom surface at the semantically meaningful level (two facts about actual
transcendentals) rather than four ad-hoc "trust this polynomial's sign" facts. Technique: bound
each of `quad`'s three terms INDEPENDENTLY at whichever box corner is worst-case for that term
alone (looser than joint optimization, checked numerically first that the loose bound still clears
with real margin — e.g. `-0.050` vs. true `-0.056` at `E=1.3`).

Hit a genuine `mach_decimal` gap: no general SIGNED decimal subtraction (only the `1-x` special
case via `one_sub_decimal`). Fixed two ways — added `decimal_sub_same` to `Decimal.lean` itself
(the general same-exponent case, mirroring how `decimal_add_same` generalizes addition: real,
reusable infrastructure), and reformulated every `A-B+C<0` goal as `A+C<B` so the top-level
combination never needs signed subtraction at all. Also: every literal padded to a UNIFORM
decimal-place count (`1.3`→`1.3000`) so every product in a sum lands at the same
`realOfScientific` exponent — `decimal_add_same` only fires on matching exponents.

**Piece 4 — the `E`-to-`x` translation and final assembly**
(`WitnessResidualGrowthCompetitionAssembly.lean`). `E:=exp(exp x)` is a strictly increasing
bijection `ℝ→(1,∞)` with inverse `x=log(log E)` (valid whenever `E>1`); `exp_exp_log_log` is the
inversion, `log_log_mono`/`exp_exp_mono` the two monotonicity directions. Chose `x1:=log(log 1.02)`,
`x2:=log(log 1.05)` (increasing interval, both below the vertex `≈1.912`) and `x3:=log(log 1.3)`,
`x4:=log(log 2.3)` (decreasing interval, between the roots `≈1.112` and `≈2.712`) — `E=1.02`/`E=1.3`
also anchor `hApos`/`hBpos` across their WHOLE interval via monotonicity (`1.02>1.3>log(2.7)>log(2.2)`
with comfortable margin). Fed both intervals into `strictMono_of_deriv_pos`/`strictAnti_of_deriv_neg`,
then combined into `growthCompetitionWitness_2_2_2_7_not_monotone` — TWO disjoint point-pairs (not
a shared 3-point pivot; the negation of "monotone" only needs one counterexample pair per
direction, and the two intervals already give one each, which turned out simpler than the
`nonMonotonicWitness_not_monotone` 3-point template used elsewhere in this arc).

**Two new `apply`-unification gotchas, worth recording precisely.** (1) Stating a goal as
`(fun w => BODY) x` gets silently beta-reduced by the elaborator into `BODY[w:=x]` directly, so
`apply strictAnti_of_deriv_neg _ a b hab` (function left as `_`) fails to higher-order-unify
against the now-non-application-shaped goal — fixed by supplying the lambda EXPLICITLY (not a
metavariable), letting Lean check by defeq (which includes beta) instead of syntactic pattern
matching. (2) `mach_decimal` cannot prove `(1:Real) < 1.3` directly (`1` is the raw `oneR`, not a
`realOfScientific` literal) — fixed via the pre-existing ad-hoc bridge
`realOfScientific_one_dot_zero : realOfScientific 10 true 1 = 1`, rewritten in first. Also needed
a small but essential bridge lemma, `quad_forms_eq`, converting between the "subtraction" form
(how the numeric facts and sign corollaries are stated) and the "`k·X·X+m·X+n`" addition form
(how the convexity tools are stated) — mathematically identical but syntactically different terms,
since `sub_def` is an axiom, not a `rfl`-reduction, in this codebase.

**The closing theorem**: `growthCompetitionWitness_2_2_2_7_exists` — bounded both directions, not
`RightChildrenSimplePositive`, non-monotonic both directions, all for the CONCRETE instance
`c1=2.2, c2=2.7`. `#print axioms` clean: only ordered-field/exp/log/decimal/`HasDerivAt`-calculus
axioms plus `log_2_2_bounds`/`log_2_7_bounds` — no `sorryAx`, `eml_pfaffian_validon_from_sin_equality`
does NOT appear. This is a genuinely NEW, FULLY VERIFIED member of the witness-finding residual's
open classification — one that escapes every closure mechanism built earlier in this whole arc (no
`log`-clamp anywhere in the tree; the non-monotonicity here comes from pure growth-rate competition
between two smooth, never-clamping sub-expressions, unlike every prior tree in the crossing-family).

**What this means for the residual, stated precisely.** The open classification (bounded,
non-constant, non-simple, non-monotonic EML trees exist) is no longer just a true STATEMENT — it
now has an EXPLICIT, FULLY VERIFIED witness. Whether this closes the whole witness-finding Option D
question (i.e. whether `growthCompetitionWitness 2.2 2.7`, or a tree built from it, can be shown to
actually FAIL the witness-finding equation `t.eval = sin` for some `T1,S2,S3,c2`, the way
`boundedNonConstantWitness_ne_shifted_sin_target` did via injectivity for the monotonic case) is
the natural next question — NOT attempted this round. `growthCompetitionWitness` is not injective
(it's non-monotonic by construction), so the injectivity trick used for the monotonic witness does
NOT apply here; a different argument would be needed.

Full `lake build MachLib` passes (425 modules). Three new files this round
(`WitnessResidualGrowthCompetitionNumeric.lean`, `WitnessResidualGrowthCompetitionAssembly.lean`,
plus `quadratic_pos_below_vertex`/sign-corollaries added to the two pre-existing files), one
Decimal.lean addition (`decimal_sub_same`), zero `sorry` anywhere in the new work.

## 2026-07-21 (cont. 28) — MILESTONE: `growthCompetitionWitness` can NEVER be a witness-finding
counterexample; a fourth `eml_depth2_witness_of_const_*` family member, closed via a route that
sidesteps the arc's central multi-week obstruction entirely

**Direct user request: "proceed into that please"**, continuing from cont. 27's flagged "natural
next question" — does `growthCompetitionWitness` (or a tree built from it) actually BREAK the
`t.eval=sin` equation, or does the witness-finding theorem still hold for it? Answer: **it still
holds**, for ANY valid `c1', c2'`, not just the concrete `2.2, 2.7` instance.

**The plan that was NOT used, and why.** Initial approach (worked out on paper first, per house
style): since `growthCompetitionWitness` is non-monotonic (not injective), the "injectivity"
trick that closed the monotonic witness doesn't apply. Sketched an alternative — find two points
`x_a < x_b` with `T1(x_a)=T1(x_b)` (via IVT on `growthCompetitionWitness`'s increase-decrease-
increase shape, using the already-proven monotonicity intervals from cont. 27) with `sin(x_a)≠
sin(x_b)` (via sin's own monotonicity on those same x-ranges, since they land in disjoint sin-
monotonic pieces), then feed into `eml_depth2_witness_of_const_sibling_two_equal_points`. Verified
numerically that ALL the needed inequalities hold with comfortable margin (T1-range overlap ≈0.14,
sin-range separation ≈0.061) — so the plan was mathematically sound. But every step needed NEW
numeric bounds on deeply nested transcendental expressions (`T1` and `sin` evaluated at points
like `log(log(1.02))`) — a substantial undertaking, likely comparable in scope to cont. 27's whole
numeric-bounding effort, repeated for harder (nested, not polynomial) expressions.

**The route that actually worked, found by re-reading `EMLPfaffianValidOn`'s definition instead
of building more numeric machinery.** It's a plain structural recursion (`EMLPfaffian.lean:117`):
`True` at every leaf; at `eml t1 t2`, `EMLPfaffianValidOn t1 ∧ EMLPfaffianValidOn t2 ∧ (∀x∈(a,b),
0<t2.eval x)`. The reason this predicate has been the arc's central multi-week obstruction (see
the `2026-07-20` "grounded WHY path (1) is hard" entry) is that GENERAL compound trees mix
`log`-CLAMPED and unclamped regions across the interval — needing a not-yet-built branch-switching
Pfaffian chain type, since the SAME fixed algebraic relation can't describe `log(t2)` across a
sign change. But `growthCompetitionWitness` is built entirely from `boundedNonConstantWitness`,
whose whole defining feature (from the very first file in this sub-arc) is that it NEVER clamps —
`boundedNonConstantWitness_Bpos` already gives `0 < exp(exp x) - log c` UNCONDITIONALLY, for every
`x`, no case split needed anywhere. Once every log-argument positivity condition in the tree is
available like this, `EMLPfaffianValidOn` falls out by walking the (fixed, finite) tree shape
ONCE — no induction on tree depth, no branch-switching machinery, no numeric point-evaluation at
all. Genuinely faster and cleaner than the numeric plan, once seen.

**Two small building blocks, both fully unconditional in the interval `(a,b)`** — no restriction,
no case split: `boundedNonConstantWitness_EMLPfaffianValidOn` (the recursion bottoms out in
`boundedNonConstantWitness_Bpos` plus two trivial constant-positivity facts, `0<1` and `0<c`) and
`growthCompetitionWitness_EMLPfaffianValidOn` (reuses the above TWICE, once per inner constant
`c1, c2`, plus one trivial `exp(...)-log 1 = exp(...) > 0` fact for the outer structure).

**The closure itself** feeds these into machinery that ALREADY EXISTED in the codebase but had
never been exercised for a genuinely compound tree: `eml_T1eq_of_const_sibling_le_zero`
(`WitnessResidualSimpleT1Application.lean` — the `S3≤0` collapse, already fully general, no
`RightChildrenSimplePositive` needed) derives `T1.eval x = log(c2+sin x)` from the collapse
assumption; `T1_not_eq_log_c2_plus_sin_given_validon` (`WitnessResidualChainSkeleton.lean` — the
generic zero-counting contradiction via `enc_combinedBound`, previously ONLY ever called with
`hvalidon_any_b` left as an explicit UNDISCHARGED hypothesis, per that file's own stated purpose
of "verify the rest of the architecture is sound before attacking the hard piece") now gets fed a
genuine PROOF of that hypothesis for the first time in the whole arc.

**Result**: `eml_depth2_witness_of_const_gt_one_sibling_growthCompetition` — a FOURTH member of
the `eml_depth2_witness_of_const_*` family, alongside `_le_one_sibling` (`c2≤1`),
`_unbounded_T1` (`T1` unbounded), and `_gt_one_sibling_simple_T1` (`RightChildrenSimplePositive`).
Covers the exact combination none of the other three reach: `T1` bounded, non-simple, AND
non-monotonic all at once — precisely the shape this whole `growthCompetitionWitness` sub-arc was
built to explore. `#print axioms` confirms `eml_pfaffian_validon_from_sin_equality` does NOT
appear in the dependency chain (genuinely non-circular), zero `sorryAx` — dependencies are exactly
the arc's standard trusted base: the analytic-function axioms (`IsAnalyticOnReals`/`analytic_*`),
`HasDerivAt` calculus, `rolle_ct`, sin/cos facts.

**Why this may matter FAR beyond this one tree — flagged precisely, not claimed further.** This is
the FIRST time in the ENTIRE 40+-file arc that `hvalidon_any_b` has been discharged for a
genuinely compound, non-trivial tree WITHOUT restricting to `RightChildrenSimplePositive` (every
right child literally `var`/positive constant) and WITHOUT building the not-yet-existing
branch-switching chain machinery. The actual mechanism — "if every log-argument positivity fact
in the tree is available UNCONDITIONALLY (no clamp anywhere), `EMLPfaffianValidOn` is free, by
direct structural recursion" — is not tied to `growthCompetitionWitness`'s specific shape at all.
It should extend to ANY tree built entirely from non-clamping pieces, which is a substantially
LARGER class than `RightChildrenSimplePositive` (that restriction requires right children to be
LEAVES; this mechanism only requires log-arguments to be provably positive, which compound
non-leaf expressions can also satisfy, as this file demonstrates). Whether this closes a
meaningfully larger fraction of the ORIGINAL general-tree-depth-induction wall is a real,
substantial, OPEN follow-up question — genuinely promising, not yet investigated, not claimed
here as solved.

Full `lake build MachLib` passes (426 modules). Two files this round
(`WitnessResidualGrowthCompetitionValidOn.lean`, new), zero `sorry` anywhere in the new work.

## 2026-07-21 (cont. 29) — the no-clamp `EMLPfaffianValidOn` route GENERALIZED past
`growthCompetitionWitness`, confirmed correct via a research pass + a sanity-check corollary

**Direct user request: "proceed please"**, continuing from cont. 28's flagged follow-up: is the
"no clamp anywhere ⟹ `EMLPfaffianValidOn` is free" mechanism tied to `growthCompetitionWitness`'s
specific shape, or genuinely general? Dispatched a research agent first (read-only, no edits) to
survey the existing `EMLPfaffianValidOn` machinery end to end before building anything — confirmed
no such general predicate already existed in the committed codebase, and gave a complete map of
every file that constructs or consumes the predicate (the OTHER existing route,
`eml_pfaffian_validon_of_witnesses_backward`/`_twosided` in `EMLSmoothness.lean`, derives validity
from a single-point witness + no-crossing + differentiability — more powerful in principle, but
needs exactly the crossing-analysis machinery this arc has spent weeks building one shape at a
time; genuinely complementary to what follows, not overlapping).

**`RightChildrenEverywherePositive`** (`WitnessResidualRightChildrenEverywherePositive.lean`):
`True` at leaves; at `eml t1 t2`, both children recursively satisfy it AND `t2` is positive for
EVERY `x` — no interval, no case split. `EMLPfaffianValidOn_of_right_children_everywhere_positive`
converts this into `EMLPfaffianValidOn T a b` for ANY `a,b`, via one structural induction
MIRRORING `EMLPfaffianValidOn`'s own recursive definition exactly — the induction step is a single
line, since the only thing changing is weakening a bare `∀x` into `∀x∈(a,b)`.

**One real build hiccup, worth recording precisely — a stale-cache FALSE POSITIVE.** The first
draft compiled with "Build completed successfully" and no errors from `lake build
MachLib.ZZZTestGeneralValidOn`, but a subsequent `#print axioms` on the SAME theorem names failed
with "unknown constant" — the targeted build had silently read a stale cached `.olean` from an
EARLIER, differently-named file state, not the actual current source. This is the SAME class of
gotcha flagged before (`feedback_lake_targeted_build_stale_measurement` in memory) but caught here
via the SAME discipline that flagged it originally: always verify with `#print axioms` from a
FRESH import, never trust a bare "successfully built" message alone. Forcing a clean rebuild (`rm`
the `.olean`/`.c` artifacts, rebuild) surfaced the REAL error: a mis-nested anonymous constructor
in `boundedNonConstantWitness_RightChildrenEverywherePositive` (missing the `1<c` hypothesis
entirely, silently absorbed by the wrong slot in the nesting). Fixed by re-deriving the EXACT
nested `∧`-structure by hand (right-associative, matching `EMLPfaffianValidOn`'s own shape level
by level) before re-writing the `refine`.

**Relationship to `RightChildrenSimplePositive`** (the FIRST unconditional closure in the whole
arc, `WitnessResidualSimpleRightChildren.lean`): strictly more general — that predicate ADDITIONALLY
requires every right child to be a LEAF (`var`/positive constant); this one only needs positivity,
allowing arbitrarily compound right children as long as their positivity is provable by OTHER
means (a derivative argument, an algebraic identity, whatever — `growthCompetitionWitness`'s own
right children are the concrete witness that this genuinely expands the reachable class, not just
restates it).

**Verified, not just asserted**: `growthCompetitionWitness_EMLPfaffianValidOn_via_general`
re-derives cont. 28's hand-built result EXACTLY through the new general machinery — confirms the
generalization captures the same content.

**Honestly checked and left open**: whether any OTHER tree already built in this arc satisfies
`RightChildrenEverywherePositive`. Every other compound-tree investigation here
(`EMLZeroCrossingDomainSplit*.lean` and its many variants) DELIBERATELY explores trees whose right
children DO cross zero — the interesting, hard case this predicate structurally excludes by
design (checked the most memory-famous blocking example, the `WitnessResidualCancellation.lean`
"conspiratorial cancellation" counterexample, but it's already known-harmless since it's CONSTANT,
outside the residual's own hypotheses — not a genuine second application, just ruled out). Whether
a genuinely NEW, non-constant tree exists that's compound AND covered by this predicate is real,
unexplored future work — this round's honest scope was confirming the generalization is SOUND and
reproduces the known result, not hunting for a second instance.

Full `lake build MachLib` passes (427 modules). `#print axioms`, checked from a genuinely FRESH
rebuild (not a stale-cache read, per the gotcha above): zero `sorryAx`, no dependence on
`eml_pfaffian_validon_from_sin_equality`.

## 2026-07-21 (cont. 30) — the CLOSURE THEOREM itself generalized: a two-tree result becomes an
infinite-family one; a real factual error caught and fixed in the previous round's own docs

**Direct user request: "proceed please."** Cont. 29 generalized the VALIDITY derivation
(`RightChildrenEverywherePositive` ⟹ `EMLPfaffianValidOn`) but left the CLOSURE theorem itself
(`eml_depth2_witness_of_const_gt_one_sibling_growthCompetition`) specific to
`growthCompetitionWitness`. Checked whether that specificity was load-bearing — it wasn't:
the proof never touches anything about `growthCompetitionWitness` beyond feeding its
`EMLPfaffianValidOn` into `eml_T1eq_of_const_sibling_le_zero` and `T1_not_eq_log_c2_plus_sin_
given_validon`, BOTH already tree-agnostic. Restating the closure to take `RightChildrenEverywhere
Positive T1` directly, for an ARBITRARY `T1`, turns a two-tree result into an infinite-family one:
`eml_depth2_witness_of_const_gt_one_sibling_right_children_everywhere_positive`. ANY tree
satisfying the predicate — not just this one construction — can never be part of a witness-finding
counterexample. Verified (not just asserted) via a sanity-check corollary reproducing the
`growthCompetitionWitness`-specific closure exactly.

**A real factual error caught and fixed, worth recording precisely.** Cont. 29's own docstring
claimed `RightChildrenSimplePositive` trees "trivially satisfy" `RightChildrenEverywherePositive`
too, calling the new predicate "strictly more general." FALSE — checked `RightChildrenSimplePositive`'s
actual definition (`WitnessResidualSimpleRightChildren.lean`) directly rather than trusting the
earlier characterization, and it explicitly allows a bare `var` as a right child
(`t2 = EMLTree.var ∨ ...`). `var.eval x = x` is NOT positive for `x ≤ 0` — so a
`RightChildrenSimplePositive` tree with a `var` right child does NOT satisfy `RightChildrenEverywhere
Positive`. That predicate's own closure mechanism (`eml_witnesses_of_right_children_simple_positive`)
only ever needs a SINGLE-POINT witness (`EMLWitnesses A x0` at some `x0 > 0`), not uniform
positivity — a genuinely DIFFERENT technique, not a weaker case of this one. The two predicates
are INCOMPARABLE — neither contains the other — not a subsumption in either direction. Corrected
both the module docstring and the predicate's own doc-comment in the same commit. Caught by simply
re-reading the source definition instead of trusting an earlier paraphrase — the same discipline
("verify against source, not memory/assumption") that's paid off repeatedly throughout this whole
arc, this time catching an error in THIS session's own prior work rather than inherited confusion.

Full `lake build MachLib` passes (427 modules). `#print axioms`, checked from a genuinely fresh
rebuild per the stale-cache lesson from cont. 29: zero `sorryAx`, no dependence on
`eml_pfaffian_validon_from_sin_equality` on either new theorem.

## 2026-07-21 (cont. 31) — digging hard for a second concrete `RightChildrenEverywherePositive`
tree: found, verified, structurally closed (bounded + non-simple); non-monotonicity mapped in
full but genuinely harder than `growthCompetitionWitness`'s own, left open with a precise plan

**Direct user request: "no second concrete tree... has yet been found... can we dig into this
hard please."** Took this literally — searched the SAME limited combinatorial space
(compositions of `boundedNonConstantWitness` and `E(c) := eml(BNCW c)(const1)`, the two "safe,
bounded, positive" building blocks available) for a structurally different non-monotonic tree.

**Two dead ends, ruled out RIGOROUSLY not just abandoned.** `eml(E c1)(E c2)` (`exp(exp(BNCW c1))
- BNCW c2`, double-exp vs zero-exp) is numerically monotonic — the double-exp side dominates too
strongly. `eml(BNCW c1)(BNCW c2)` directly (no wrapper) is UNBOUNDED (BNCW's own infimum is `0`,
approached not attained, so the outer `log` blows up) — falls into the already-closed
"unbounded-`T1`" case, not new ground. The SYMMETRIC `exp(BNCW c1) - exp(BNCW c2)` (both
single-wrapped) looked non-monotonic on an INITIAL float64 scan across ~28 parameter pairs — but
this was a FALSE POSITIVE, confirmed by re-checking at `mpmath` 30-digit precision: every pair
tested was actually monotonic, matching an independent analytical proof (`∂/∂q[q/(E-q)²] =
(E+q)/(E-q)³ > 0`, so the relevant bracket never changes sign). Numeric noise near a flat
asymptotic tail (differences `~1e-10`) had been indistinguishable from a genuine sign change at
float64 — a real, useful gotcha for future numeric exploration in this arc, recorded precisely.

**The winning construction**: `exp(exp((BNCW c1).eval x)) - exp((BNCW c2).eval x)` — DOUBLE-exp(c1)
vs SINGLE-exp(c2), the "one-level-asymmetric" pattern that made `growthCompetitionWitness` work,
shifted up one level. Confirmed genuinely non-monotonic at high precision for `c1=1.5, c2=2.0`: a
SINGLE local maximum near `x≈-2.2` (a different SHAPE from `growthCompetitionWitness`'s
local-max-then-local-min — one hump, not two turning points), with clean closed-form asymptotic
limits (`e-1` as `x→∞`).

**Fully closed this round** (`WitnessResidualGrowthCompetitionDeepWitness.lean`): the tree's
structure and clean `eval` formula, `RightChildrenEverywherePositive` (trivial, same building
blocks), boundedness both directions (same crude-additive-bound technique as
`growthCompetitionWitness`'s own), and non-`RightChildrenSimplePositive` (same
`EMLTree.noConfusion` argument). Combined into `growthCompetitionWitnessDeep_partial_exists` —
already sufficient, via cont. 30's GENERAL closure theorem, to show this tree can never be a
witness-finding counterexample, for ANY valid `c1,c2`.

**Substantial additional progress on non-monotonicity** (`WitnessResidualDeepGSignControl.lean`):
derived and NUMERICALLY VERIFIED (finite differences vs. the formula, `mpmath`, matching to 15+
digits — same discipline as `growthCompetitionWitness`'s own derivative work) the exact raw
derivative: `T'(x) = exp(x)·E·g(E)`, `g(E) := q/(E-q)² - exp(E/(E-p))·p/(E-p)²`. Unlike
`growthCompetitionWitness`'s analogous quantity, `g` retains a genuine transcendental factor
`exp(E/(E-p))` that clearing denominators cannot remove — `quadratic_neg_between`/`quadratic_pos_
below_vertex` don't apply. Built the ANALOGOUS sign-control tool via a different, arguably
simpler route: rather than exploiting convexity, showed each of `g`'s two terms is monotonic
(decreasing) in `E` DIRECTLY via pure order theory (no derivative of `g` needed at all) — `term1
:=q/(E-q)²` decreasing via cross-multiplication (squaring preserves order on nonnegatives);
`term2:=exp(E/(E-p))·p/(E-p)²` decreasing via `E/(E-p)` decreasing (cross-multiplication) then
`exp` of a decreasing function (monotone composition) times `p/(E-p)²` (same fact as `term1`),
product of two nonnegative decreasing functions being decreasing. `g_lower_bound_on_interval`/
`g_upper_bound_on_interval` then bound `g` throughout an interval using the WORST-CASE corner —
exactly `quadratic_neg_between`'s "no monotonicity of the target itself required" trick, applied
to a genuinely transcendental function instead of a quadratic.

**What remains, stated precisely** (not attempted past this point, deliberately — the numeric
piece is a real escalation in scope, not routine engineering this time): (1) `HasDerivAt`
composition for `T_D` (one more `exp` layer than `growthCompetitionWitness` needed, otherwise
direct reuse of `boundedNonConstantWitness_hasDerivAt`); (2) an identity connecting the raw
derivative to `exp(x)·E·g(E)` (more direct than `growthCompetitionWitness`'s own
`clear_denom_identity`, since `g` is ALREADY in cleared form here — no further polynomial
reduction needed, just the composition algebra); (3) NEW numeric axioms bounding `exp` at the
SPECIFIC `E/(E-p)` values arising at chosen witness `E`-points — genuinely new machinery,
`growthCompetitionWitness` never needed to bound `exp` beyond the trivial `exp(0)=1`; (4) the
`E`-to-`x` translation and final `strictMono`/`strictAnti` assembly — a close structural match to
`growthCompetitionWitness`'s own, reusable with parameter substitution. Piece (3) is the
genuinely hard, new difficulty; the rest is mapped, analogous work.

**A real Lean gotcha hit while building `g_lower_bound_on_interval`/`g_upper_bound_on_interval`,
worth recording**: applying `term1_decreasing`/`term2_decreasing` with the explicit hypothesis
arguments alone repeatedly picked the WRONG implicit `E1, E2` assignment (unifying against the
hypotheses' own types before consulting the expected goal type) — silently producing "expected
type X, got type Y" errors that looked like hypothesis mismatches rather than an inference-order
issue. Fixed by supplying `E1 := ...`/`E2 := ...` explicitly at every call site rather than
relying on inference. Combined with the discipline (from cont. 29) of forcing a clean rebuild plus
a fresh `#print axioms` after every "Build completed successfully" — applied throughout this round
as a precaution, catching real compile errors promptly rather than letting them surface later.

Full `lake build MachLib` passes (429 modules). `#print axioms`, checked from genuinely fresh
rebuilds throughout: zero `sorryAx`, no dependence on `eml_pfaffian_validon_from_sin_equality`
anywhere in this round's new work.

## 2026-07-21 (cont. 32) — `growthCompetitionWitnessDeep`'s FULL derivative machinery built and
verified; concrete witness points pinned down with real margins; only the final numeric-bound
layer and E-to-x/assembly remain, precisely scoped

**Direct user request: "proceed into that please"**, continuing cont. 31's precisely-scoped
non-monotonicity work. Built essentially the ENTIRE derivative pipeline this round — matching
cont. 26+27's whole scope for `growthCompetitionWitness`, but one `exp` layer deeper and with a
genuinely transcendental (not pure-algebra) term surviving throughout.

**`growthCompetitionWitnessDeep_hasDerivAt`** (`WitnessResidualDeepDeriv.lean`): three layers of
`HasDerivAt_comp` (`exp(A)`, `exp(exp(A))`, `exp(B)`) then `HasDerivAt_sub`, reusing
`boundedNonConstantWitness_hasDerivAt` unchanged for both `A` and `B`. Hit a genuinely new
wrinkle: `HasDerivAt_comp`'s natural output associates the derivative value as `b·(a₁·a₂)` once
`a` is itself already a product from a prior composition step — NOT `(b·a₁)·a₂`. Rather than
fighting this per-step, used `HasDerivAt_of_eq` to re-anchor both function and value to a clean,
uniform shape immediately after EACH composition, so associativity mismatches never compound
across layers — a technique worth remembering for any FUTURE multi-layer composition in this
codebase.

**`growthCompetitionWitnessDeep_deriv_clear_denom`**: `T_D'(z)·(E-p)²·(E-q)² = exp(z)·E·[q·(E-p)²
- U·p·(E-q)²]`, `U := exp(E/(E-p)) = exp(exp(A(z)))`. Verified numerically (random substitution
respecting the four defining constraints, THEN a finite-difference ground-truth check for the
concrete `c1=1.5,c2=2.0` instance) before any Lean. Built via an ABSTRACT `deep_clear_denom_
identity`, `U` staying opaque throughout (genuinely transcendental — no amount of clearing removes
it), substituting `exp(A(z)), A'(z), exp(B(z)), B'(z)` via their own already-proven multiplied-out
facts (`exp_A_mul_denom`, `deriv_A_mul_denom` — REUSED UNCHANGED from `growthCompetitionWitness`'s
own file, since `A, B` are the identical `boundedNonConstantWitness` objects). Needed `set_option
maxHeartbeats 1000000` — the extra substitution layer genuinely pushes past `mach_mpoly`'s default
budget, a real complexity increase over the original tree's identical-in-spirit identity. One
piece `growthCompetitionWitness` never needed: `exp_A_eq_ratio`, isolating `exp(A(z)) = E/(E-p)`
via division (not just the multiplied form) — needed to express `U` explicitly.

**The sign bridge** (`growthCompetitionWitnessDeep_deriv_neg_of_quad_neg`/`_pos_of_quad_pos`):
divides the cleared identity back out through the known-positive `(E-p)²·(E-q)²`, reusing
`neg_of_mul_neg_pos`/`pos_of_mul_pos_right` UNCHANGED from `growthCompetitionWitness`'s own sign
bridge.

**Concrete witness points, pinned down numerically with real margins** (not yet in Lean — this is
the piece left for next round): the naive choice of a WIDE interval for the negative region (e.g.
`[1.3, 3.0]`, which had a comfortable margin at growthCompetitionWitness's own quadratic tool)
turned out TOO LOOSE here — the `term1`/`term2` "worst-case corner" trick is looser for this
transcendental `g` than for a quadratic, since `term2` (`U`-weighted) moves faster across a wide
range. Found workable, comfortably-margined intervals by narrowing: **positive region `E ∈
[1.02, 1.03]`** (worst-case bound `term1(1.03)-term2(1.02) ≈ +0.409`, robust across a `±0.0005`
box on `p := log(1.5), q := log(2.0)`) and **negative region `E ∈ [1.48, 1.52]`** (worst-case
bound `term1(1.48)-term2(1.52) ≈ -0.152`, same robustness check) — centered near `g`'s actual
minimum (`≈-0.268` at `E≈1.5`, from the earlier numeric survey) rather than spread across
`g`'s whole negative range, since narrower intervals give tighter (hence more robust) corner
bounds for THIS transcendental target. The needed `exp(E/(E-p))` arguments at these witnesses
are narrow ranges themselves (`≈1.658–1.661` at `E=1.02`; `≈1.363–1.365` at `E=1.52`) — meaning
the FINAL numeric axioms needed are tight `exp`-value brackets at these two specific small
ranges, on top of the already-familiar `log(1.5)`/`log(2.0)` bracket axioms.

**What remains, precisely** (not attempted past this point): (1) two new numeric axioms bracketing
`log(1.5)` and `log(2.0)` (same style as `growthCompetitionWitness`'s `log_2_2_bounds`/`log_2_7_
bounds`); (2) two new numeric axioms bracketing `exp` at the specific narrow ranges above — the
GENUINELY new piece, needing the log-bounds to first pin down `E/(E-p)`'s range via interval
arithmetic through a rational function, THEN bound `exp` there; (3) instantiate `g_lower_bound_
on_interval`/`g_upper_bound_on_interval` at the four witness `E`-values, connecting to the sign
bridge; (4) the `E`-to-`x` translation (`exp_exp_log_log`/`log_log_mono`/`exp_exp_mono`, ALL
already built and REUSABLE unchanged from `WitnessResidualGrowthCompetitionAssembly.lean`) and
final `strictMono`/`strictAnti` + non-monotonicity assembly — a close structural match to
`growthCompetitionWitness`'s own, differing only in which concrete facts get plugged in.

Full `lake build MachLib` passes (430 modules). `#print axioms`, checked from genuinely fresh
rebuilds throughout: zero `sorryAx`, no dependence on `eml_pfaffian_validon_from_sin_equality`
anywhere in this round's new work. Three commits this round (`f3fa5d62`, `0bcd31f7`, plus this
docs commit), all pushed.

## 2026-07-21 (cont. 33) — `growthCompetitionWitnessDeep 1.5 2.0` FULLY CLOSED: second witness
tree, transcendental derivative, non-monotonicity proven end to end

**Direct user request: "proceed into that please"** (twice), continuing cont. 32's precisely
scoped remaining work. Closed all four remaining pieces this round.

**`WitnessResidualDeepNumeric.lean`** — pieces (1) and (2) from cont. 32's scope. Four numeric
axioms: `log_1_5_bounds`, `log_2_0_bounds` (same style as the first tree's own log-bound axioms),
plus `exp_1_7_upper : exp(1.7) < 5.4740` and `exp_1_35_lower : 3.8570 < exp(1.35)` — the genuinely
new piece. Key simplification found this round: rather than axiomatizing `exp` at the EXACT
irrational argument `E/(E-p)`, bound that argument by a clean round number with comfortable slack
(`1.02/(1.02-log 1.5) < 1.7`, `1.35 < 1.52/(1.52-log 1.5)`) and axiomatize `exp` AT the round
number instead. Avoids ever needing `exp` axiomatized at a parameter-dependent argument — a
technique worth reusing for any future transcendental-derivative witness tree. One monotonicity
fact discovered necessary mid-round, not anticipated in cont. 32's scoping: `term1_increasing_in_q`
(`q/(E-q)²` increasing in `q`, not just decreasing in `E` — needed because `log(1.5)`/`log(2.0)`
are only known via interval bounds, so the numerator argument itself needs order control too).
`deep_g_pos_witness`/`deep_g_neg_witness` (the two corner-point sign facts) verified sorryAx-free.

**`WitnessResidualDeepAssembly.lean`** — pieces (3) and (4), completing the arc. The one piece
with NO analogue in the first tree's assembly: `g_to_hquad_pos`/`g_to_hquad_neg`, bridging `g`'s
fractional form to the cleared `hquad` numerator form the sign-bridge theorems expect (combine
over a common denominator via `div_sub_div`, then match quotient sign to numerator sign since the
denominator's positivity is known unconditionally — no case split needed). `deep_g_pos_on_interval`
/`deep_g_neg_on_interval` extend the corner-point witnesses to the FULL interval via
`g_lower_bound_on_interval`/`g_upper_bound_on_interval` (built in cont. 31). Everything past that
— `E`-to-`x` translation, `strictMono_of_deriv_pos`/`strictAnti_of_deriv_neg`, the two-disjoint-
witness-pairs non-monotonicity argument, final packaging — is a DIRECT structural mirror of
`WitnessResidualGrowthCompetitionAssembly.lean`, including reusing `exp_exp_log_log`/`log_log_mono`
/`exp_exp_mono` UNCHANGED (generic to any `exp(exp x)`-parameterized family, not tree-specific).

**`growthCompetitionWitnessDeep_1_5_2_0_exists`**: six conjuncts — bounded both directions,
non-`RightChildrenSimplePositive`, `RightChildrenEverywherePositive`, non-monotonic both
directions. Verified sorryAx-free from a genuinely fresh rebuild: depends only on the foundational
`HasDerivAt`/`exp`/`log` axiom calculus, Rolle's theorem, and the four numeric axioms above —
nothing else, no dependence on `eml_pfaffian_validon_from_sin_equality`.

**Net effect on Option D**: TWO structurally distinct trees now confirmed to satisfy
`RightChildrenEverywherePositive` with fully proven non-monotonicity — `growthCompetitionWitness`
(pure-algebra derivative, quadratic sign argument) and `growthCompetitionWitnessDeep`
(transcendental derivative, genuinely different closure technique). This is real evidence the
witness-finding residual is broader than a single example, and that the "corner-bound + round-
number `exp` axiomatization" technique built this round generalizes to future transcendental-
derivative witnesses beyond quadratics.

Full `lake build MachLib` passes (432 modules). `#print axioms`, checked from genuinely fresh
rebuilds throughout (including the final assembly theorem itself): zero `sorryAx`, no dependence
on `eml_pfaffian_validon_from_sin_equality` anywhere in this round's new work. Two commits this
round (`66bb6f81`, `d55aaa84`, plus this docs commit), all pushed.

## 2026-07-21 (cont. 34) — RESEARCH, no Lean this round: mapping the "no-clamp ⟹
`EMLPfaffianValidOn` is free" mechanism's actual reach, per the honest open question flagged at
the end of cont. 28/31 — finding: a SECOND, largely disconnected mechanism already exists

**Direct user request**: assess "how much of the original general tree-depth induction (arbitrary
compound trees, not just `RightChildrenEverywherePositive` ones) does the no-clamp mechanism
actually reach" — explicitly framed as research, not routine engineering. No Lean written this
round; this is a survey + a concrete, scoped finding for whoever picks up the next round.

**Part 1 — `RightChildrenEverywherePositive`'s reach is real but structurally narrow.** Re-read
its definition precisely (`WitnessResidualRightChildrenEverywherePositive.lean:82`): recursive
over BOTH children (`RCEP t1 ∧ RCEP t2 ∧ ∀x,0<t2.eval x`) — meaning `var` can NEVER appear as a
right child ANYWHERE in the tree, at any depth, since `var.eval x = x` isn't positive for `x≤0`.
Left children (and left-spines built from them) are unrestricted in CONTENT but must themselves
recursively satisfy the same right-child constraint. The one universally-safe recipe this arc has
found and reused (`eml P (const 1)` is `exp(P.eval x) - log 1 = exp(P.eval x) > 0` for ANY `P`,
no constraint on `P` needed) is why `boundedNonConstantWitness`/`E_BNCW`-style trees qualify. Net
effect: the class is "trees where every right-branch point is capped by a positive-constant-style
wrapper instead of exposing raw content" — real and useful (two structurally different witnesses
now live in it), but inherently excludes any tree with a genuinely load-bearing, sign-changing
right child anywhere — which is most of the "interesting" compound-tree space.

**Part 2 — a SECOND mechanism already exists, built for exactly this gap, and it's currently
disconnected from the witness-finding closure.** `EMLZeroCrossing*.lean` (10 files:
`Depth1`/`Depth2Compound`/`Depth3Compound`/`DomainSplit`(+`General`)/`BothCompound`(+`Deeper`,
+`General`,+`DeeperGeneral`)/`ConvexT1`) is explicitly self-described as "Continuation of path (1)"
— this IS the original general tree-depth induction, just via ELEMENTARY calculus (Rolle +
derivative monotonicity) instead of the Khovanskii/Pfaffian-chain route, entirely bypassing
`EMLPfaffianValidOn`. Its headline theorems (e.g. `eml_const_evarConstC2_boundedZeros`,
`WitnessResidualChainSkeleton.lean`-analogue-shaped) prove `∀ a b, zeros of (eml t1 t2).eval on
(a,b) ≤ [literal constant]` — genuinely UNIFORM, interval-length-INDEPENDENT bounds, confirmed by
reading the actual type signatures (not just docstrings), e.g. `eml_const_evarConstC2_boundedZeros
(c1 c2 : Real)(hc2:1<c2)(a b:Real) : ∀ zeros, ... → zeros.length ≤ 4` — `a,b` universally
quantified, `4` a bare literal. The capstone, `eml_convexT1_conditionT2_boundedZeros`
(`BothCompoundDeeperGeneral.lean`): `t1` convex + `t2` sign-crossing-with-a-structural-condition
⟹ `eml T1 t2` has `≤3` zeros on ANY interval, `M` auto-discharged.

**Why this matters, precisely.** `zeros of (eml T1 (const K)).eval x = 0` is EXACTLY `zeros of
T1.eval x = log K` — the SAME quantity `WitnessResidualChainSkeleton.lean`'s `T1_not_eq_log_c2_
plus_sin_given_validon` needs a bound on (there, supplied by `combinedBoundE`, which NEEDS
`EMLPfaffianValidOn T1`). If ANY of these elementary bounds applied to `T1 := const K`'s role,
plugging a LITERAL bound straight into an analogous "no validity needed" version of that theorem
would close the residual for that `T1` shape with ZERO `EMLPfaffianValidOn` dependency — not just
avoiding the hard case-split machinery (RightChildrenEverywherePositive's own trick), but avoiding
`EMLPfaffianValidOn`/the Khovanskii encoder ENTIRELY.

**Checked whether this composition is already wired anywhere — it is NOT.** Import-graph search:
zero files both depend on `EMLZeroCrossing*` AND feed a bound into `WitnessResidualChainSkeleton`/
`WitnessResidualTargetGeneric`-style closure. The two mechanisms (RightChildrenEverywherePositive
and the elementary zero-crossing family) have run as fully independent threads since roughly
cont. 19–24 (crossing family, elementary "constant on a ray" trick, unrelated to both) diverged
from cont. 25+ (growthCompetitionWitness, RightChildrenEverywherePositive). `EMLZeroCrossing*`'s
own uniform bounds have never been consumed by anything outside their own files.

**The concrete gap, characterized exactly.** The family has `eml_const_genericT2_boundedZeros`
(const `t1`, generic sign-crossing `t2`) and `eml_genericT1_genericT2_boundedZeros`/`eml_convexT1_
conditionT2_boundedZeros` (generic/convex `t1`, generic sign-crossing `t2`) — but NO "generic
(or convex) `t1`, CONSTANT `t2`" variant. That's the one actually needed for the `log K`-target
application (a constant `t2` has no crossing point to domain-split on at all — a structurally
different, in fact SIMPLER argument: `d/dx[eml T1 (const K)] = exp(T1eval x)·T1deriv(x)` exactly
— zero iff `T1deriv(x)=0`, so if `T1` is convex on `(x0,b)`, `expMul_atMostOneZero_of_convex`
(`EMLZeroCrossingConvexT1.lean`, ALREADY built, explicitly "independent of `log`/`eml`/this
investigation entirely") gives `≤1` critical point directly, then `zero_count_bound_by_deriv`
(Rolle, used everywhere in this family) lifts that to `≤2` zeros of `eml T1 (const K)` on
`(x0,b)` — the SAME "nearly free, pure wiring" pattern `EMLZeroCrossingDepth3Compound.lean`
already demonstrated for a different composition. Realistically ~20–50 lines, no new mathematical
content, matching this arc's own established estimate style.

**The honest limit of even that, checked before recommending it as "the" next step.** A function
that's CONVEX on ALL of ℝ and non-constant is necessarily unbounded (basic real analysis) — so a
`eml_convexT1_const_boundedZeros`-style theorem, built exactly as scoped above, would only ever
supply a BOUNDED `T1` if convexity is restricted to a sub-ray `(x0,b)` (matching every existing
theorem's own shape) with the LEFT region handled separately (clamp/constant, the same recipe used
throughout this family) — meaning: closing a genuinely NEW witness this way still needs a
NEW CONCRETE bounded, non-monotonic `T1` construction with a provably-eventually-convex-or-concave
derivative and a right child that GENUINELY crosses zero (not `RightChildrenEverywherePositive`) —
not yet searched for, numerically or otherwise. `growthCompetitionWitness`/`growthCompetitionWitness
Deep` themselves don't qualify as NEW targets for this route (their right children are ALREADY
globally positive by construction — that's what got them closed via the other mechanism).

**Net assessment, stated as plainly as the question was asked.** The no-clamp/`RightChildrenEverywhere
Positive` mechanism's reach is real but narrow (no `var` ever as a right child, anywhere). It does
NOT, by itself, meaningfully close the general tree-depth induction. But a SECOND mechanism
(elementary zero-crossing bounds, `EMLZeroCrossing*.lean`, unconnected until now) already covers a
different, complementary slice — and even at ITS most general point (`eml_convexT1_condition
T2_boundedZeros`), it structurally cannot reach bounded, non-monotonic `T1` with a crossing right
child without a further "generic-`t1`-plus-const-`t2`" theorem (scoped above, not yet built) AND a
brand-new concrete witness tree (not yet searched for). The fraction of "arbitrary compound trees"
covered by everything built so far — RightChildrenEverywherePositive class ∪ the elementary
zero-crossing family's actual (currently unconnected) shapes ∪ the "crossing family"/"constant
on a ray" elementary trick — is genuinely larger than any one mechanism alone suggests, but still
far from "arbitrary compound tree," and no single remaining piece would close it in one round.
Two concrete, honestly-scoped next steps for whoever continues, in order of effort: (1) build
`eml_convexT1_const_boundedZeros` + the "no validity needed" closure analogue (small, mechanical,
high-confidence); (2) search for a genuinely new bounded/non-monotonic/crossing-right-child `T1`
to plug into it (open-ended, numeric-first per house style, comparable in scope to the original
`growthCompetitionWitness` hunt).

No files changed, no build run — pure research/survey round, recorded here so the next session
doesn't have to re-derive the import-graph check or re-read the ten `EMLZeroCrossing*.lean`
signatures from scratch.

## 2026-07-21 (cont. 35) — item (1) from cont. 34 built: the elementary zero-crossing family is
now WIRED into the witness-finding closure, a second, fully independent mechanism confirmed to
work via a genuinely fresh `#print axioms`

**Direct user request**: "yes please" to starting item (1) from cont. 34's scoped next steps.
`WitnessResidualConvexZeroBoundClosure.lean` closes it in one round.

**The bound** (`convexT1_sub_const_atMostTwoZeros`): the one shape `EMLZeroCrossing*.lean` didn't
have — generic/convex `t1`, CONSTANT `t2` (every existing generic-`t1` theorem there needs `t2`
to have a genuine sign crossing to domain-split on; a constant `t2` has none). Turned out simpler
than scoped: no `exp`/`log` wrapping needed at all. The cont. 34 write-up's own sketch mistakenly
modeled the target quantity as `exp(t1eval x) - log K`, mirroring the EML-tree-eval SHAPE `eml t1
(const K)` — but the ACTUAL quantity the target-shift argument needs a bound on is `T1eval(x) - L`
DIRECTLY (`L := log c2`), not an `eml`-wrapped version of it. Caught this BEFORE writing any Lean,
by re-deriving on paper what `no_tree_eq_target_given_validon` actually bounds — a genuine
simplification, and a good instance of why "verify on paper first" catches real design errors,
not just algebra slips. `t1eval` convex on `(c,d)` ⟹ `t1deriv` strictly increasing (from
`t1deriv2>0`) hence injective hence `≤1` zero (`atMostOneZero_of_strictMono` +
`strictMono_of_deriv_pos`, both pre-existing); Rolle (`zero_count_bound_by_deriv`) lifts that to
`≤2` zeros of `t1eval - L` itself — genuinely "nearly free wiring," as scoped.

**The closure** (`no_tree_eq_target_given_zero_bound`): same `M+1`-witness-points-at-`kπ`
construction as `no_tree_eq_target_given_validon`, `M` supplied directly by the caller instead of
derived via `enc`/`combinedBoundE` — so `EMLPfaffianValidOn`/`LogArgPosOn`/the Khovanskii encoder
never appear anywhere. Also dropped `hTargetPi1` (the original's non-degeneracy witness) entirely
— purely an artifact of `enc_combinedBound`'s own API; a convex/bounded-critical-point `T1eval`
can't be identically `L`, so nothing separate is needed here. `eml_depth2_witness_of_const_gt_
one_sibling_convexT1` mirrors `..._right_children_everywhere_positive`'s shape exactly, substituting
this mechanism for that one.

**Verified, not just claimed**: `#print axioms`, from a genuinely fresh rebuild (`rm .olean/.c` +
rebuild + `lake env lean` on a scratch import), confirms `eml_depth2_witness_of_const_gt_one_
sibling_convexT1` depends on nothing beyond the foundational `HasDerivAt` axiom calculus, Rolle's
theorem, and `sin`/`pi`'s own basic axioms — grepped the FULL output for `EMLPfaffianValidOn`/
`eml_pfaffian_validon_from_sin_equality`/`sorry`: none appear. This is a real, independent,
COMPILED confirmation of the cont. 34 hypothesis — a second, fully disconnected mechanism
genuinely closes this residual, for tree shapes `RightChildrenEverywherePositive` structurally
cannot reach (convex `T1`, not built from never-clamping right-child wrappers).

**Sanity check, same discipline as every prior generalization in this arc**:
`eml_var_const_c1_witness_via_convexT1` instantiates the whole pipeline on a genuine `EMLTree`
(`T1 := eml var (const c1)`, convex everywhere since `t1deriv=t1deriv2=exp`), confirming it
composes end to end and not just type-checks in the abstract. Honestly NOT new residual coverage
on its own — this `T1` is unbounded above, already closed by the far easier "unbounded-T1" case —
its only job is confirming the machinery is real.

**What's still open, unchanged from cont. 34's own honest limit**: a function convex on ALL of
`(1,∞)` and non-constant is necessarily unbounded (basic calculus) — so reaching genuinely NEW
residual coverage (a bounded, non-monotonic `T1` with a crossing right child, not reachable via
`RightChildrenEverywherePositive` either) still needs a fresh concrete witness construction, not
attempted this round. That remains item (2) from cont. 34's scoping, open-ended, comparable to
the original `growthCompetitionWitness` hunt.

Full `lake build MachLib` passes (433 modules, up from 432). One commit this round (`3f0c0d06`,
plus this docs commit), pushed.

## 2026-07-21 (cont. 36) — item (2) attempted: numeric exploration only, a real negative finding
— existing crossing-family constructions are structurally the WRONG shape for the new mechanism,
and the natural fix just reproduces the OLD mechanism instead

**Direct user request: "proceed"**, continuing to item (2) from cont. 34/35's scoping — hunt a
genuinely new bounded, non-monotonic `T1` with a crossing right child (not
`RightChildrenEverywherePositive`) to actually exploit `WitnessResidualConvexZeroBoundClosure.lean`.
No Lean written this round — numeric exploration (`mpmath`, 50 digits) surfaced a real structural
obstacle worth recording before committing further rounds to this specific hunt.

**A general fact, checked and confirmed numerically, not just argued**: for `eml A B` with `B`
having a genuine, continuous sign crossing at some finite `x0` (`B(x0)=0`, `B>0` just before,
`B≤0` just after, say), the whole tree is FORCED unbounded near `x0` from the side where `B>0`:
`-log(B) → +∞` as `B→0+` (continuity of `B` guarantees it passes through arbitrarily small
positive values approaching the crossing), and nothing in `exp(A)` (bounded contribution near a
fixed point) can cancel a term diverging to `+∞`. Verified directly on `nonMonotonicWitness`
(`WitnessResidualNonMonotonic.lean`) itself — sampled `T.eval` at `x0 + d` for `d` from `1e-6` up
to `2`: **not bounded**, `T(x0+10⁻⁶) ≈ -2.09`, growing steadily MORE negative as `d→0` (a slow,
log-of-log divergence, easy to miss at coarse sampling resolution — `T(x0+10⁻³) ≈ -1.53` looks
almost like a local minimum until you sample closer). `nonMonotonicWitness` is genuinely unbounded
below, contrary to what a casual glance at its shape (a single dip-then-recover, `T` decaying back
to `0` on BOTH far ends) might suggest.

**The natural "absorb the blow-up one level up" idea, checked and it doesn't help.** Wrapping the
whole thing one level deeper (`T2 := eml (const k) T`) does successfully turn the divergence into
a bounded contribution — `T`'s negativity gets CLAMPED by the outer `log`, so `T2` becomes
literally CONSTANT (`= exp k`) throughout the WHOLE region where `T ≤ 0`. Numerically confirmed
this region is `(-∞, x0+0.893...]` — i.e. an entire unbounded ray again (`T` dips negative right
after `x0`, stays negative until crossing back to positive once around `x0+0.89`, never dipping
negative again out to `x=20` in the scan). **This is exactly the "constant on an unbounded ray"
shape the cont. 24 mechanism already closes** — so `T2` isn't new ground either, just a
differently-dressed instance of the SAME already-covered family. The clamp-absorption trick that
makes crossing constructions bounded seems to inherently produce eventually-constant behavior,
not the "approaches a limit without ever being flat" shape (like `boundedNonConstantWitness`'s own
asymptotic behavior) that would be needed to escape BOTH existing mechanisms at once.

**What this suggests, stated as a hypothesis, not a proof**: escaping both `RightChildrenEverywhere
Positive` (needs no crossing right child anywhere) and the cont. 24 "constant on a ray" mechanism
(needs the crossing's clamp-absorbed region to be bounded, not a half-line) likely needs a right
child with a DOUBLE zero-crossing — i.e., a subtree that goes non-positive on a BOUNDED interval
only, sandwiched between two crossings, not a half-line. If wrapping such a doubly-crossing `B` one
level up (`eml (const k) B'` for some derived `B'`), the resulting non-positive region would be
bounded, not a ray — avoiding the "eventually constant" trap. NOT attempted this round: doubly-
crossing constructions are structurally more involved (need TWO transition points tracked, likely
non-monotonic in a more complex way than anything built so far in this arc) and deserve their own
numeric-first exploration pass, not a rushed extension of this one.

**Honest status of item (2)**: genuinely harder than the "comparable in scope to
`growthCompetitionWitness`" estimate from cont. 34/35 suggested. That estimate was based on
`growthCompetitionWitness`'s OWN search (which found a working construction within one round, cont.
25) — but that search was hunting for ANY bounded non-monotonic tree with no constraint on its
mechanism; THIS search additionally needs the tree to escape TWO already-built closure mechanisms
simultaneously, a strictly harder target. Recommending a pause on this specific thread rather than
continuing to force it — the double-crossing idea above is a real, scoped next attempt if picked
back up, but warrants its own dedicated numeric exploration round, not a continuation of this one.

No files changed, no build run — pure numeric research, Python only (`mpmath`, 50-digit
precision), not committed to the repo (scratchpad only). Recorded here so the next session
doesn't re-derive `nonMonotonicWitness`'s actual (non-obvious, slowly-divergent) unboundedness or
re-discover that the naive one-level wrap reproduces the existing mechanism.

## 2026-07-21 (cont. 37) — MILESTONE: item (2) closed in the NEGATIVE, PROVEN not just observed
— a genuine right-child crossing forces unboundedness, for ANY tree built around it

**Direct user request: "keep going please"**, continuing past cont. 36's negative numeric
finding. Two things happened this round: (1) a fresh, more careful numeric construction (double
zero-crossing, engineered so BOTH tails of `growthCompetitionWitness` land above a threshold with
the local min dipping below it — parameters `c1=1.9, c2=2.3` found via a targeted sweep on the
closed-form asymptote formula, `left_tail = 1/(1-log c1) + log(1-log c2)`, `right_tail` always
exactly `1`) DID succeed at making the "constant" region genuinely BOUNDED, escaping the cont. 24
mechanism — but a fine-resolution scan right at both crossing points showed the SAME slow,
easy-to-miss divergence `nonMonotonicWitness` had (`T1` growing without bound: `4.27, 5.17, 5.99,
7.11...` approaching one crossing, `3.90, 4.61, 5.17, 5.67, 6.19, ..., 6.79...` approaching the
other) — confirming the obstruction is NOT specific to `nonMonotonicWitness`'s own construction.
(2) That convergent numeric evidence (now from THREE independent constructions) motivated turning
the pattern into an actual proof rather than continuing to search.

**The theorem** (`WitnessResidualCrossingUnbounded.lean`,
`eml_A_crossing_var_const_unbounded_above`): `eml A (eml var (const c))` (`c>1`) is unbounded
ABOVE for literally ANY `A` — no constraint on `A`'s shape, boundedness, or structure whatsoever.
The mechanism, worked out on paper before any Lean: `eml A B := exp(A) - log(B)`; `exp(A) ≥ 0`
ALWAYS, so it can never supply the `-∞` a cancellation of `-log(B) → +∞` (as `B→0⁺`) would need —
this part of the argument needs nothing about `A` at all. The witness is fully EXPLICIT, no
Taylor/derivative bound on `exp` needed: `eml var (const c)` is the literal algebraic inverse of
`log`, so for ANY target value `ε>0`, `x := log(ε + log c)` makes the right child EXACTLY `ε` (not
merely small — exact, in closed form). Setting `ε := exp(-(M+1))` for target `M` gives
`-log(right child) = M+1` exactly, and `exp(A.eval x) - (-(M+1)) ≥ M+1 > M`.

**Confirms cont. 36's finding is forced, not a fluke of one construction**:
`nonMonotonicWitness_N_unbounded_above` instantiates the general theorem at `A := eml var (const
1), c := 1+1` — EXACTLY `nonMonotonicWitness`'s own `N` node — showing its slow-divergence
unboundedness (numerically found in cont. 36) was never going to resolve with more careful
tuning; it's structurally forced by the crossing shape itself, independent of what's on the left.

**What this settles, precisely.** Item (2) from cont. 34/35's scoping — hunt a bounded,
non-monotonic witness with a genuinely crossing right child, to exploit
`WitnessResidualConvexZeroBoundClosure.lean` — is now CLOSED IN THE NEGATIVE for the crossing
shape this entire arc has ever actually built with (`eml var (const c)`, the only crossing
primitive used anywhere in the 40+-file investigation): no bounded tree can be built with this
crossing as a right child, anywhere in the structure, under any amount of wrapping. This is a
genuine, valuable research conclusion — not merely "we didn't find one," but "provably cannot
exist, for this construction primitive." Doesn't rule out every conceivable crossing shape (a
right child with a crossing but NO explicit closed-form inverse might behave differently — not
investigated, and no such primitive exists in this codebase to test against anyway).

**Net effect on Option D overall**: the residual's landscape is now sharper than at any point in
this arc. `RightChildrenEverywherePositive` (no crossing anywhere) closes one large class. The
"constant on an unbounded ray" mechanism (cont. 24) closes trees built from a crossing that ends
up flattening one whole ray. THIS round closes off the remaining natural attempt (a crossing that
DOESN'T flatten a ray) by showing it can't be bounded at all. Together these cover essentially
every construction pattern this arc's own toolkit can build — the open frontier is now squarely
either (a) a crossing subtree fundamentally different from `eml var (const c)` (not yet
identified, possibly not expressible in this EML grammar) or (b) accepting the residual's fully
general case needs the still-unresolved tree-depth induction from the ORIGINAL Option D framing,
not a cleverer witness search.

`sorryAx`-free, verified via a genuinely fresh rebuild: only foundational `MachLib.Real`
ordered-field/exp/log axioms, nothing else — no dependence on
`eml_pfaffian_validon_from_sin_equality`. Full `lake build MachLib` passes (434 modules, up from
433). One commit this round (`68a458d4`, plus this docs commit), pushed.

## 2026-07-21 (cont. 38) — digging into the original tree-depth induction, per direct request:
the crossing-unboundedness result generalized to ANY EML tree, via the real IVT

**Direct user request: "the original tree-depth induction from Option D's own framing — lets dig
into this please."** Cont. 37's theorem was still tied to one concrete crossing shape (`eml var
(const c)`); its proof mechanism (`exp(A)≥0` can't cancel `-log(B)→+∞`) never actually needed
`B`'s specific closed form — only that `B` could be driven to hit any target value. Removing that
dependency needed a genuine tool this arc had built but never exercised: the real Intermediate
Value Theorem.

**Found it already sitting in the codebase, unused for this purpose.** `IntermediateValue.lean`
(375 lines) proves a COMPLETE, in-model IVT (`intermediate_value`, from the completeness axiom
`sup_exists`, via a sup-construction and sign-preservation lemmas around `ContinuousAt`) plus a
`HasDerivAt`-friendly wrapper (`intermediate_value_of_hasDerivAt`) — built at some earlier point
in this codebase's history (Gate 2d / IFT gate work) but never once used anywhere in the whole
Option D witness-finding arc until this round.

**The generalized theorem** (`WitnessResidualCrossingUnboundedGeneral.lean`,
`eml_A_crossing_B_unbounded_above`): if `B.eval` crosses zero genuinely — `B(x0)=0`, `B(x1)>0`
for SOME `x0<x1`, differentiable throughout `[x0,x1]` — then `eml A B` is unbounded above, for
ANY `A` and for ANY EML tree `B` whatsoever, not just `eml var (const c)`. Proof, worked out on
paper first: for target `M`, either `exp(-(M+1)) < B(x1)` (apply IVT to `B(z)-exp(-(M+1))` on
`[x0,x1]`, getting an EXACT point where `B` equals `exp(-(M+1))`), or `B(x1) ≤ exp(-(M+1))`
already (in which case `x1` itself works directly via `log`'s monotonicity, no IVT needed at
all). Either way `exp(A)≥0` unconditionally can't cancel the resulting `-log(B) ≥ M+1`.

**Confirmed via a sanity-check corollary**: `eml_A_crossing_var_const_unbounded_above_via_general`
re-derives cont. 37's hand-built theorem exactly (`B := eml var (const c)`, `x0 := log(log c)`,
`x1 := x0+1`, reusing the pre-existing `hasDerivAt_evarConstC`) — the generalization captures the
same content, not merely a similar-looking one.

**What this settles for the induction, precisely.** Every EML tree ever built anywhere in this
40+-file arc with a genuine finite-point right-child crossing uses `eml var (const c)` as that
crossing — the ONLY crossing primitive this whole investigation has ever constructed. This
theorem now shows unboundedness holds for ANY genuine crossing whatsoever, differentiable and
sign-changing, regardless of shape or depth — meaning even a hypothetical future construction
using some entirely different crossing primitive would hit the same wall, PROVIDED it's
differentiable and genuinely changes sign at a finite point (the only real constraint left). This
is the tree-depth-induction spirit of the original Option D framing, done for real: a fact about
the `eml`-constructor's own structure (`exp≥0`, IVT for differentiable functions), not a
shape-by-shape enumeration that needs re-doing for every new tree shape someone thinks up.

**What's still, honestly, not covered by this**: a right child that ISN'T differentiable
everywhere on the relevant interval (this codebase's own `EMLTree.eval` is always differentiable
away from isolated non-generic points via the standard `HasDerivAt` composition machinery, so this
is unlikely to bite in practice, but wasn't formally ruled out); and the POSITIVE side of the
tree-depth induction (establishing `EMLPfaffianValidOn`-equivalent structure for trees whose right
children DON'T cross, beyond `RightChildrenEverywherePositive`'s current reach) remains untouched
— this round closes the unboundedness/negative half definitively, not the whole original question.

`sorryAx`-free, verified via a genuinely fresh rebuild: depends only on foundational
`MachLib.Real` axioms plus `hasDerivAt_continuousAt` (`IntermediateValue.lean`'s one analytic
bridge axiom) and `sup_exists` (the completeness axiom, already trusted throughout this codebase)
— no dependence on `EMLPfaffianValidOn` or `eml_pfaffian_validon_from_sin_equality`. Full `lake
build MachLib` passes (435 modules, up from 434). One commit this round (`ca5680ca`, plus this
docs commit), pushed.

## 2026-07-21 (cont. 39) — closing the direction-symmetry gap: the crossing-unboundedness result
now covers BOTH directions a right child can cross zero

**Direct user request: "proceed."** While considering the cont. 38 theorem's scope, noticed every
crossing subtree this whole arc has ever built (`eml var (const c)` and everything derived from
it) happens to INCREASE through zero (negative-then-positive, left to right) — the theorem's
hypotheses (`B(x0)=0, B(x1)>0` for `x0<x1`) only cover that one direction. The underlying
mechanism is obviously direction-agnostic (`exp(A)≥0` blocks cancellation regardless of which
side of the touch point `B` is small-and-positive on) but this was worth checking formally rather
than assuming — especially since `boundedNonConstantWitness` is PROVEN DECREASING
(`boundedNonConstantWitness_deriv_neg`), making a decreasing-through-zero right child (e.g.
`eml (boundedNonConstantWitness c) (const K)` for `K` large enough) a real, buildable candidate
worth ruling out explicitly rather than by analogy.

**`eml_A_crossing_B_unbounded_above_mirror`** (`WitnessResidualCrossingUnboundedMirror.lean`): `B`
positive at an EARLIER point `x0`, zero at a LATER point `x1` (decreasing-through-zero) — `eml A
B` is STILL unbounded above, for any `A`. Same IVT proof shape as the increasing case, just with
the auxiliary function's sign flipped (`h(z) := exp(-(M+1)) - B(z)` instead of `B(z) -
exp(-(M+1))`) so `intermediate_value_of_hasDerivAt`'s required negative-then-positive order (left
to right) is still satisfied — genuinely mechanical once the increasing case existed to mirror,
no new mathematical content.

**`eml_A_crossing_B_unbounded_above_either_direction`**: packages both directions into one
theorem (`B(p)=0 ∧ 0<B(q)` OR `0<B(p) ∧ B(q)=0`) for callers who just know a crossing exists
somewhere without knowing which side is which.

**What this closes, precisely.** A differentiable real function crossing zero transversally is
LOCALLY either increasing or decreasing through it — there is no third direction to check (this
is a basic fact about ℝ, not something specific to EML trees). Between cont. 38's theorem and
this round's mirror, the tree-depth induction's negative half is now closed EXHAUSTIVELY for
finite-point transversal crossings — not just for the one crossing direction this arc happened to
build, but for both directions any differentiable right child could possibly take.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as cont. 38 (only
foundational axioms plus `hasDerivAt_continuousAt` and `sup_exists`), no dependence on
`EMLPfaffianValidOn`. Full `lake build MachLib` passes (436 modules, up from 435). One commit this
round (`f5d40177`, plus this docs commit), pushed.

## 2026-07-21 (cont. 40) — MILESTONE: the "positive half" closed — `RightChildrenEverywherePositive`
is essentially NECESSARY, not just sufficient, for a bounded compound tree in this grammar

**Direct user request**: dig into the positive half, per its own framing at the end of cont. 39
— extending `EMLPfaffianValidOn`-equivalent structure to non-crossing trees beyond what
`RightChildrenEverywherePositive` already reaches. Worked through directly rather than assuming
an answer either way; the honest conclusion is a genuine surprise: there is essentially nothing
"beyond" it to find.

**The necessary-condition theorem** (`WitnessResidualSignNecessity.lean`,
`eml_A_B_bounded_above_sign_definite`): if `eml A B` is bounded above and `B` is differentiable
everywhere, `B` must be SIGN-DEFINITE throughout `ℝ` — strictly positive everywhere, or
non-positive everywhere. No third option. The proof is a direct application of the
crossing-unboundedness machinery, packaged as a genuine necessary condition rather than a family
of specific-shape refutations: `eml_A_B_unbounded_of_mixed_sign` shows that `B` taking BOTH a
non-positive value (at some `p`) and a positive value (at some `q`) forces unboundedness
regardless of which of `p, q` comes first — combining weakened versions of both directional
crossing theorems (`B(x0) ≤ 0`, not necessarily exactly `0`, turned out to suffice — a genuine
simplification over the exact-zero versions, discovered while building this).

**Why the "non-positive everywhere" disjunct isn't genuinely new territory.** If `B ≤ 0`
everywhere, `log(B)` clamps to `0` EVERYWHERE (`Real.log_nonpos`), so `eml A B` reduces IDENTICALLY
to `exp(A.eval ·)` (`eml_A_B_eq_exp_A_of_nonpos`, three lines) — the entire `B`-branch is dead
code, a disguised way to write a strictly simpler tree that drops `B` entirely. A tree built this
way contributes nothing a tree without the `B`-branch didn't already have; its own boundedness
becomes a question about `A` alone, recursively — not a new construction at all.

**The upshot, stated as plainly as the original question.** At EVERY `eml`-node in a bounded
compound tree, the right child must be either (a) globally positive (`RightChildrenEverywherePositive`'s
own condition, already built) or (b) globally non-positive (degenerate, reduces the node away).
There is nothing meaningfully "beyond `RightChildrenEverywherePositive`" within this grammar — not
because this arc hasn't found it yet, but because the crossing-unboundedness results, now
packaged this way, show there is nothing left of that kind to find. This closes the positive half
of the original Option D tree-depth induction question about as definitively as the negative half
was closed two rounds ago: not by exhausting shapes one at a time, but by characterizing the
constraint directly and showing it's tight.

**Honest scope, precisely — this is NOT the same as "the whole induction is closed."** This is a
ONE-LEVEL necessary condition (about a single `eml A B` node's own immediate right child). Turning
it into a full statement about an ENTIRE compound tree (recursively, at every node) needs a
structural induction applying this same dichotomy at every level — not carried out here. What
this round DOES establish is that the mathematical CONTENT such a recursion would need at each
step is now a genuine theorem, not an assumption or a per-shape argument. Also left untouched:
whether `EMLPfaffianValidOn`'s own INTERVAL-based (not global) formulation could admit trees
bounded only on a restricted range via crossings entirely outside it — not useful for the
residual's own purposes (which needs boundedness on all of `ℝ`, matching `sin`'s domain) but a
genuinely distinct question from what's closed here.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as the
crossing-unboundedness results it's built on (foundational axioms plus `hasDerivAt_continuousAt`
and `sup_exists`) — no dependence on `EMLPfaffianValidOn` or `eml_pfaffian_validon_from_sin_equality`
anywhere. Full `lake build MachLib` passes (437 modules, up from 436). One commit this round
(`46467b9a`, plus this docs commit), pushed.

## 2026-07-21 (cont. 41) — quantifying the sign-necessity dichotomy: `B` must be bounded AWAY
from zero, not merely positive — connecting the abstract result back to `boundedNonConstantWitness`

**Direct user request: "proceed."** Cont. 40's `eml_A_B_bounded_above_sign_definite` is a
QUALITATIVE dichotomy (`B` positive everywhere or non-positive everywhere). Checking what more
the SAME boundedness inequality forces — essentially for free, no new machinery — turns up a
genuinely useful QUANTITATIVE strengthening.

**`B_bounded_below_of_eml_bounded_above`** (`WitnessResidualQuantitativeBound.lean`): `eml A B`
bounded above by `M`, `B` positive everywhere ⟹ `B` is bounded AWAY from `0`, uniformly, by
`exp(-M)`. Direct algebra: from `exp(A.eval x) - log(B.eval x) ≤ M` and `exp(A.eval x) ≥ 0`
unconditionally, `-M ≤ log(B.eval x)` falls out immediately; apply `exp` monotone to get
`exp(-M) ≤ B.eval x`. `A_bounded_above_of_eml_bounded_above_nonpos` handles the dual degenerate
case (transfers the bound directly to `exp(A.eval ·)` via the reduction identity).
`eml_A_B_bounded_above_characterization` packages both into the full quantitative picture.

**Why this is worth recording, not just a routine corollary.** This is EXACTLY the shape
`boundedNonConstantWitness`'s own right-child machinery has used since the very start of this
whole arc (`boundedNonConstantWitness_Bpos` establishes `0 < exp(exp z) - log c` UNCONDITIONALLY,
and every downstream construction — `E_BNCW`, `growthCompetitionWitness`,
`growthCompetitionWitnessDeep` — relies on right children whose INFIMUM is a strictly positive
constant, not merely "eventually positive somewhere"). This file shows that reliance was never
incidental engineering discovered by trial per construction — it's the precise QUANTITATIVE form
the sign-necessity dichotomy FORCES on any bounded compound tree, derivable directly from the
same inequality that gave the qualitative half. A satisfying, retroactive explanation for a
pattern this arc has been using successfully for many rounds without a general account of why it
had to look that way.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as cont. 40
(foundational axioms plus `hasDerivAt_continuousAt` and `sup_exists`) — no dependence on
`EMLPfaffianValidOn`. Full `lake build MachLib` passes (438 modules, up from 437). One commit
this round (`10d4b9ac`, plus this docs commit), pushed.

## 2026-07-21 (cont. 42) — MILESTONE: the recursive lift, done — the one-level fact now a genuine
theorem about an ENTIRE compound tree's structure

**Direct user request**: focus specifically on lifting the one-level fact to a full recursive
statement, per the honest gap flagged at the end of cont. 40/41. Two real obstacles surfaced
while attempting the natural first approach — worked through directly rather than assumed away
or hand-waved past.

**Obstacle 1 — naive top-down propagation doesn't work.** The first instinct ("`T` bounded ⟹ its
immediate right child sign-definite; recurse into `T`'s children using the SAME bound") fails,
and `boundedNonConstantWitness` itself is the counterexample: `T := eml var B` is bounded overall
via a delicate CANCELLATION between `exp(x)` and `log(B(x))` as `x→±∞` — but the bare `var` playing
`T`'s own left child is individually UNBOUNDED, and `B` need not be bounded ABOVE either (only
bounded away from `0`, per cont. 41). Boundedness of a compound tree does not require boundedness
of its parts — cancellation between diverging pieces is a real, load-bearing phenomenon in this
grammar, not a corner case. The recursive theorem therefore takes an EXPLICIT per-node hypothesis
(`SupportsSignAnalysis`), not a single top-level bound propagated automatically — matching how
`EMLPfaffianValidOn` and `RightChildrenEverywherePositive` were ALREADY structured this whole arc,
for reasons that are now explicit rather than just "that's the established pattern."

**Obstacle 2 — found by testing against `boundedNonConstantWitness` directly, not left
theoretical.** The natural per-node hypothesis ("every `eml`-node's own eval bounded above") is
TOO STRONG: `boundedNonConstantWitness`'s own inner node `eml var (const 1)` (`= exp(x)`,
literally unbounded above) fails it — even though its right child (`const 1`) is trivially
sign-definite, needing no boundedness argument at all (a literal constant's sign is decidable
directly via `lt_total`). `SupportsSignAnalysis` (`WitnessResidualRecursiveSignLift.lean`)
special-cases literal-`const` right children, skipping the boundedness requirement exactly where
it isn't actually needed — the fix that makes the hypothesis satisfiable by real constructions.

**`AllRightChildrenSignDefinite`**: the recursive conclusion, mirroring
`RightChildrenEverywherePositive`'s own shape exactly, weaker (either sign, not just positive).
**`supportsSignAnalysis_sign_definite_and_diff`**: proven by structural induction, concluding
BOTH sign-definiteness throughout AND differentiability everywhere TOGETHER — the differentiability
half is what lets the induction invoke the one-level theorem again at the next level up.
`eml_node_sign_and_diff` factors the shared "differentiable right child + this node's bound ⟹
sign + this node's own differentiability" step, reused for both remaining cases (`var` and
compound right children).

**Confirmed against the real construction, not left as an abstract exercise.**
`boundedNonConstantWitness_supportsSignAnalysis` verifies `boundedNonConstantWitness` — the safe
building block this entire arc has relied on since its very first appearance — genuinely
satisfies `SupportsSignAnalysis` (top-level bound from the already-established
`boundedNonConstantWitness_upper_bound`; every inner node's own requirement vanishes via the
`const`-right-child special case, exactly matching the obstacle-2 fix).
`boundedNonConstantWitness_allRightChildrenSignDefinite` then applies the main theorem, concluding
full sign-definiteness throughout — proven via the GENERAL machinery built this round, not by
re-deriving positivity by hand the way every earlier file in this arc did for this exact tree.

**What this closes.** The "one-level vs. whole-tree" gap explicitly flagged at the end of cont.
40 is closed: the mathematical content a recursive argument needs at every step is now not just
available but ASSEMBLED into one clean theorem, verified against the arc's own central
construction. Combined with cont. 38–41, the tree-depth induction's original core question —
negative half (crossings force unboundedness) and positive half (sign-definiteness is necessary,
now at every level of an entire tree, not just one node) — is closed about as completely as this
grammar allows.

`sorryAx`-free, verified via a genuinely fresh rebuild: same axiom footprint as cont. 38–41
(foundational axioms plus `hasDerivAt_continuousAt` and `sup_exists`) — no dependence on
`EMLPfaffianValidOn` or `eml_pfaffian_validon_from_sin_equality` anywhere. Full `lake build
MachLib` passes (439 modules, up from 438). One commit this round (`52e4799e`, plus this docs
commit), pushed.

## 2026-07-21 (cont. 43) — attempting the actual residual closure, per direct request: two new
techniques found, residual NOT closed, honest account of exactly where it stops

**Direct user request**: try to actually close the residual using everything built in this arc —
deriving `SupportsSignAnalysis` (or an equivalent) from the equation `T1.eval = target` itself,
rather than assuming it, per the gap named at the end of cont. 42. This is genuinely the "weeks
to a month" undertaking from the original June 12 decision doc. This round does not close it —
but finds two real, verified, independently reusable techniques and sharpens exactly where the
remaining wall is, from a new angle.

**Checked a real fact before relying on it**: does `Real.log`'s clamp make it CONTINUOUS at its
boundary (a claim this doc's own cont. 30 entry asserted)? Read `Log.lean`'s actual definition
directly rather than trusting the earlier characterization — it does NOT. `log` returns exactly
`0` for `x ≤ 0` while the true logarithm diverges to `-∞` as `x → 0⁺` (a deliberate design choice,
matching this file's own comment: "GNU libc gives `-∞`, we deliberately use `0`"). This is a
genuine DISCONTINUITY, not just non-differentiability — confirming an arbitrary, unknown EML
tree has NO free continuity/differentiability guarantee, and that guarantee genuinely depends on
whether its own right children avoid the clamp boundary — exactly the fact under investigation.
The earlier "continuous at 0" claim was wrong; worth having caught before building on it.

**Technique 1 — differentiability transports for free from the target's own closed form**
(`WitnessResidualClosureAttempt.lean`, `T1_hasDerivAt_of_eq_nestedTarget`). The fix needs no
structural argument on `T1` at all: `nestedTarget cs` is a SPECIFIC, KNOWN function, provably
differentiable everywhere given `nestedWF cs` (`nestedTarget_hasDerivAt`, straightforward
induction on `cs` composing `HasDerivAt_sin`/`HasDerivAt_log_pos`). Since the residual's own
hypothesis gives `T1.eval = nestedTarget cs` GLOBALLY, `HasDerivAt_of_eq` transports that
differentiability directly onto `T1` — sidestepping "does an arbitrary tree's structure guarantee
differentiability" for `T1` ITSELF, with zero assumption on `T1`'s own shape.

**Technique 2 — pure algebra pins down `B` pointwise, no IVT needed at all**
(`B_eval_forced_pos_of_ne`). For `T1 = eml A B`, `T1.eval x0 = target x0` directly gives
`log(B.eval x0) = exp(A.eval x0) - target x0`. `log`'s clamp returns EXACTLY `0` for non-positive
arguments — so if this computed quantity is NONZERO, `B.eval x0` is FORCED strictly positive
(in fact forced to equal `exp(exp(A.eval x0) - target x0)` EXACTLY) — no IVT, no continuity, no
differentiability argument anywhere. Confirmed by the axiom check: depends on nothing beyond the
most basic ordered-field facts, not even `exp_pos`. Contrapositive
(`exp_A_eq_target_of_B_nonpos`): the ONLY way `B` can ever be non-positive is at a point where
`A`'s exp-image hits the target exactly.

**Where this leaves the residual, precisely — not overstated.** These two facts together pin
down `B` almost everywhere: positive unconditionally EXCEPT possibly at points where
`exp(A(x)) = target(x)` exactly (the "ambiguous set"). If that set is empty, `B` is positive
EVERYWHERE for free, closing the case immediately via the existing `RightChildrenEverywherePositive`
machinery. But the set's emptiness is NOT free — it depends on `A`'s own behavior, which is
EXACTLY what the induction is trying to establish in the first place, and it does NOT transport
the same way `T1`'s differentiability did: `A`, unlike `T1`, has no known closed form independent
of the tree's own unknown structure (that's what makes `A` the unknown, not the target). This is
the SAME underlying difficulty this whole arc identified from its earliest rounds ("grounded WHY
path 1 is hard" — general compound trees mixing clamped/unclamped regions needs machinery not yet
built) — now sharpened and CONFIRMED from a genuinely different angle (pointwise algebra and
differentiability-transport, not the Pfaffian-chain encoding originally used to state it), rather
than resolved. Both techniques remain independently reusable for whoever continues: transport
works for ANY equation `T1.eval = (known closed-form target)`, not just this family; the pointwise
determination works for ANY compound tree at all, not just nested-target-family instances.

`sorryAx`-free, verified via a genuinely fresh rebuild. Full `lake build MachLib` passes (440
modules, up from 439). One commit this round (`d7d07845`, plus this docs commit), pushed.

## 2026-07-21 (cont. 44) — the residual, actually closed for a real (scoped) special case: the
non-positive left-spine

**Direct user request**: "procced further please" — a bare continuation of cont. 43's residual-
closure attempt. Rather than continue circling the "ambiguous set" wall directly, this round asks
a narrower question: is there a clean special case of the residual that closes completely, using
what's already built? Yes — and it turns out to be the FIRST case in this whole arc where the raw
question ("does some tree equal a member of the nested-target family") closes with ZERO
hypothesis beyond the tree's own shape — no `EMLPfaffianValidOn`, no assumed sign-definiteness,
nothing borrowed from outside this file.

**The case**: `B ≤ 0` everywhere, at EVERY `eml` node down the tree's own left spine
(`BChainNonpos`, `WitnessResidualNonposChainClosure.lean`). When `B ≤ 0` everywhere at a node,
`eml_A_B_eq_exp_A_of_nonpos` (already sitting in `WitnessResidualSignNecessity.lean` since
cont. 40) reduces that node's eval to `exp(A.eval x)` exactly — there is no "ambiguous set" left
to worry about, because the reduction doesn't go through the pointwise-algebra case split at all;
it's unconditional given the hypothesis. From there the only question is whether
`exp(A.eval x) = nestedTarget cs x` for all `x` is possible, and THAT splits cleanly on
`nestedLo cs`: if `≤ 0`, evaluating at `x = -π/2` (`nestedTarget`'s own attained minimum — a fact
that turned out to already exist in the codebase, `nestedTarget_at_neg_pi_div_two`, built back
during the `WitnessResidualNestedTargetBWitness.lean` round and re-discovered by grep this round)
forces `exp(A(-π/2)) ≤ 0`, immediate contradiction against `exp > 0`. If `nestedLo cs > 0`, `log`
undoes the `exp` (`log_exp`), giving `A.eval x = nestedTarget (0 :: cs) x` for ALL `x` — i.e. `A`
itself matches ONE LEVEL DEEPER into the very same family. Since `A` is a genuine, structurally
smaller subterm of the original tree, this is real recursion, not just a restated hypothesis:
`no_tree_eq_nested_target_of_BChainNonpos` inducts on the tree directly, terminating at `const`/
`var` base cases (two small new lemmas needed: a constant tree can't match because the family
takes two provably different values — at `kπ` vs. `π+1`, both already established by
`nestedTarget_facts`; `var` can't match because the family is bounded by `nestedHi cs` but `id`
is not).

**Why this is a genuine closure, not another partial result.** Every earlier "closure" in this
arc (starting from the original `no_tree_eq_target_given_validon`) needed `EMLPfaffianValidOn` or
an equivalent as an explicit, undischarged hypothesis — the whole point of Option D was finding
ways to discharge that hypothesis FROM a tree's own structure instead of assuming it. This is the
first result in the whole arc where that hypothesis is gone entirely, replaced by a purely
structural condition on the tree (`BChainNonpos`) that can be checked by inspection, no analysis
needed. It is real, but it is also SCOPED: it's the "opposite extreme" from
`RightChildrenEverywherePositive` (every right child positive, cont. 30-33) — together the two
results now cover both ends of the sign spectrum for right children. What's still open is exactly
the same "mixed" case flagged at the end of cont. 43: some right child that is positive somewhere
and non-positive elsewhere.

**An unexplored lead, flagged honestly as unexplored, not claimed.** A right child that takes
both signs is, by definition, a CROSSING in the sense already built and proven in
`WitnessResidualCrossingUnboundedGeneral.lean` (cont. 38) — and `nestedTarget cs` is BOUNDED
(`nestedTarget_facts`'s own range fact). If the crossing machinery's differentiability hypothesis
on `B` could be established for an arbitrary compound `B` (the same kind of question Technique 1
answered for `T1` itself via transport, but here needed for `B` specifically, which does NOT have
a known closed form the way `nestedTarget cs` does), the mixed case would force `T1` unbounded,
directly contradicting `nestedTarget`'s own boundedness — potentially closing the WHOLE residual,
not just another special case. This is written down as a lead because it connects two previously
disjoint sub-arcs of this session (crossing-unboundedness from cont. 37-39, and sign-necessity/
pointwise-algebra from cont. 40-43) that hadn't been checked against each other before. It has
been checked for internal consistency only as far as this paragraph goes — not attempted in Lean,
not even sketched on paper beyond the one-paragraph argument above. Whoever continues this should
treat it as a real next step, not a result.

`sorryAx`-free, verified via a genuinely fresh rebuild — confirmed to depend on nothing beyond
this codebase's base ordered-field/trig/exp axioms, no `EMLPfaffianValidOn`, no differentiability
axioms at all (this particular case needed none of the transport machinery from cont. 43, since
the non-positive reduction sidesteps the ambiguity that machinery was built to handle). Full
`lake build MachLib` passes (441 modules, up from 440). One commit this round (`8bf378f1`, plus
this docs commit), pushed.

## 2026-07-21 (cont. 45) — realizing the crossing/boundedness bridge flagged last round: two more
concrete shapes closed unconditionally

**Direct user request**: "proceed" — continuing straight off cont. 44's own flagged lead (the
crossing/boundedness connection, written down as "unexplored, not merely unproven"). Rather than
stop at flagging it, this round actually builds it, and finds it is both real and stronger than
the cautious framing suggested.

**The bridge, in two lines** (`no_eml_A_B_eq_nested_target_of_unbounded_above`,
`WitnessResidualCrossingBoundednessBridge.lean`): any right child `B` that provably forces
`eml A B` unbounded above — by ANY means — immediately rules out matching ANY member of the
nested-target family, since the family is bounded above by `nestedHi cs`
(`nestedTarget_facts`'s own range fact). Extract the unboundedness witness at `M := nestedHi cs`,
substitute the equality hypothesis, contradict the range fact directly. This is the first place
in the whole arc where the crossing-unboundedness sub-arc (cont. 37-39) and the nested-target
boundedness sub-arc (`WitnessResidualNestedTargetFamily.lean`) connect to each other at all.

**Where the earlier framing undersold it.** cont. 44's docstring assumed closing the mixed-sign
gap would need `B`'s differentiability established for an ARBITRARY, unknown compound tree — the
same "no known closed form to transport from" wall `WitnessResidualClosureAttempt.lean` hit. That
wall only applies to a truly UNKNOWN `B`. For CONCRETE, SPECIFIC crossing shapes, differentiability
is already proven in this codebase, unconditionally, no transport needed at all — the bridge just
had to be pointed at facts that already existed:
- **`B = var`** (`no_eml_A_var_eq_nested_target`): `var` genuinely crosses zero
  (`var.eval 0 = 0`, `var.eval 1 = 1 > 0`) and is unconditionally differentiable (`HasDerivAt_id`
  — `var`'s closed form literally IS `id`, known outright, not borrowed from anywhere). Closes
  `eml A var` against the WHOLE family, for ANY `A`, regardless of `nestedLo cs`'s sign — no case
  split on `cs` needed at all. Strictly stronger than a pointwise `nestedLo cs ≤ 0`-only variant
  built earlier in the same round and kept in the file for its different coverage (see below).
- **`B = eml var (const c)`, `c > 1`** (`no_eml_A_evarConstC_eq_nested_target`): the ORIGINAL
  crossing primitive this entire 40+-file arc was built around
  (`WitnessResidualCrossingUnbounded.lean`, cont. 37 — the very first crossing example this
  session ever constructed), reusing the already-proven
  `eml_A_crossing_var_const_unbounded_above_via_general` (built cont. 38) directly. Closes
  unconditionally, ANY `A`, ANY `c > 1`.

**A complementary, non-overlapping pointwise result**
(`no_eml_eq_nested_target_of_B_neg_pi_div_two_nonpos`): re-examining `BChainNonpos`'s own
immediate-contradiction branch (cont. 44) shows it never actually needed `B ≤ 0` EVERYWHERE —
only at the single point `-π/2`. Generalizes to ANY `A`, ANY `B` (no crossing, no
differentiability, nothing) whenever `nestedLo cs ≤ 0`. This covers a DIFFERENT axis than the
bridge: shapes that dip non-positive at exactly that one point WITHOUT crossing zero anywhere
else (so the crossing machinery wouldn't apply to them), at the cost of needing `nestedLo cs ≤ 0`
(the bridge needs nothing about `cs` at all).

**What is still open, stated plainly — this is not the full residual.** A fully GENERAL compound
`B` — arbitrary structure, no promise of a known crossing shape, no known closed form — remains
exactly as open as `WitnessResidualClosureAttempt.lean` left it at the end of cont. 43. This round
closes two concrete, NAMED shapes plus one pointwise-general-but-crossing-agnostic case, by reusing
existing machinery — not the fully general induction the residual ultimately needs, and not a
claim that the "mixed-sign case" as a whole is closed. The lasting value is the bridge lemma
itself: reusable for ANY future crossing shape this codebase proves unbounded, without redoing the
boundedness-contradiction argument from scratch each time — a genuine piece of general
infrastructure, not just two more special cases.

`sorryAx`-free, verified via a genuinely fresh rebuild for every theorem in the file. No
`EMLPfaffianValidOn`, no `eml_pfaffian_validon_from_sin_equality` dependence anywhere. Full
`lake build MachLib` passes (442 modules, up from 441). One commit this round (`48a691f5`, plus
this docs commit), pushed.

## 2026-07-21 (cont. 46) — the crossing bridge generalized beyond hand-verified shapes, via
pre-existing `EMLNoCrossingAt` infrastructure

**Direct user request**: "proceed" — continuing directly off cont. 45's own two concrete closures
(`var`, `eml var (const c)`). Before writing more hand-verified special cases, this round asked
whether the pattern generalizes: both closures needed `B`'s differentiability, hand-proven once
each. Is there a general tool for that instead of proving it per-shape forever?

**Yes — and it already existed in the codebase, unused by this arc until now.**
`EMLSmoothness.lean` is a large (2985-line), SEPARATE, EARLIER sub-arc toward closing
`eml_pfaffian_validon_from_sin_equality` directly — predating the `WitnessResidual*` naming
convention entirely, and already wired into a DOZEN `WitnessResidual*` files (including
`WitnessResidualRightChildrenEverywherePositive.lean`, meaning the very first two witnesses closed
at the START of this whole arc already rest on this file, unknowingly to this particular
sub-thread until this round). It proves `EMLNoCrossingAt` — a purely LOCAL, non-circular,
structurally-checkable predicate ("no internal log-argument lands exactly on `0` at this point",
strictly weaker than `EMLPfaffianValidOn`) — and `eml_hasDerivAt_of_no_crossing`: ANY `EMLTree` is
differentiable at `x`, given `EMLNoCrossingAt` there, by plain structural induction, no
circularity, no reference to siblings or ancestors.

**Before building on it, checked for accidental duplication.** `WitnessResidualBChainCompound.lean`'s
name looked suspiciously close to cont. 44's `BChainNonpos`. Read it directly: unrelated — a
"chain of `≤1`-bounded positive constants" mechanism (`GoodPositiveChain`), a naming coincidence
with no actual overlap. Worth the two minutes to check before assuming novelty.

**The generalized bridge**
(`no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing`,
`WitnessResidualCrossingBoundednessBridge.lean`, added to the same file as cont. 45's results):
feed `eml_hasDerivAt_of_no_crossing` directly into `eml_A_crossing_B_unbounded_above`'s
differentiability hypothesis. Closes the residual for ANY `B` — not just `var` or
`eml var (const c)` — that genuinely crosses zero on some `[x0, x1]` AND satisfies
`EMLNoCrossingAt` throughout that interval. `var`/`eml var (const c)` are now understood as the
two cases where that side condition happened to be free (known outright); this makes the SAME
argument available for any future candidate `B` a checkable structural condition away, instead of
requiring a from-scratch differentiability proof each time.

**What is still open, stated plainly — genuinely unchanged from cont. 45's own accounting.** A
truly UNKNOWN compound `B` — no promise of a genuine crossing, no promise of `EMLNoCrossingAt` on
the relevant interval — remains exactly as open as `WitnessResidualClosureAttempt.lean` left it at
the end of cont. 43. `EMLNoCrossingAt` is a real hypothesis, not free for an arbitrary tree — this
broadens the class of closeable shapes from "two named ones" to "any shape satisfying two
checkable conditions," which is real progress on reusability, but does not touch the fully general
induction. Worth flagging for whoever continues: `EMLSmoothness.lean` also contains
`eml_pfaffian_validon_of_sin_and_witness_at_point`, described in its own docstring as "the closest
form to `eml_pfaffian_validon_from_sin_equality` itself... exactly the witness-finding question...
and nothing else" — i.e. a DIFFERENT, EARLIER reduction of the SAME overall axiom to
`EMLNoCrossingAt` (throughout `(0,∞)`) plus `EMLWitnesses t p` (one point). This is a positive-
direction reduction (assume the tree exists with these properties, derive full validity),
complementary to this whole `WitnessResidual*` sub-arc's negative-direction strategy (show no tree
with certain properties CAN equal the target at all). The two strategies have not yet been
explicitly reconciled or compared for relative strength — a real next step, not yet attempted.

`sorryAx`-free, verified via a genuinely fresh rebuild for all six theorems in the file. No
`EMLPfaffianValidOn`, no `eml_pfaffian_validon_from_sin_equality` dependence anywhere. Full
`lake build MachLib` passes (442 modules — this round extended an existing file rather than adding
a new one). One commit this round (`45c734c7`, plus this docs commit), pushed.

## 2026-07-21 (cont. 47) — a major clarification, no new Lean: "attempt the full Khovanskii
generalization" turns out to already be done, and this whole `WitnessResidual*` sub-arc IS its
continuation

**User request**: given cont. 46's discovery of the separate, earlier `EMLSmoothness.lean`
sub-arc, asked to investigate whether the "Khovanskii/Wronskian rigidity machinery" lead (flagged
as unexplored back in round 5 of that sub-arc, memory file `machlib-khovanskii-axiom-frontier.md`)
was worth attempting, before committing effort either way. Spent this round reading, not writing:
the full 30-round history in that memory file (a DIFFERENT project's memory directory,
`-home-monogate-monogate-wawire`, found via a cross-project search — worth remembering this
decision doc's own prequel lives partly outside this project's own memory), then this document's
own opening (lines 1–463, never read this session before now), specifically the very first entry
(2026-07-19, before what this document's numbering calls "cont. 1") titled "Option D, strong
induction on tree depth with the target generalized."

**What that entry actually proposed**, precisely: don't reuse `sin_not_in_eml_any_depth` as a black
box (checked: doing so would be circular — its own proof needs
`eml_pfaffian_validon_from_sin_equality` as an input). Instead, re-derive its WHOLE mechanism —
the constructive Khovanskii zero-count bound (`combinedBoundE`/`enc_combinedBound`,
`EMLExplicitBoundEncoder.lean`) plus a concrete "target's own oscillation exceeds the bound"
contradiction — generalized to an ARBITRARY target function, not hardcoded to `sin`. The next
entry (still before "cont. 1") worked out the exact missing piece ("step (c)") ON PAPER: the
**target-shift trick** — instead of counting zeros of `T1.eval`, count solutions to
`T1.eval x = L` for a shifted level `L` (here `L = log(c2)`), via
`p' := MultiPoly.sub (enc T1 chain).2 (MultiPoly.const L)` fed into `enc_combinedBound` — checked
against the real `MultiPoly`/`enc_combinedBound` type signatures, not assumed. That entry left it
explicitly UNIMPLEMENTED, flagged as "genuinely multi-round work... possibly larger" than the
5-round mechanism-building push that had just finished.

**It was NOT left unimplemented for long — a later, still-pre-"cont. 1" round in this SAME
document actually built it.** `WitnessResidualTargetGeneric.lean`'s `no_tree_eq_target_given_validon`
IS the target-shift trick, fully generalized over `(TARGET, L)` rather than hardcoded to
`(sin, 0)` or `(log(c2+sin·), log c2)` specifically — read its body directly to confirm, not
assumed from the name: `p := (enc T1 emlEmptyChain).2`, `p' := MultiPoly.sub p (MultiPoly.const L)`,
`M := combinedBoundE (len T1 0) (enc T1 emlEmptyChain).1 (encTags T1 emlEmptyChain ()) p'` —
literally the exact construction sketched on paper, generalized one step further (arbitrary `L`,
not just `log c2`) and already wired into the WHOLE `nestedTarget` family this session's cont. 34–46
has been extending (`no_tree_eq_nested_target_given_validon`,
`WitnessResidualNestedTargetFamily.lean`, built on top of it). **This is genuinely the full
Khovanskii generalization from the 2026-07-19 brainstorm — already built, already the load-bearing
foundation under every result cont. 34–46 produced this session, not a separate undertaking
waiting to be started.**

**What this means for "attempt the Khovanskii route," concretely.** The Khovanskii/zero-counting
side of Option D is MAXED OUT — `no_tree_eq_target_given_validon`/`no_tree_eq_nested_target_given_validon`
already close "does any tree equal this target" for the WHOLE nested-target family, for literally
any target expressible this way, GIVEN `EMLPfaffianValidOn T1` (equivalently, `hvalidon_any_b`).
There is no further Khovanskii-flavored generalization left to build on that side — the machinery
already covers arbitrary targets in this family, not just `sin`/`log(c2+sin·)`. **The entire
remaining gap — discharging `hvalidon_any_b` for an arbitrary, structurally unknown `T1` — is NOT
a zero-counting question at all.** It's a positivity/no-crossing question (does `T1`'s own
structure keep every internal log-argument positive), which is exactly what
`RightChildrenEverywherePositive` (cont. 29, closing the arc's first two witnesses),
`BChainNonpos` (cont. 44), and the crossing/boundedness bridge (cont. 45–46) have all been
attacking directly. **This whole `WitnessResidual*` sub-arc — cont. 1 through cont. 46 — IS the
continuation of the Khovanskii-generalization plan, specifically its `hvalidon_any_b`-discharge
half; it was never a parallel or lesser-scoped alternative to it.**

**Why this is worth a full round of investigation rather than a two-line note.** Going in, both the
user and I were treating "attempt the Khovanskii route" and "keep extending the structural
`hvalidon_any_b` work" as genuinely different bets with different risk profiles — one big and
unstarted, one incremental and safe. That framing was wrong: there is no unstarted big bet here.
The honest recommendation, now that this is actually verified against the source rather than
inferred from a label, is to keep doing exactly what cont. 34–46 have been doing — closing more
structural classes that discharge `hvalidon_any_b` — with the clarification that this is now
understood to be the SOLE remaining piece of the entire multi-week program, not one option among
several.

No Lean written or modified this round — pure investigation, per the user's own "investigate
first" framing, now resolved with a concrete, source-verified answer rather than left open.

## 2026-07-21 (cont. 48) — the first theorem to connect both halves of the arc against each other:
`BChainNonpos` and `RightChildrenEverywherePositive`, unified

**Direct user request**: "proceed" — continuing cont. 47's clarification into concrete work. Since
cont. 47 established that the Khovanskii/zero-counting side
(`no_tree_eq_nested_target_given_validon`) and the structural/positivity side
(`RightChildrenEverywherePositive`, `BChainNonpos`, the crossing bridge) were never separate
projects, the natural next move is to check whether they connect to EACH OTHER directly, not just
share a common ancestor theorem.

**The gap.** `BChainNonpos` (cont. 44) requires `B ≤ 0` everywhere at EVERY `eml` node down a
tree's left spine, terminating only at a `const`/`var` leaf. A tree whose spine goes non-positive
for several levels and THEN hits a node where the remaining subtree happens to be fully
`RightChildrenEverywherePositive` was covered by NEITHER theorem: too much non-positive structure
for `RightChildrenEverywherePositive` (which tolerates none), not non-positive all the way to a
leaf for `BChainNonpos`.

**`BChainOrPositive`** (`WitnessResidualChainOrPositive.lean`): at each `eml A B` node, the chain
now has TWO ways to close instead of one — EITHER the whole remaining subtree satisfies
`RightChildrenEverywherePositive` (closed immediately by feeding
`EMLPfaffianValidOn_of_right_children_everywhere_positive` into
`no_tree_eq_nested_target_given_validon` — genuinely invoking the Khovanskii zero-counting bound
for the first time from within this recent lineage), OR `B` is non-positive everywhere and the
chain continues into `A` exactly as `BChainNonpos` already does. The resulting theorem
STRICTLY generalizes both priors as special cases (always the right disjunct = `BChainNonpos`;
left disjunct at the very top = `RightChildrenEverywherePositive`'s own closure) — the first time
in this whole recent lineage (cont. 44-47) that the two named mechanisms have been combined into
one proof rather than sitting as disjoint special cases.

**Confirms cont. 47's finding concretely, not just in principle.** `#print axioms` on the new
theorem shows it pulling in `IsAnalyticOnReals`/`analytic_*`/`rolle_ct` — the arc's standard
Khovanskii trusted base — for the FIRST TIME in the `WitnessResidualNonposChainClosure`/
`CrossingBoundednessBridge` lineage; every theorem built cont. 44-46 was purely elementary,
touching neither `enc_combinedBound` nor any analytic axiom. This is a small, concrete
demonstration that "the structural route" and "the Khovanskii route" were never actually two
different projects — this theorem needed BOTH halves at once, cleanly, on the first attempt.

**Scope, stated plainly — not oversold.** Still not the fully general residual: a tree that
alternates non-positive/positive/non-positive down its spine remains uncovered, since the positive
branch (`RightChildrenEverywherePositive`) has no escape hatch of its own back into a non-positive
continuation — it's an all-or-nothing condition on the WHOLE remaining subtree. Closing the truly
alternating case would need `RightChildrenEverywherePositive` itself generalized the same way
`BChainNonpos` just was, which is a natural, symmetric next step but not attempted this round.

`sorryAx`-free, verified via a genuinely fresh rebuild. Compiled clean on the first attempt (no
errors, no fixes needed). No `eml_pfaffian_validon_from_sin_equality` dependence. Full
`lake build MachLib` passes (443 modules, up from 442). One commit this round (`acca725e`, plus
this docs commit), pushed.

## 2026-07-21 (cont. 49) — the third mechanism folded in: `BChainTriple` unifies
`RightChildrenEverywherePositive`, the crossing bridge, and `BChainNonpos` in one theorem

**Direct user request**: "proceed" — continuing cont. 48's own named gap directly. That entry
flagged: the positive escape hatch (`RightChildrenEverywherePositive`) is all-or-nothing over the
WHOLE remaining subtree, so a node whose failure to qualify is caused SPECIFICALLY by its own
immediate right child genuinely crossing zero had no direct closure — `BChainOrPositive` could
only escape via full positivity or continue via full non-positivity, nothing in between.

**No new mechanism needed — the crossing bridge (cont. 45-46) already closes exactly this,
more directly than either of the other two escapes.**
`no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing` derives `False` straight from
`(eml A B).eval = nestedTarget cs` whenever `B` genuinely crosses zero on some `[x0,x1]` with
`EMLNoCrossingAt` holding throughout — no recursion into `A` at all, unlike the positive escape
(needs the Khovanskii bound on the WHOLE subtree) or the non-positive branch (needs to recurse one
level deeper with a shifted target). Adding it as a third disjunct in the chain definition was
purely mechanical: wire an existing, already-verified closure into the induction's crossing
branch — no new proof technique invented this round.

**`BChainTriple`** (`WitnessResidualTripleChain.lean`): at each `eml A B` node, three ways to
close — `RightChildrenEverywherePositive` (Khovanskii escape), `B` crosses zero with
`EMLNoCrossingAt` on the interval (crossing-bridge escape, immediate), or `B` non-positive
everywhere (continue the chain, `BChainNonpos`'s reduction unchanged). `BChainOrPositive` is
exactly the sub-case where the crossing disjunct is never taken; `BChainNonpos` is exactly the
sub-case where neither of the first two ever is. Compiled clean on the first attempt, same as
cont. 48's unification — a second data point that these three pieces were built compatibly with
each other from the start, not by luck once.

**Scope, stated plainly — still not the fully general residual, and this round doesn't claim
otherwise.** All three mechanisms are now combined into one theorem, but none of them individually
grew any more powerful this round — the crossing disjunct needs an EXPLICIT, controllable zero
crossing (`B.eval x0 = 0` exactly, `B.eval x1 > 0`) plus verifiable `EMLNoCrossingAt` on that exact
interval. A `B` that's non-positive somewhere and positive elsewhere WITHOUT a clean, controllable
crossing point — e.g. touching `0` only in a limit, or with `EMLNoCrossingAt` failing to hold on
any usable interval — remains covered by NONE of the three mechanisms. The remaining gap is
unchanged in kind from where `WitnessResidualClosureAttempt.lean` (cont. 43) left it: a truly
unconstrained, structurally unknown `B`. This round's contribution is combining what already
existed into strictly broader coverage per theorem, not discovering new closeable territory.

`sorryAx`-free, verified via a genuinely fresh rebuild. No `eml_pfaffian_validon_from_sin_equality`
dependence. Full `lake build MachLib` passes (444 modules, up from 443). One commit this round
(`c2ee4889`, plus this docs commit), pushed.

## 2026-07-21 (cont. 50) — the crossing disjunct broadened: exact-zero requirement replaced with
sign-change, no new mechanism needed again

**Direct user request**: "proceed" — continuing directly off cont. 49's own scope note, which
flagged the crossing disjunct's exact-crossing requirement (`B.eval x0 = 0` precisely) as awkward
to satisfy for most concrete trees, which more naturally give a sign CHANGE
(`B.eval x0 ≤ 0`, `B.eval x1 > 0`) without the caller already knowing exactly where the root sits.

**The fix, mechanical once seen.** `EMLNoCrossingAt` already gives `B` continuous on `[x0,x1]`
(`eml_continuousAt_of_no_crossing`, `EMLSmoothness.lean`), and `intermediate_value`
(`IntermediateValue.lean`, already-proven, no new axioms) finds an EXACT root given a genuine sign
change and continuity — so `no_eml_A_B_eq_nested_target_of_sign_change_and_no_crossing` just
applies IVT itself when `B.eval x0 < 0` strictly (recovering the exact-crossing case directly when
`B.eval x0 = 0` already), rather than requiring the caller to supply the root. Wired directly into
`BChainTriple`'s OWN definition (`B.eval x0 ≤ 0` replacing `B.eval x0 = 0`) rather than left as a
separate add-on — every existing exact-crossing instance still qualifies (`≤0` is implied by `=0`
trivially), with strictly broader applicability besides. Compiled clean on the first attempt, the
THIRD theorem in a row in this lineage to do so (cont. 48, cont. 49, and now this) — a consistent
pattern, not a coincidence: this arc's existing pieces (`eml_continuousAt_of_no_crossing`,
`intermediate_value`, the crossing bridge itself) were each built general enough to compose
directly, without needing rework at the seams.

**Scope, stated plainly — same honest boundary as the last two rounds, restated because it's
still true, not because anything changed.** The crossing disjunct still needs verifiable
`EMLNoCrossingAt` on the connecting interval and an ACTUAL point where `B` is strictly positive
(not merely approaching positivity in a limit, and not merely "not provably non-positive"). A `B`
whose sign behavior can't be pinned down this concretely is covered by none of the three
mechanisms — same wall as cont. 43, viewed from a slightly wider angle each round without actually
moving.

`sorryAx`-free, verified via a genuinely fresh rebuild. No `eml_pfaffian_validon_from_sin_equality`
dependence. Full `lake build MachLib` passes (444 modules — extended the existing file, no new
module). One commit this round (`2fbbc757`, plus this docs commit), pushed.

## 2026-07-21 (cont. 51) — the mirror sign order added: crossing disjunct now allows either
direction

**Direct user request**: "proceed" — continuing the same broadening pattern one more step.
Everything in the crossing disjunct through cont. 50 required `B` non-positive at the EARLIER
point and positive at the LATER one. `B` positive first, dipping non-positive later, is the mirror
image and was not covered — noticed by re-checking what `WitnessResidualCrossingUnboundedMirror.lean`
(cont. 39) actually built: `eml_A_crossing_B_unbounded_above_mirror`/`_either_direction` already
prove unboundedness for this direction too, sitting unused by this recent lineage until now.

**Same two-step pattern as the primary direction, applied a second time.** An exact-root bridge
(`no_eml_A_B_eq_nested_target_of_crossing_and_no_crossing_mirror`, direct wiring of the mirror
unboundedness theorem into the existing general bridge) then the sign-change broadening via IVT
(`no_eml_A_B_eq_nested_target_of_sign_change_and_no_crossing_mirror`) — this time applying
`intermediate_value` to `-B` (via `HasDerivAt_neg`, an existing axiom not previously exercised in
this lineage), since `intermediate_value` itself only takes a negative-to-positive order and the
mirror direction needs positive-to-negative. `BChainTriple`'s crossing disjunct now allows EITHER
order via a top-level `∨`.

**One small, quickly-caught fix.** An `lt_of_le_of_lt`/`lt_of_lt_of_le` argument-order mixup in the
final case of the mirror sign-change proof — the compiler flagged the exact expected type
immediately, fixed in the next edit. First non-clean-first-try compile in this particular
sub-lineage since cont. 44, worth noting honestly rather than glossing over — four clean-first-try
rounds in a row (cont. 47-50) was a good run, not an unbroken law.

**Scope, unchanged in substance.** The crossing disjunct (either direction now) still needs
verifiable `EMLNoCrossingAt` on the connecting interval and an ACTUAL endpoint value on the correct
side of zero — not a limit, not an assumption. A `B` whose behavior can't be pinned down this
concretely remains outside all mechanisms in this file. This round adds coverage symmetry (both
sign orders now available), not new closeable territory beyond that.

`sorryAx`-free, verified via a genuinely fresh rebuild for all three new theorems. No
`eml_pfaffian_validon_from_sin_equality` dependence. Full `lake build MachLib` passes (444 modules
— extended the existing file). One commit this round (`dad3c7be`, plus this docs commit), pushed.
