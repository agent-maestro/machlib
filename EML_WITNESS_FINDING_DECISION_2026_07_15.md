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
