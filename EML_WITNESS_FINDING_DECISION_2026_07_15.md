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
